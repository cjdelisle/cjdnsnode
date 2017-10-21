/* @flow */
/*
 * You may redistribute this program and/or modify it under the terms of
 * the GNU General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
'use strict';
const Fs = require('fs');
const Net = require('net');
const Udp = require('dgram');
const Crypto = require('crypto');
const nThen = require('nthen');
const Dijkstra = require('node-dijkstra');
const Cjdnsplice = require('cjdnsplice');
const Cjdnskeys = require('cjdnskeys');
const Cjdnsniff = require('cjdnsniff');
const Cjdnsadmin = require('cjdnsadmin');
const Cjdnsann = require('cjdnsann');
const Http = require('http');

const Peer = require('./peer');


const MS_MINUTE = 1000 * 60;
const KEEP_TABLE_CLEAN_CYCLE = 4 * 60 * MS_MINUTE;
const AGREED_TIMEOUT_MS = 10 * MS_MINUTE;
const MAX_CLOCKSKEW_MS = (1000 * 10);
const MAX_GLOBAL_CLOCKSKEW_MS = (1000 * 60 * 60 * 20);
const GLOBAL_TIMEOUT_MS = MAX_GLOBAL_CLOCKSKEW_MS + AGREED_TIMEOUT_MS;

const now = () => (+new Date());

const mkLink = (annPeer, ann) => {
    if (!ann) { throw new Error(); }
    return Object.freeze({
        label: annPeer.label,
        mtu: annPeer.mtu,
        drops: annPeer.drops,
        latency: annPeer.latency,
        penalty: annPeer.penalty,
        encodingFormNum: annPeer.encodingFormNum,
        flags: annPeer.flags,
        time: Number('0x' + ann.timestamp)
    });
};

const linkValue = (link) => {
    return 1;
};

const getRoute = (ctx, src, dst) => {
    if (!src || !dst) { return null; }

    if (src === dst) {
        return { label: '0000.0000.0000.0001', hops: [] };
    }

    if (!ctx.mut.dijkstra) {
        ctx.mut.routeCache = {};
        const dijkstra = ctx.mut.dijkstra = new Dijkstra();
        for (const nip in ctx.nodesByIp) {
            const links = ctx.nodesByIp[nip].inwardLinksByIp;
            const l = {};
            for (const pip in links) { l[pip] = linkValue(links[pip]); }
            ctx.mut.dijkstra.addNode(nip, l);
        }
    }

    const cachedEntry = ctx.mut.routeCache[dst.ipv6 + '|' + src.ipv6];
    if (typeof(cachedEntry) !== 'undefined') {
        return cachedEntry;
    }

    // we ask for the path in reverse because we build the graph in reverse.
    // because nodes announce own their reachability instead of announcing reachability of others.
    const path = ctx.mut.dijkstra.path(dst.ipv6, src.ipv6);
    if (!path) {
        return (ctx.mut.routeCache[dst.ipv6 + '|' + src.ipv6] = null);
    }
    path.reverse();
    let last;
    let lastLink;
    const hops = [];
    const labels = [];
    let formNum;

    path.forEach((nip) => {
        const node = ctx.nodesByIp[nip];
        if (last) {
            const link = node.inwardLinksByIp[last.ipv6];
            let label = link.label;
            const curFormNum = Cjdnsplice.getEncodingForm(label, last.encodingScheme);
            if (curFormNum < formNum) {
                label = Cjdnsplice.reEncode(label, last.encodingScheme, formNum);
            }
            labels.unshift(label);
            hops.push({
                label: label,
                origLabel: link.label,
                scheme: last.encodingScheme,
                inverseFormNum: formNum
            });
            formNum = link.encodingFormNum;
        }
        last = node;
    });
    labels.unshift('0000.0000.0000.0001');
    const spliced = Cjdnsplice.splice.apply(null, labels);
    return (ctx.mut.routeCache[dst.ipv6 + '|' + src.ipv6] = { label: spliced, hops: hops, path:path });
};

const nodeAnnouncementHash = (node) => {
    let carry = new Buffer(64).fill(0);
    if (node) {
        for (let i = node.mut.announcements.length - 1; i >= 0; i--) {
            const hash = Crypto.createHash('sha512').update(carry);
            carry = hash.update(node.mut.announcements[i].binary).digest();
        }
        node.mut.stateHash = carry;
    }
    return carry;
};

const peersFromAnnouncement = (ann) => {
    return (ann.entities.filter((x) => (x.type === 'Peer')) /*:Array<any>*/ );
};

const encodingSchemeFromAnnouncement = (ann) => {
    const scheme /*:any*/ = ann.entities.filter((x) => (x.type === 'EncodingScheme'))[0];
    return scheme ? scheme.scheme : undefined;
};

const versionFromAnnouncement = (ann) => {
    const ver /*:any*/ = ann.entities.filter((x) => (x.type === 'Version'))[0];
    return ver ? ver.version : undefined;
};

const addAnnouncement = (ctx, node, ann) => {
    const time = Number('0x' + ann.timestamp);
    const sinceTime = time - AGREED_TIMEOUT_MS;
    const newAnnounce = [];
    const peersAnnounced = {};
    node.mut.announcements.unshift(ann);
    node.mut.announcements.forEach((a) => {
        if (Number('0x' + a.timestamp) < sinceTime) { return; }
        let safe = false;
        const peers = peersFromAnnouncement(a);
        for (let i = 0; i < peers.length; i++) {
            if (peersAnnounced[peers[i].ipv6]) { continue; }
            safe = true;
            peersAnnounced[peers[i].ipv6] = true;
        }
        if (safe) {
            newAnnounce.push(a);
        } else {
            ctx.peer.deleteAnn(a.hash);
        }
    });
    node.mut.timestamp = ann.timestamp;
    node.mut.announcements = newAnnounce;
};

const mkNode = (ctx, obj) => {
    if (typeof(obj.version) !== 'number') { throw new Error(); }
    if (typeof(obj.key) !== 'string') { throw new Error(); }
    if (typeof(obj.timestamp) !== 'string') { throw new Error(); }
    if (isNaN(Number('0x' + obj.timestamp))) { throw new Error(); }
    let encodingScheme;
    if (typeof(obj.encodingScheme) === 'undefined') {
        const onode = ctx.nodesByIp[obj.ipv6];
        if (onode && typeof(onode.encodingScheme) === 'object') {
            encodingScheme = onode.encodingScheme;
        } else {
            throw new Error("cannot create node we do not know its encoding scheme");
        }
    } else {
        encodingScheme = obj.encodingScheme;
    }
    const out = Object.freeze({
        type: "Node",
        version: obj.version,
        key: obj.key,
        ipv6: obj.ipv6,
        encodingScheme: encodingScheme,
        inwardLinksByIp: { },
        mut: {
            timestamp: obj.timestamp,
            announcements: [ ],
            stateHash: undefined
        }
    });
    if (obj.announcement) {
        out.mut.announcements[0] = obj.announcement;
    }
    return out;
};

const addNode = (ctx, node, overwrite) => {
    if (node.type !== "Node") { throw new Error(); }
    //if (!overwrite && ctx.nodesByKey[node.key]) { throw new Error(); }
    if (!overwrite && ctx.nodesByIp[node.ipv6]) { throw new Error(); }
    //ctx.nodesByKey[node.key] = node;
    ctx.nodesByIp[node.ipv6] = node;
    return node;
};

const handleAnnounce = (ctx, annBin, fromNode) => {
    let ann;
    let replyError = 'none';
    let annHash;
    try {
        annHash = Crypto.createHash('sha512').update(annBin).digest('hex');
    } catch (e) {
        console.log(annBin);
        console.log(e.stack);
        throw e;
    }
    //console.log("ann: " + annBin.toString('hex'));
    console.log("ann:" + annHash);
    try {
        ann = Cjdnsann.parse(annBin);
    } catch (e) {
        console.log("bad announcement [" + e.message + "]");
        replyError = "failed_parse_or_validate";
    }
    //console.log(ann);
    //console.log(+new Date());

    let node;
    if (ann) { node = ctx.nodesByIp[ann.nodeIp]; }

    if (fromNode && ann && node && node.mut.timestamp > ann.timestamp) {
        console.log("old timestamp");
        replyError = "old_message";
        ann = undefined;
    }

    let maxClockSkew;
    if (fromNode) {
        maxClockSkew = MAX_CLOCKSKEW_MS;
        if (!ctx.mut.selfNode) { throw new Error(); }
        if (ann && ann.snodeIp !== ctx.mut.selfNode.ipv6) {
            console.log("announcement from peer which is one of ours");
            replyError = "wrong_snode";
            ann = undefined;
        }
    } else {
        maxClockSkew = MAX_GLOBAL_CLOCKSKEW_MS;
        if (ctx.mut.selfNode && ann && ann.snodeIp === ctx.mut.selfNode.ipv6) {
            console.log("announcement meant for other snode");
            replyError = "wrong_snode";
            ann = undefined;
        }
    }
    if (ann && Math.abs(new Date() - Number('0x' + ann.timestamp)) > maxClockSkew) {
        console.log("unacceptably large clock skew " +
            (new Date() - Number('0x' + ann.timestamp)));
        replyError = "excessive_clock_skew";
        ann = undefined;
    } else if (ann) {
        //console.log("clock skew " + (new Date() - Number('0x' + ann.timestamp)));
    }

    let scheme;
    if (ann && (scheme = encodingSchemeFromAnnouncement(ann))) {
    } else if (node) {
        scheme = node.encodingScheme;
    } else if (ann) {
        console.log("no encoding scheme");
        replyError = "no_encodingScheme";
        ann = undefined;
    }

    let version;
    if (ann && (version = versionFromAnnouncement(ann))) {
    } else if (node) {
        version = node.version;
    } else if (ann) {
        console.log("no version");
        replyError = "no_version";
        ann = undefined;
    }

    if (!ann) {
        return { stateHash: nodeAnnouncementHash(node), error: replyError };
    }

    const nodex = mkNode(ctx, {
        version: version,
        key: ann.nodePubKey,
        encodingScheme: scheme,
        timestamp: ann.timestamp,
        ipv6: ann.nodeIp,
        announcement: ann
    });
    if (node) {
        if (node.mut.timestamp > ann.timestamp) {
            console.log("old announcement, drop");
            return { stateHash: nodeAnnouncementHash(node), error: replyError };
        } else if (node.version !== nodex.version) {
            console.log("version change, replacing node");
            node = addNode(ctx, nodex, true);
        } else if (JSON.stringify(node.encodingScheme) !== JSON.stringify(nodex.encodingScheme)) {
            console.log("encodingScheme change, replacing node");
            node = addNode(ctx, nodex, true);
        } else if (ann.isReset) {
            console.log("reset message");
            node = addNode(ctx, nodex, true);
            console.log(node.mut.announcements.length + ' announcements');
        } else {
            addAnnouncement(ctx, node, ann);
        }
    } else {
        node = addNode(ctx, nodex, false);
    }

    const peersIp6 = [];
    peersFromAnnouncement(ann).forEach((peer) => {
        const ipv6 = peer.ipv6;
        peersIp6.push(ipv6);
        if (!node) { throw new Error(); }
        if (peer.label === '0000.0000.0000.0000' && node.inwardLinksByIp[ipv6]) {
            delete node.inwardLinksByIp[ipv6];
            ctx.mut.dijkstra = undefined;
            return;
        }
        const stored = node.inwardLinksByIp[ipv6];
        const newLink = node.inwardLinksByIp[ipv6] = mkLink(peer, ann);
        if (!stored) {
        } else if (newLink.label !== stored.label) {
        } else if (linkValue(newLink) !== linkValue(stored)) {
        } else {
            return;
        }
        ctx.mut.dijkstra = undefined;
    });

    if (peersIp6.length) {
        ctx.peer.addAnn(annHash, ann.binary);
    }
    return { stateHash: nodeAnnouncementHash(node), error: replyError };
};

const onSubnodeMessage = (ctx, msg, cjdnslink) => {
    if (!msg.contentBenc.sq) { return; }
    if (!msg.routeHeader.version || !msg.routeHeader.publicKey) {
        if (msg.routeHeader.ip) {
            console.log("message from " + msg.routeHeader.ip + " with missing key or version");
        }
        return;
    }
    if (msg.contentBenc.sq.toString('utf8') === 'gr') {
        const srcIp = Cjdnskeys.ip6BytesToString(msg.contentBenc.src);
        const tarIp = Cjdnskeys.ip6BytesToString(msg.contentBenc.tar);
        const src = ctx.nodesByIp[srcIp];
        const tar = ctx.nodesByIp[tarIp];
        const logMsg = "getRoute req " + srcIp + " " + tarIp + "  ";
        const r = getRoute(ctx, src, tar);

        if (r) {
            console.log(logMsg + r.label);
            msg.contentBenc.n = Buffer.concat([
                Cjdnskeys.keyStringToBytes(tar.key),
                new Buffer(r.label.replace(/\./g, ''), 'hex')
            ]);
            msg.contentBenc.np = new Buffer([1, tar.version]);
        } else {
            console.log(logMsg + "not found");
        }
        msg.contentBenc.recvTime = now();
        msg.routeHeader.switchHeader.labelShift = 0;

        delete msg.contentBenc.sq;
        delete msg.contentBenc.src;
        delete msg.contentBenc.tar;
        cjdnslink.send(msg);
    } else if (msg.contentBenc.sq.toString('utf8') === 'ann') {
        const reply = handleAnnounce(ctx, msg.contentBenc.ann, true, false);
        if (!ctx.mut.selfNode) { throw new Error(); }
        msg.contentBenc = {
            txid: msg.contentBenc.txid,
            p: ctx.mut.selfNode.version,
            recvTime: +new Date(),
            stateHash: reply.stateHash,
            error: reply.error
        };
        msg.routeHeader.switchHeader.labelShift = 0;
        console.log("reply: " + reply.stateHash.toString('hex'));
        cjdnslink.send(msg);
    } else if (msg.contentBenc.sq.toString('utf8') === 'pn') {
        msg.contentBenc.recvTime = now();
        msg.contentBenc.stateHash = new Buffer(new Array(64).fill(0));
        // can't possibly be a ctrl message but needed to please flow.
        if (!msg.routeHeader.ip) { throw new Error(); }
        if (msg.routeHeader.ip in ctx.nodesByIp) {
            const n = ctx.nodesByIp[msg.routeHeader.ip];
            if (n.mut.stateHash) {
                msg.contentBenc.stateHash = n.mut.stateHash;
            }
        }
        msg.routeHeader.switchHeader.labelShift = 0;
        delete msg.contentBenc.sq;
        delete msg.contentBenc.src;
        delete msg.contentBenc.tar;
        cjdnslink.send(msg);
    } else {
        console.log(msg.contentBenc);
    }
};

/*::import type { Cjdnsniff_BencMsg_t } from 'cjdnsniff'*/
const service = (ctx) => {
    let cjdns;
    nThen((waitFor) => {
        Cjdnsadmin.connectWithAdminInfo(waitFor((c) => { cjdns = c; }));
    }).nThen((waitFor) => {
        cjdns.Core_nodeInfo(waitFor((err, ret) => {
            if (err) { throw err; }
            const parsedName = Cjdnskeys.parseNodeName(ret.myAddr);
            const ipv6 = Cjdnskeys.publicToIp6(parsedName.key);
            ctx.mut.selfNode = mkNode(ctx, {
                version: parsedName.v,
                key: parsedName.key,
                ipv6: ipv6,
                encodingScheme: ret.encodingScheme,
                inwardLinksByIp: {},
                timestamp: 'ffffffffffffffff'
            });
            console.log("Got selfNode");
        }));
    }).nThen((waitFor) => {
        Cjdnsniff.sniffTraffic(cjdns, 'CJDHT', waitFor((err, cjdnslink) => {
            console.log("Connected to cjdns engine");
            if (err) { throw err; }
            cjdnslink.on('error', (e) => {
                console.error('sniffTraffic error');
                console.error(e.stack);
            });
            cjdnslink.on('message', (msg) => {
                /*::msg = (msg:Cjdnsniff_BencMsg_t);*/
                onSubnodeMessage(ctx, msg, cjdnslink);
            });
        }));
    }).nThen((waitFor) => {
        setInterval(() => {
            cjdns.UpperDistributor_listHandlers(0, (err, ret) => {
                if (err) { throw err; }
                if (ret.error !== 'none') {
                    throw new Error("from cjdns: " + ret.error);
                }
                if (!ret.handlers.length) {
                    throw new Error("became disconnected for cjdns");
                }
            });
        }, 5000);
    });
};

const testSrv = (ctx) => {
    const reqHandler = (req, res) => {
        const ents = req.url.split('/');
        ents.shift();
        if (ents[0] === 'path') {
            ents.shift();
            //res.end(JSON.stringify(ents));
            const srcIp = ents[0];
            const tarIp = ents[1];
            const src = ctx.nodesByIp[srcIp];
            const tar = ctx.nodesByIp[tarIp];
            console.log("http getRoute req " + srcIp + " " + tarIp);
            if (!src) { res.end("src not found"); return; }
            if (!tar) { res.end("tar not found"); return; }
            const r = getRoute(ctx, src, tar);
            res.end(JSON.stringify(r, null, '  '));
        } else if (ents[0] === 'walk') {
            const out = [];
            const outLinks = [];
            for (const ip in ctx.nodesByIp) {
                const node = ctx.nodesByIp[ip];
                out.push([
                    "node",
                    Math.floor(Number('0x' + node.mut.timestamp) / 1000),
                    "-",
                    "v" + node.version + ".0000.0000.0000.0001." + node.key,
                    node.encodingScheme
                ]);
                for (const peerIp in node.inwardLinksByIp) {
                    const link = node.inwardLinksByIp[peerIp];
                    const otherNode = ctx.nodesByIp[peerIp];
                    //if (!otherNode) { continue; }
                    outLinks.push([
                        otherNode ? "link" : "oldlink",
                        Math.floor(link.time / 1000),
                        "-",
                        node.key,
                        otherNode ? otherNode.key : peerIp,
                        link.label,
                        link.drops
                    ]);
                }
            }
            out.push.apply(out, outLinks);
            res.end(out.map((x)=>JSON.stringify(x)).join('\n'));
        } else if (ents[0] === 'dump') {
            res.setHeader('Content-Type', 'application/octet-stream');
            for (const ip in ctx.nodesByIp) {
                const node = ctx.nodesByIp[ip];
                node.announcements.forEach((ann) => {
                    const len = new Buffer(4);
                    len.writeInt32BE(ann.binary.length, 0);
                    res.write(len);
                    res.write(ann.binary);
                });
            }
            const end = new Buffer(4);
            end.writeInt32BE(0, 0);
            res.end(end);
        } else {
            //console.log(req.url);
            res.end(req.url);
        }
    };
    const httpServer = Http.createServer(reqHandler);
    ctx.peer.runServer(httpServer);
    httpServer.listen(3333);
};

const keepTableClean = (ctx) => {
    setInterval(() => {
        console.log("keepTableClean()");
        const minTime = now() - GLOBAL_TIMEOUT_MS;
        for (const nodeIp in ctx.nodesByIp) {
            const node = ctx.nodesByIp[nodeIp];
            const n = now();
            if (minTime > Number(node.timestamp)) {
                console.log("forgetting node [" + nodeIp + "]");
                delete ctx.nodesByIp;
                node.mut.announcements.forEach((ann) => {
                    ctx.peer.deleteAnn(ann.hash);
                });
            }
        }
    }, KEEP_TABLE_CLEAN_CYCLE);
};

const getConfig = () => {
    const confIdx = process.argv.indexOf('--config');
    /*::const ConfigType = require('./config.example.js');*/
    return (require /*:(any)=>typeof(ConfigType)*/)(
        (confIdx > -1) ? process.argv[confIdx+1] : './config'
    );
};

const main = () => {
    const config = getConfig();
    let ctx = Object.freeze({
        //nodesByKey: {},
        //ipnodes: {},
        nodesByIp: {},
        clients: [],
        version: 1,

        config: config,
        peer: Peer.create(),

        mut: {
            dijkstra: undefined,
            selfNode: undefined,
            routeCache: {}
        }
    });

    keepTableClean(ctx);
    if (config.connectCjdns) { service(ctx); }
    testSrv(ctx);
    ctx.peer.onAnnounce((peer, msg) => { handleAnnounce(ctx, msg, false, false); });
    (ctx.config.peers || []).forEach(ctx.peer.connectTo);
};
main();

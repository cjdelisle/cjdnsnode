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
const KEEP_TABLE_CLEAN_CYCLE = 1000 * 30;
const AGREED_TIMEOUT_MS = 10 * MS_MINUTE;
const MAX_CLOCKSKEW_MS = (1000 * 10);
const MAX_GLOBAL_CLOCKSKEW_MS = (1000 * 60 * 60 * 20);
const GLOBAL_TIMEOUT_MS = MAX_GLOBAL_CLOCKSKEW_MS + AGREED_TIMEOUT_MS;

const now = () => (+new Date());

// Workaround for bug fixed in:
// https://github.com/cjdelisle/cjdns/commit/b97787073b88e3123873ed8773d07716a78bab6d
const bswap16 = (b) => {
    return ((b & 0xff) << 8) | ((b & 0xffff) >>> 8);
};

const linkStateUpdate = (link, ann, dst, src) => {
    ann.entities.forEach((e) => {
        if (e.type !== 'LinkState') { return; }
        //console.log("LinkState " + e.nodeId + '  ' + link.peerNum);
        if (e.nodeId !== link.peerNum && e.nodeId !== bswap16(link.peerNum)) { return; }
        // The most recent 10 second timeslot should be Math.floor(time_of_signing / 1000 / 10)
        const time = Number('0x' + ann.timestamp);
        const ts = Math.floor(time / 1000 / 10);
        // Timeslots older than AGREED_TIMEOUT_MS will be dropped
        const earliestOkTs = ts - Math.floor(AGREED_TIMEOUT_MS / 100 / 10);
        Object.keys(link.linkState).forEach((ls) => {
            if (Number(ls) < earliestOkTs) { delete link.linkState[ls]; }
        });
        for (let i = e.startingPoint - 1; i !== e.startingPoint; i--) {
            if (i < 0) { i = Cjdnsann.LinkState.SLOTS; }
            if (link.linkState[ts]) { continue; } // TODO: check if the numbers are the same?
            let x = {
                drops: e.dropSlots[i],
                lag: e.lagSlots[i],
                kbRecv: e.kbRecvSlots[i]
            };
            if (typeof(x.drops) === 'undefined' &&
                typeof(x.lag) === 'undefined' &&
                typeof(x.kbRecv) === 'undefined')
            {
                continue;
            }
            link.linkState[ts] = x;
            console.log(JSON.stringify(["LINK_STATE_UPDATE", ts, dst, src, link.label, x]));
        }
    });
};

const mkLink = (annPeer, ann) => {
    if (!ann) { throw new Error(); }
    return Object.freeze({
        label: annPeer.label,
        mtu: annPeer.mtu,
        encodingFormNum: annPeer.encodingFormNum,
        flags: annPeer.flags,
        time: Number('0x' + ann.timestamp),
        peerNum: annPeer.peerNum,
        linkState: {}
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

    if (ctx.mut.lastRebuild + 3000 < +new Date()) {
        ctx.mut.routeCache = {};
        ctx.mut.dijkstra = new Dijkstra();
        for (const nip in ctx.nodesByIp) {
            const links = ctx.nodesByIp[nip].inwardLinksByIp;
            const l = {};
            for (const pip in links) {
              const reverse = ctx.nodesByIp[pip];
              if (!reverse || !reverse.inwardLinksByIp[nip]) { continue; }
              l[pip] = linkValue(links[pip]);
            }
            console.log(nip, l);
            ctx.mut.dijkstra.addNode(nip, l);
        }
        ctx.mut.lastRebuild = +new Date();
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
        // current announcement is always safe because it might not have actually announced anything
        // in which case it's an empty announce just to let the snode know the node is still here...
        if (safe || a === ann) {
            newAnnounce.push(a);
        }
    });
    node.mut.announcements.forEach((a) => {
        if (newAnnounce.indexOf(a) === -1 && a !== node.mut.resetMsg) {
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
            stateHash: undefined,

            // Dirty trick to preserve the last reset message in order to
            // allow downstream snode peers to be able to get the version and the
            // encoding scheme of the node without telling the node that in fact we
            // have to preserve this stuff, because it thinks we're going to delete them
            // and if we don't tell it the right hash, it will go into desync mode.
            resetMsg: undefined,
        }
    });
    if (obj.announcement) {
        out.mut.resetMsg = out.mut.announcements[0] = obj.announcement;
    }
    return out;
};

const addNode = (ctx, node, overwrite) => {
    if (node.type !== "Node") { throw new Error(); }
    let oldNode = ctx.nodesByIp[node.ipv6];
    if (!overwrite && oldNode) { throw new Error(); }
    if (oldNode) {
        oldNode.mut.announcements.forEach((ann) => { ctx.peer.deleteAnn(ann.hash); });
        if (oldNode.mut.resetMsg) { ctx.peer.deleteAnn(oldNode.mut.resetMsg.hash); }
    }
    ctx.nodesByIp[node.ipv6] = node;
    return node;
};

const handleAnnounce = (ctx, annBin, fromNode) => {
    let ann;
    let replyError = 'none';
    try {
        ann = Cjdnsann.parse(annBin);
    } catch (e) {
        console.log("bad announcement [" + e.message + "]");
        replyError = "failed_parse_or_validate";
    }
    //console.log(ann);
    //console.log(+new Date());

    let node;
    if (ann) {
        node = ctx.nodesByIp[ann.nodeIp];
        if (0) {
            console.log("ANN from [" + ann.nodeIp + "] " +
                "ts [" + ann.timestamp + "] " +
                "isReset [" + String(ann.isReset) + "] " +
                "peers [" + ann.entities.filter((a) => (a.type === 'Peer')).length + "] " +
                "ls [" + ann.entities.filter((a) => (a.type === 'LinkState')).length + "] " +
                "known [" + (!!node) + "]" + ((!node && !ann.isReset) ? " ERR_UNKNOWN" : ""));
        }
    }

    if (fromNode && ann && node &&
        Number("0x" + node.mut.timestamp) > Number("0x" + ann.timestamp)) {
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
        //console.log("no encoding scheme");
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

    if (node && Number("0x" + node.mut.timestamp) > Number("0x" + ann.timestamp)) {
        console.log("old announcement [" + ann.timestamp +
                "] most recent [" + node.mut.timestamp + "]");
        return { stateHash: nodeAnnouncementHash(node), error: replyError };
    }

    if (ann.isReset) {
        node = addNode(ctx, mkNode(ctx, {
            version: version,
            key: ann.nodePubKey,
            encodingScheme: scheme,
            timestamp: ann.timestamp,
            ipv6: ann.nodeIp,
            announcement: ann
        }), true);
    } else if (node) {
        addAnnouncement(ctx, node, ann);
    } else {
        console.log("no node and no reset message");
        return { stateHash: nodeAnnouncementHash(undefined), error: "unknown_node" };
    }

    const peersIp6 = [];
    peersFromAnnouncement(ann).forEach((peer) => {
        const ipv6 = peer.ipv6;
        peersIp6.push(ipv6);
        if (!node) { throw new Error(); }
        if (peer.label === '0000.0000.0000.0000' && node.inwardLinksByIp[ipv6]) {
            delete node.inwardLinksByIp[ipv6];
            return;
        }
        const stored = node.inwardLinksByIp[ipv6];
        const newLink = mkLink(peer, ann);
        if (!stored) {
        } else if (newLink.label !== stored.label) {
        } else if (linkValue(newLink) !== linkValue(stored)) {
        } else {
            linkStateUpdate(stored, ann, node.ipv6, ipv6);
            return;
        }
        linkStateUpdate(newLink, ann, node.ipv6, ipv6);
        node.inwardLinksByIp[ipv6] = newLink;
    });

    if (node.mut.announcements.indexOf(ann) > -1 || node.mut.resetAnn === ann) {
        ctx.peer.addAnn(ann.hash, ann.binary);
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
        //const logMsg = "getRoute req " + srcIp + " " + tarIp + "  ";
        const r = getRoute(ctx, src, tar);

        if (r) {
            //console.log(logMsg + r.label);
            msg.contentBenc.n = Buffer.concat([
                Cjdnskeys.keyStringToBytes(tar.key),
                new Buffer(r.label.replace(/\./g, ''), 'hex')
            ]);
            msg.contentBenc.np = new Buffer([1, tar.version]);
        } else {
            //console.log(logMsg + "not found");
        }
        msg.contentBenc.recvTime = now();
        msg.routeHeader.switchHeader.labelShift = 0;

        delete msg.contentBenc.sq;
        delete msg.contentBenc.src;
        delete msg.contentBenc.tar;
        cjdnslink.send(msg);
    } else if (msg.contentBenc.sq.toString('utf8') === 'ann') {
        const reply = handleAnnounce(ctx, msg.contentBenc.ann, true);
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
        } else if (ents[0] === 'ni') {
            if (!ents[1]) {
                let totalAnn = 0;
                let resets = 0;
                res.end(JSON.stringify({
                    nodes: Object.keys(ctx.nodesByIp).map((ip6) => {
                        const n = ctx.nodesByIp[ip6];
                        const announcements = n.mut.announcements.length;
                        totalAnn += announcements;
                        const rst = (n.mut.resetAnn && n.mut.announcements.indexOf(n.mut.resetAnn) === -1);
                        if (rst) { resets++; }
                        return {
                            ip6: ip6,
                            announcements: announcements,
                            rst: rst
                        };
                    }),
                    totalAnnouncements: totalAnn,
                    totalWithRsts: resets + totalAnn,
                    peerInfo: ctx.peer.info(),
                    totalNodes: Object.keys(ctx.nodesByIp).length
                }, null, '  '));
            } else {
                res.end(JSON.stringify({ node: ctx.nodesByIp[ents[1]] }, null, '  '));
            }
        } else if (ents[0] === 'ls') {

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
                    node.encodingScheme,
                    node.ipv6
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
                        link.label
                    ]);
                }
            }
            out.push.apply(out, outLinks);
            res.end(out.map((x)=>JSON.stringify(x)).join('\n'));
        } else if (ents[0] === 'dump') {
            res.setHeader('Content-Type', 'application/octet-stream');
            Object.keys(ctx.nodesByIp).forEach((ip) => {
                const node = ctx.nodesByIp[ip];
                node.mut.announcements.forEach((ann) => {
                    const len = new Buffer(4);
                    len.writeInt32BE(ann.binary.length, 0);
                    res.write(len);
                    res.write(ann.binary);
                });
            });
            const end = new Buffer(4);
            end.writeInt32BE(0, 0);
            res.end(end);
        } else if (ents[0] === '') {
            res.end(JSON.stringify({
                peer: ctx.peer.info(),
                nodesByIp: Object.keys(ctx.nodesByIp).length
            }, null, '  '));
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
        Object.keys(ctx.nodesByIp).forEach((nodeIp) => {
            const node = ctx.nodesByIp[nodeIp];
            if (minTime > Number('0x' + node.mut.timestamp)) {
                console.log("forgetting node [" + nodeIp + "]");
                delete ctx.nodesByIp[nodeIp];
                node.mut.announcements.forEach((ann) => { ctx.peer.deleteAnn(ann.hash); });
                if (node.mut.resetAnn) { ctx.peer.deleteAnn(node.mut.resetAnn.hash); }
            }
        });
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
        version: 1,

        config: config,
        peer: Peer.create(),

        mut: {
            lastRebuild: +new Date(),
            dijkstra: undefined,
            selfNode: undefined,
            routeCache: {}
        }
    });

    keepTableClean(ctx);
    if (config.connectCjdns) { service(ctx); }
    testSrv(ctx);
    ctx.peer.onAnnounce((peer, msg) => { handleAnnounce(ctx, msg, false); });
    (ctx.config.peers || []).forEach(ctx.peer.connectTo);
};
main();

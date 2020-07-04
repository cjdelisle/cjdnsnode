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
const AGREED_TIMEOUT_MS = 20 * MS_MINUTE;
const MAX_CLOCKSKEW_MS = (1000 * 10);
const MAX_GLOBAL_CLOCKSKEW_MS = (1000 * 60 * 60 * 20);
const GLOBAL_TIMEOUT_MS = MAX_GLOBAL_CLOCKSKEW_MS + AGREED_TIMEOUT_MS;


/*::
import type { Cjdnsniff_GenericMsg_t } from 'cjdnsniff'
type QueryBenc_t = {
    // Query and response
    p: number,  // "protocol version"
    txid: Buffer, // transaction id

    // Query only
    sq?: Buffer, // "snode query"
    src?: Buffer,  // for a "gr" (get-route) query, source
    tar?: Buffer,  // for a "gr" (get-route) query, destination
    ann?: Buffer,  // for an "ann" (announce) query, the announcement

    // Response only
    recvTime?: number, // reply
    stateHash?: Buffer, // reply
    error?: string,
    n?: Buffer,
    np?: Buffer,
};
export type Query_t = Cjdnsniff_GenericMsg_t & {
    contentBenc: QueryBenc_t;
};




type LinkStateEntry_t = {
    drops: number,
    lag: number,
    kbRecv: number,
};
type LinkState_t = {[number]: LinkStateEntry_t};
type Link_t = {
    label: string,
    encodingFormNum: number,
    peerNum: number,
    linkState: LinkState_t,
    mut: {
        mtu: number,
        flags: number,
        time: number,
        cost: number,
    }
};
type Cjdnsencode_Form_t = {
    prefixLen: number,
    prefix: string,
    bitCount: number
};
type Cjdnsencode_Scheme_t = Cjdnsencode_Form_t[];
type Announce_Entity_EncodingScheme_t = {
    type: 'EncodingScheme',
    hex: string,
    scheme: Cjdnsencode_Scheme_t
};
type Announce_Entity_LinkState_t = {
    type: 'LinkState',
    nodeId: number,
    startingPoint: number,
    lagSlots: Array<number|null>,
    dropSlots: Array<number|null>,
    kbRecvSlots: Array<number|null>,
};
type Announce_Entity_Version_t = {
    type: 'Version',
    version: number,
};
type Announce_Entity_Peer_t = {
    type: 'Peer',
    ipv6: string,
    label: string, // '0000.0000...'
    mtu: number,
    peerNum: number,
    unused: number,
    encodingFormNum: number,
    flags: number,
};
type Announce_Entity_t = (
    Announce_Entity_EncodingScheme_t |
    Announce_Entity_LinkState_t |
    Announce_Entity_Version_t |
    Announce_Entity_Peer_t
);
type Announce_t = {
    signature: string, // hex
    pubSigningKey: string, // hex
    snodeIp: string, // cjdns fc00::/8 ipv6
    nodePubKey: string, // xxxxx.k
    nodeIp: string, // cjdns fc00::/8 ipv6
    ver: number,
    isReset: bool,
    timestamp: string, // hex uint64
    entities: Array<Announce_Entity_t>,
    binary: Buffer,
    hash: string, // hex
};
type Node_t = {
    type: "Node",
    version: number,
    key: string,
    ipv6: string,
    encodingScheme: Cjdnsencode_Scheme_t,
    inwardLinksByIp: {[string]:Array<Link_t>},
    mut: {
        timestamp: string, //hex
        announcements: Array<Announce_t>,
        stateHash: ?Buffer,

        // Dirty trick to preserve the last reset message in order to
        // allow downstream snode peers to be able to get the version and the
        // encoding scheme of the node without telling the node that in fact we
        // have to preserve this stuff, because it thinks we're going to delete them
        // and if we don't tell it the right hash, it will go into desync mode.
        resetMsg: ?Announce_t,
    }
};

type Response_Hop_t = {
    label: string,
    origLabel: string,
    scheme: Cjdnsencode_Scheme_t,
    inverseFormNum: number
};
type Response_t = {
    label: string, // 0000.0000....
    hops: Response_Hop_t[],
    path: Array<string>,  // list of ipv6
};
const ConfigType = require('./config.example.js');
type Config_t = typeof(ConfigType);
type Context_t = {
    //nodesByKey: {},
    //ipnodes: {},
    nodesByIp: {[string]:Node_t},
    version: 1,

    config: Config_t,
    peer: any, // too much work to flow this

    mut: {
        debugNode: string,
        lastRebuild: number, // date as number
        dijkstra: any,
        selfNode: ?Node_t,
        routeCache: {[string]:?Response_t},
        currentNode: string,
    }
}
*/


const now = () => (+new Date());

const warn = (ctx /*:Context_t*/, ...msg) => {
    console.log('WARN', ctx.mut.currentNode, ...msg);
};
const debug = (ctx /*:Context_t*/, ...msg) => {
    if (ctx.mut.currentNode !== ctx.mut.debugNode) { return; }
    console.log('DEBUG', ...msg);
};

const linkStateUpdate1 = (ctx /*:Context_t*/, ann /*:Announce_t*/, node /*:Node_t*/) => {
    const time = Number('0x' + ann.timestamp);
    const ts = Math.floor(time / 1000 / 10);
    // Timeslots older than AGREED_TIMEOUT_MS will be dropped
    const earliestOkTs = ts - Math.floor(AGREED_TIMEOUT_MS / 1000 / 10);

    const inwardLinksByNum /*:{[number]:Link_t}*/ = {};
    const ipsByNum /*:{[number]:string}*/ = {};
    for (const peerIp in node.inwardLinksByIp) {
        for (const p of node.inwardLinksByIp[peerIp]) {
            inwardLinksByNum[p.peerNum] = p;
            ipsByNum[p.peerNum] = peerIp;
        }
    }    
    for (const e of ann.entities) {
        if (e.type !== 'LinkState') { continue; }
        const ls = (e /*:Announce_Entity_LinkState_t*/);
        const link = inwardLinksByNum[ls.nodeId];
        if (!link) { continue; }
        for (const oldLs in link.linkState) {
            if (Number(oldLs) < earliestOkTs) {
                //warn(ctx, 'dropping link state slot ' + oldLs + ' from ' + ann.nodeIp + ' for age');
                delete link.linkState[Number(oldLs)];
            }
        }
        // The startingPoint is the index of the *oldest* entry, newer entries continue forward from
        // this entry. To save space, cjdns doesn't send any more entries than it needs to, which
        // means while deserializing, the nonexistant entries will be filled by nulls.
        //
        // We will assign the newest entry the timeslot corresponding to the time of the announcement
        // itself, but we don't know the timestamp of the starting point. To solve this, we
        // walk backward from the starting point, looping at the end. But since the array is filled
        // with empty space (nulls), we need to be careful not to start deincrementing the timeslot
        // until we hit actual numbers.
        const sp = e.startingPoint % Cjdnsann.LinkState.SLOTS;
        let time = ts;
        for (let i = sp - 1; i !== sp; i--) {
            if (i < 0) { i = Cjdnsann.LinkState.SLOTS; continue; }
            // If there's already a time entry for this slot, we don't care because new data wins.
            //if (link.linkState[ts]) { continue; } // TODO: check if the numbers are the same?
            if (typeof(e.dropSlots[i]) !== 'number') {
            } else if (typeof(e.lagSlots[i]) !== 'number') {
            } else if (typeof(e.kbRecvSlots[i]) !== 'number') {
            } else {
                const x = link.linkState[time] = {
                    drops: e.dropSlots[i],
                    lag: e.lagSlots[i],
                    kbRecv: e.kbRecvSlots[i]
                };
                debug(ctx, JSON.stringify(
                    ["LINK_STATE_UPDATE", time, ann.nodeIp, ipsByNum[ls.nodeId], link.label, x]));
                time--;
            }
        }
    }
};

const mkLink = (annPeer, ann /*:Announce_t*/) /*:Link_t*/ => {
    if (!ann) { throw new Error(); }
    return Object.freeze({
        label: annPeer.label,
        encodingFormNum: annPeer.encodingFormNum,
        peerNum: annPeer.peerNum,
        linkState: {},
        mut: {
            time: Number('0x' + ann.timestamp),
            mtu: annPeer.mtu,
            cost: -1,
            flags: annPeer.flags,
        }
    });
};

const linkCost = (link /*:Link_t*/) => {
    return 1;
};

const getRoute = (ctx /*:Context_t*/, src /*:?Node_t*/, dst /*:?Node_t*/) => {
    if (!src || !dst) { return null; }

    if (src === dst) {
        return { label: '0000.0000.0000.0001', hops: [] };
    }

    if (ctx.mut.lastRebuild + 3000 < +new Date() || !ctx.mut.dijkstra) {
        ctx.mut.routeCache = {};
        const d = ctx.mut.dijkstra = new Dijkstra();
        for (const nip in ctx.nodesByIp) {
            const links = ctx.nodesByIp[nip].inwardLinksByIp;
            const l = {};
            for (const pip in links) {
                const reverse = ctx.nodesByIp[pip];
                if (!reverse || !reverse.inwardLinksByIp[nip]) { continue; }
                const peerLinks = links[pip];
                for (const peerLink of peerLinks) {
                    peerLink.mut.cost = linkCost(peerLink);
                }
                peerLinks.sort((a,b) => a.mut.cost - b.mut.cost);
                // Shouldn't happen but lets be safe
                if (!peerLinks.length) { continue; }
                l[pip] = peerLinks[0].mut.cost;
            }
            debug(ctx, 'building dijkstra tree', nip, l);
            d.addNode(nip, l);
        }
        ctx.mut.lastRebuild = +new Date();
    }

    const cachedEntry = ctx.mut.routeCache[dst.ipv6 + '|' + src.ipv6];
    if (typeof(cachedEntry) !== 'undefined') {
        return cachedEntry;
    }

    // we ask for the path in reverse because we build the graph in reverse.
    // because nodes announce own their reachability instead of announcing reachability of others.
    const path = ( ctx.mut.dijkstra.path(dst.ipv6, src.ipv6) /*:?Array<string>*/ );
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
            const link = node.inwardLinksByIp[last.ipv6][0];
            let label = link.label;
            const curFormNum = Cjdnsplice.getEncodingForm(label, last.encodingScheme);
            if (curFormNum < formNum) {
                label = Cjdnsplice.reEncode(label, last.encodingScheme, formNum);
            }
            labels.unshift(label);
            hops.push(({
                label: label,
                origLabel: link.label,
                scheme: last.encodingScheme,
                inverseFormNum: formNum
            } /*:Response_Hop_t*/));
            formNum = link.encodingFormNum;
        }
        last = node;
    });
    labels.unshift('0000.0000.0000.0001');
    const spliced = Cjdnsplice.splice.apply(null, labels);
    return (ctx.mut.routeCache[dst.ipv6 + '|' + src.ipv6] = { label: spliced, hops: hops, path:path });
};

const nodeAnnouncementHash = (ctx /*:Context_t*/, node /*:?Node_t*/) => {
    let carry = Buffer.alloc(64).fill(0);
    let state = 0;
    if (node) {
        state = node.mut.announcements.length;
        for (let i = node.mut.announcements.length - 1; i >= 0; i--) {
            const hash = Crypto.createHash('sha512').update(carry);
            carry = hash.update(node.mut.announcements[i].binary).digest();
        }
        node.mut.stateHash = carry;
    }
    debug(ctx, "nodeAnnouncementHash", carry.toString('hex'), state);
    return carry;
};

const peersFromAnnouncement = (ann /*:Announce_t*/) /*:Array<Announce_Entity_Peer_t>*/ => {
    return (
        (
            ann.entities.filter((x) => (x.type === 'Peer')) /*:Array<any>*/
        ) /*:Array<Announce_Entity_Peer_t>*/
    );
};

const encodingSchemeFromAnnouncement = (ann /*:Announce_t*/) /*:?Cjdnsencode_Scheme_t*/ => {
    for (const e of ann.entities) {
        if (e.type === 'EncodingScheme') {
            return (e /*:Announce_Entity_EncodingScheme_t*/).scheme;
        }
    }
};

const versionFromAnnouncement = (ann /*:Announce_t*/) /*:?number*/ => {
    for (const e of ann.entities) {
        if (e.type === 'Version') {
            return (e /*:Announce_Entity_Version_t*/).version;
        }
    }
};

const isEntityEphimeral = (e /*Announce_Entity_t*/) => {
    switch (e.type) {
        case 'Version':
        case 'EncodingScheme':
        case 'Peer': return false;
        default: return true;
    }
};

const isEntityReplacement = (oldE /*:Announce_Entity_t*/, newE /*:Announce_Entity_t*/) => {
    if (oldE.type !== newE.type) { return false; }
    if (oldE.type === 'EncodingScheme' || oldE.type === 'Version') {
        return true;
    }
    if (oldE.type === 'Peer' && newE.type === 'Peer') {
        return oldE.peerNum === newE.peerNum;
    }
    return false;
};

const printEntity = (e /*:Announce_Entity_t*/) => {
    if (e.type === 'Peer') {
        return e.ipv6 + '/' + e.peerNum.toString(16)
    } else if (e.type === 'LinkState') {
        return 'LinkState/' + e.nodeId;
    }
    return e.type;
};

const annId = (ann /*:Announce_t*/) => {
    return ann.hash.slice(0,8);
};

const addAnnouncement = (ctx /*:Context_t*/, node /*:Node_t*/, ann /*:Announce_t*/) => {
    const time = Number('0x' + ann.timestamp);
    const sinceTime = time - AGREED_TIMEOUT_MS;
    const newAnnounce = [];
    const entitiesAnnounced = [];
    node.mut.announcements.unshift(ann);
    node.mut.announcements.forEach((a, i) => {
        if (Number('0x' + a.timestamp) < sinceTime) {
            debug(ctx, `Expiring ann [${annId(a)}] because if it is too old`);
            return;
        }
        let safe = false;
        const justifications = [];
        for (const e of a.entities) {
            if (isEntityEphimeral(e)) { continue; }
            if (entitiesAnnounced.filter((je) => isEntityReplacement(e, je)).length === 0) {
                safe = true;
                justifications.push(printEntity(e));
                entitiesAnnounced.push(e);
            }
        }
        // current announcement is always safe because it might not have actually announced anything
        // in which case it's an empty announce just to let the snode know the node is still here...
        if (safe || a === ann) {
            if (a === ann) {
                debug(ctx, `Keeping ann [${annId(a)}] it was announced just now`);
            } else {
                debug(ctx, `Keeping ann [${annId(a)}] for entities [${justifications.join()}]`);
            }
            newAnnounce.push(a);
        } else {
            debug(ctx, `Dropping ann [${annId(a)}] because all entities [${
                justifications.join()}] have been re-announced`);
        }
    });
    debug(ctx, `Finally there are ${newAnnounce.length} anns in the state`);
    node.mut.announcements.forEach((a) => {
        if (newAnnounce.indexOf(a) === -1 && a !== node.mut.resetMsg) {
            ctx.peer.deleteAnn(a.hash);
        }
    });
    node.mut.timestamp = ann.timestamp;
    node.mut.announcements = newAnnounce;
};

const mkNode = (ctx /*:Context_t*/, obj) /*:Node_t*/ => {
    if (typeof(obj.version) !== 'number') { throw new Error(); }
    const version = obj.version;
    if (typeof(obj.key) !== 'string') { throw new Error(); }
    if (typeof(obj.timestamp) !== 'string') { throw new Error(); }
    if (isNaN(Number('0x' + obj.timestamp))) { throw new Error(); }
    const encodingScheme /*:Cjdnsencode_Scheme_t*/ = (() => {
        if (!obj.encodingScheme) {
            const onode = ctx.nodesByIp[obj.ipv6];
            if (onode && typeof(onode.encodingScheme) === 'object') {
                return onode.encodingScheme;
            } else {
                throw new Error("cannot create node we do not know its encoding scheme");
            }
        } else {
            return obj.encodingScheme;
        }
    })();
    const out = Object.freeze({
        type: "Node",
        version,
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

const addNode = (ctx /*:Context_t*/, node /*:Node_t*/, overwrite /*:bool*/) /*:Node_t*/ => {
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

const handleAnnounce = (ctx /*:Context_t*/, annBin /*:Buffer*/, fromNode /*:bool*/) => {
    let annOrNull /*:Announce_t|void*/;
    let replyError = 'none';
    try {
        annOrNull = ((Cjdnsann.parse(annBin) /*:any*/) /*:Announce_t*/);
    } catch (e) {
        warn(ctx, "bad announcement [" + e.message + "]");
        replyError = "failed_parse_or_validate";
    }
    //warn(ctx, ann);
    //warn(ctx, +new Date());

    let node;
    if (annOrNull) {
        const ann = annOrNull;
        ctx.mut.currentNode = annOrNull.nodeIp;
        node = ctx.nodesByIp[annOrNull.nodeIp];
        debug(ctx, "ANN from [" + ann.nodeIp + "] " +
            "ts [" + ann.timestamp + "] " +
            "isReset [" + String(ann.isReset) + "] " +
            "peers [" + ann.entities.filter((a) => (a.type === 'Peer')).length + "] " +
            "ls [" + ann.entities.filter((a) => (a.type === 'LinkState')).length + "] " +
            "known [" + String(!!node) + "]" + ((!node && !ann.isReset) ? " ERR_UNKNOWN" : ""));
    }

    if (fromNode && annOrNull && node &&
        Number("0x" + node.mut.timestamp) > Number("0x" + annOrNull.timestamp)) {
        warn(ctx, "old timestamp");
        replyError = "old_message";
        annOrNull = undefined;
    }

    let maxClockSkew;
    if (fromNode) {
        maxClockSkew = MAX_CLOCKSKEW_MS;
        if (!ctx.mut.selfNode) { throw new Error(); }
        if (annOrNull && annOrNull.snodeIp !== ctx.mut.selfNode.ipv6) {
            warn(ctx, "announcement from peer which is one of ours");
            replyError = "wrong_snode";
            annOrNull = undefined;
        }
    } else {
        maxClockSkew = MAX_GLOBAL_CLOCKSKEW_MS;
        if (ctx.mut.selfNode && annOrNull && annOrNull.snodeIp === ctx.mut.selfNode.ipv6) {
            warn(ctx, "announcement meant for other snode");
            replyError = "wrong_snode";
            annOrNull = undefined;
        }
    }
    if (annOrNull && Math.abs(new Date() - Number('0x' + annOrNull.timestamp)) > maxClockSkew) {
        warn(ctx, "unacceptably large clock skew " +
            (new Date() - Number('0x' + annOrNull.timestamp)));
        replyError = "excessive_clock_skew";
        annOrNull = undefined;
    } else if (annOrNull) {
        //debug(ctx, "clock skew " + (new Date() - Number('0x' + ann.timestamp)));
    }

    let scheme;
    if (annOrNull && (scheme = encodingSchemeFromAnnouncement(annOrNull))) {
    } else if (node) {
        scheme = node.encodingScheme;
    } else if (annOrNull) {
        warn(ctx, "no encoding scheme");
        replyError = "no_encodingScheme";
        annOrNull = undefined;
    }

    let version;
    if (annOrNull && (version = versionFromAnnouncement(annOrNull))) {
    } else if (node) {
        version = node.version;
    } else if (annOrNull) {
        warn(ctx, "no version");
        replyError = "no_version";
        annOrNull = undefined;
    }

    if (!annOrNull) {
        return { stateHash: nodeAnnouncementHash(ctx, node), error: replyError };
    }
    const ann = annOrNull;

    if (node && Number("0x" + node.mut.timestamp) > Number("0x" + ann.timestamp)) {
        warn(ctx, "old announcement [" + ann.timestamp +
                "] most recent [" + node.mut.timestamp + "]");
        return { stateHash: nodeAnnouncementHash(ctx, node), error: replyError };
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
        warn(ctx, "no node and no reset message");
        return { stateHash: nodeAnnouncementHash(ctx, undefined), error: "unknown_node" };
    }

    const peersIp6 = [];
    peersFromAnnouncement(ann).forEach((peer) => {
        const ipv6 = peer.ipv6;
        peersIp6.push(ipv6);
        if (!node) { throw new Error(); }
        if (peer.label === '0000.0000.0000.0000') {
            const links0 = node.inwardLinksByIp[ipv6];
            if (!links0) {
                // Withdrawal of a route we never heard of
                return;
            }
            const links = links0.filter((l) => (l.peerNum !== peer.peerNum));
            if (!links.length) {
                delete node.inwardLinksByIp[ipv6];
            } else if (links.length !== links0.length) {
                node.inwardLinksByIp[ipv6] = links;
            }
            return;
        }
        const stored = node.inwardLinksByIp[ipv6];
        const newLink = mkLink(peer, ann);
        if (!stored) {
            node.inwardLinksByIp[ipv6] = [ newLink ];
            return;
        }
        for (let i = 0; i < stored.length; i++) {
            const storedLink = stored[i];
            if (storedLink.peerNum !== newLink.peerNum) { continue; }
            if (storedLink.label !== newLink.label) {
            } else if (storedLink.encodingFormNum !== newLink.encodingFormNum) {
            } else {
                // only small changes (if any)
                storedLink.mut.flags = newLink.mut.flags;
                storedLink.mut.mtu = newLink.mut.mtu;
                storedLink.mut.time = newLink.mut.time;
                return;
            }
            // major changes, replace the link and wipe out link state
            stored[i] = newLink;
            return;
        }
        // We get here when there is no match
        node.inwardLinksByIp[ipv6].push(newLink);
    });

    linkStateUpdate1(ctx, ann, node);

    if (node.mut.announcements.indexOf(ann) > -1 || node.mut.resetMsg === ann) {
        ctx.peer.addAnn(ann.hash, ann.binary);
    }
    return { stateHash: nodeAnnouncementHash(ctx, node), error: replyError };
};

const onSubnodeMessage = (ctx /*:Context_t*/, msg /*:Query_t*/, cjdnslink /*:{send:(Query_t)=>void}*/) => {
    if (!msg.contentBenc) { return; }
    if (!msg.contentBenc.sq) { return; }
    const sq = msg.contentBenc.sq.toString('utf8');
    if (msg.routeHeader.version) {
    } else if (!msg.contentBenc) {
    } else if (!msg.contentBenc.p) {
    } else {
        msg.routeHeader.version = msg.contentBenc.p;
    }
    if (!msg.routeHeader.version || !msg.routeHeader.publicKey || !msg.routeHeader.ip) {
        if (msg.routeHeader.ip) {
            warn(ctx, "message from " + msg.routeHeader.ip + " with missing key or version " +
                JSON.stringify(msg, null, '  '));
        }
        return;
    }
    ctx.mut.currentNode = msg.routeHeader.ip;
    if (sq === 'gr') {
        if (!msg.contentBenc.src) { return void warn(ctx, "missing src"); }
        const srcIp = Cjdnskeys.ip6BytesToString(msg.contentBenc.src);
        if (!msg.contentBenc.tar) { return void warn(ctx, "missing tar"); }
        const tarIp = Cjdnskeys.ip6BytesToString(msg.contentBenc.tar);
        const src = ctx.nodesByIp[srcIp];
        const tar = ctx.nodesByIp[tarIp];
        //const logMsg = "getRoute req " + srcIp + " " + tarIp + "  ";
        const r = getRoute(ctx, src, tar);

        if (r) {
            //debug(ctx, logMsg + r.label);
            msg.contentBenc.n = Buffer.concat([
                Cjdnskeys.keyStringToBytes(tar.key),
                new Buffer(r.label.replace(/\./g, ''), 'hex')
            ]);
            msg.contentBenc.np = new Buffer([1, tar.version]);
        } else {
            //warn(ctx, logMsg + "not found");
        }
        msg.contentBenc.recvTime = now();
        msg.routeHeader.switchHeader.labelShift = 0;

        delete msg.contentBenc.sq;
        delete msg.contentBenc.src;
        delete msg.contentBenc.tar;
        cjdnslink.send(msg);
    } else if (sq === 'ann' && msg.contentBenc.ann) {
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
        debug(ctx, "reply: " + reply.stateHash.toString('hex'));
        cjdnslink.send(msg);
    } else if (sq === 'pn') {
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
        warn(ctx, 'contentBenc', msg.contentBenc);
    }
    ctx.mut.currentNode = '';
};

const service = (ctx /*:Context_t*/) => {
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
                encodingScheme: (ret.encodingScheme /*:Cjdnsencode_Scheme_t*/),
                inwardLinksByIp: {},
                timestamp: 'ffffffffffffffff'
            });
            warn(ctx, "Got selfNode");
        }));
    }).nThen((waitFor) => {
        Cjdnsniff.sniffTraffic(cjdns, 'CJDHT', waitFor((err, cjdnslink) => {
            warn(ctx, "Connected to cjdns engine");
            if (!cjdnslink) { throw err; }
            cjdnslink.on('error', (e) => {
                console.error('sniffTraffic error');
                console.error(e.stack);
            });
            cjdnslink.on('message', (msg) => {
                msg = (msg /*:Query_t*/);
                onSubnodeMessage(ctx, msg, (cjdnslink /*:any*/));
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

const testSrv = (ctx /*:Context_t*/) => {
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
            warn(ctx, "http getRoute req " + srcIp + " " + tarIp);
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
                        const rst = (n.mut.resetMsg && n.mut.announcements.indexOf(n.mut.resetMsg) === -1);
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
                    const links = node.inwardLinksByIp[peerIp];
                    const otherNode = ctx.nodesByIp[peerIp];
                    if (!otherNode) { continue; }
                    for (const link of links) {
                        outLinks.push([
                            "link",
                            Math.floor(link.mut.time / 1000),
                            "-",
                            node.key,
                            otherNode.key,
                            link.label
                        ]);
                    }
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
        } else if (ents[0] === 'debugnode') {
            ctx.mut.debugNode = ents[1];
        } else if (ents[0] === '') {
            res.end(JSON.stringify({
                peer: ctx.peer.info(),
                nodesByIp: Object.keys(ctx.nodesByIp).length
            }, null, '  '));
        } else {
            //warn(ctx, req.url);
            res.end(req.url);
        }
    };
    const httpServer = Http.createServer(reqHandler);
    ctx.peer.runServer(httpServer);
    httpServer.listen(3333);
};

const keepTableClean = (ctx /*:Context_t*/) => {
    setInterval(() => {
        //warn(ctx, "keepTableClean()");
        const minTime = now() - GLOBAL_TIMEOUT_MS;
        Object.keys(ctx.nodesByIp).forEach((nodeIp) => {
            const node = ctx.nodesByIp[nodeIp];
            if (minTime > Number('0x' + node.mut.timestamp)) {
                warn(ctx, "forgetting node [" + nodeIp + "]");
                delete ctx.nodesByIp[nodeIp];
                node.mut.announcements.forEach((ann) => { ctx.peer.deleteAnn(ann.hash); });
                if (node.mut.resetMsg) { ctx.peer.deleteAnn(node.mut.resetMsg.hash); }
            }
        });
    }, KEEP_TABLE_CLEAN_CYCLE);
};

const getConfig = () => {
    const confIdx = process.argv.indexOf('--config');
    return (require /*:(any)=>Config_t*/)(
        (confIdx > -1) ? process.argv[confIdx+1] : './config'
    );
};

const main = () => {
    const config = getConfig();
    let ctx = (Object.freeze({
        //nodesByKey: {},
        //ipnodes: {},
        nodesByIp: {},
        version: 1,

        config: config,
        peer: Peer.create(),

        mut: {
            debugNode: '',
            lastRebuild: +new Date(),
            dijkstra: undefined,
            selfNode: undefined,
            routeCache: {},
            currentNode: '',
        }
    }) /*:Context_t*/);

    keepTableClean(ctx);
    if (config.connectCjdns) { service(ctx); }
    testSrv(ctx);
    ctx.peer.onAnnounce((peer, msg) => { handleAnnounce(ctx, msg, false); });
    (ctx.config.peers || []).forEach(ctx.peer.connectTo);
};
main();

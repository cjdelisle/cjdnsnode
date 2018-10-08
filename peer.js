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
const WebSocket = require('ws');
const Msgpack = require('msgpack5');
const nThen = require('nthen');
/*::const Http = require('http');*///flow

const NOFUNC = ()=>{};

const DROP_AFTER_MS = 60000;
const PING_AFTER_MS = 20000;
const PING_CYCLE_MS = 5000;

const now = () => (+new Date());

const socketSendable = function (socket) {
    return socket && socket.readyState === 1;
};

const dropPeer = (ctx, peer) => {
    try { throw new Error(); } catch (e) { console.log(e.stack); }
    if (peer.socket.readyState !== 2 /* WebSocket.CLOSING */
        && peer.socket.readyState !== 3 /* WebSocket.CLOSED */)
    {
        try {
            peer.socket.close();
        } catch (e) {
            console.log("Failed to disconnect [" + peer.id + "], attempting to terminate");
            try {
                peer.socket.terminate();
            } catch (ee) {
                console.log("Failed to terminate [" + peer.id + "]  *shrug*");
            }
        }
    }
    const idx = ctx.peers.indexOf(peer);
    if (idx !== -1) {
        ctx.peers.splice(idx, 1);
    }
};

const SEND_BATCH_SZ = 10;

const doSend = (ctx, peer) => {
    peer.mut.sendArmed = false;
    if (!socketSendable(peer.socket)) {
        setTimeout(() => { doSend(ctx, peer); }, 100);
        peer.mut.sendArmed = true;
        return;
    }
    const list = peer.msgQueue.splice(0, SEND_BATCH_SZ);
    peer.mut.msgsOnWire += list.length;
    const last = list.pop();
    try {
        list.forEach((m) => { peer.socket.send(m, () => { peer.mut.msgsOnWire--; }); });
        if (last) {
            peer.socket.send(last, () => {
                peer.mut.msgsOnWire--;
                doSend(ctx, peer);
            });
            peer.mut.sendArmed = true;
        }
    } catch (e) {
        console.log(e.stack);
        dropPeer(ctx, peer);
    }
};

const sendPeerMsg = function (ctx, peer, msg) {
    peer.msgQueue.push(ctx.msgpack.encode(msg));
    if (!peer.mut.sendArmed) { doSend(ctx, peer); }
};

const getData = (ctx, peer, hash) => {
    const seq = ctx.mut.seq++;
    peer.outstandingRequests.push({ seq: seq, data: null });
    sendPeerMsg(ctx, peer, [seq, 'GET_DATA', new Buffer(hash, 'hex')]);
};

const NO_DATA /*:any*/ = Object.freeze({});

const acceptAnnounces = (ctx, peer) => {
    peer.mut.acceptAnnouncesArmed = false;
    const r = peer.outstandingRequests[0];
    if (!r || !r.data) { return; }
    peer.outstandingRequests.shift();
    if (r.data !== NO_DATA) {
        ctx.mut.onAnnounce(peer, r.data);
    } else {
        console.log("Response with no data");
    }
    peer.mut.acceptAnnouncesArmed = true;
    setTimeout(() => { acceptAnnounces(ctx, peer); });
};

const onData = (ctx, seq, peer, data) => {
    let ok = false;
    for (let i = 0; i < peer.outstandingRequests.length; i++) {
        const r = peer.outstandingRequests[i];
        if (seq !== r.seq) { continue; }
        r.data = data || NO_DATA;
        ok = true;
        break;
    }
    if (!ok) { throw new Error(); }
    if (!peer.mut.acceptAnnouncesArmed) { acceptAnnounces(ctx, peer); }
};

const handleMessage = (ctx, peer, message) => {
    const msg = ctx.msgpack.decode(message);
    if (typeof(msg[0]) !== 'number' || typeof(msg[1]) !== 'string') {
        throw new Error();
    }
    peer.mut.timeOfLastMessage = now();
    switch (msg[1]) {
        case 'OLLEH':
        case 'HELLO': {
            if (('HELLO' === msg[1]) !== peer.outgoing) {
                console.log("bad hello message");
                dropPeer(ctx, peer);
                return;
            }
            console.log("Connected to snode with version [" + ctx.version + "]");
            return;
        }
        case 'GET_DATA': {
            const hash = msg[2].toString('hex');
            const ann = ctx.annByHash[hash] || null;
            console.log('>GET_DATA');
            sendPeerMsg(ctx, peer, [msg[0], 'DATA', ann]);
            return;
        }
        case 'PING': {
            console.log('>PING');
            sendPeerMsg(ctx, peer, [msg[0], 'ACK']);
            return;
        }
        case 'ACK': {
            return;
        }
        case 'INV': {
            if (!peer.outgoing) { return; }
            const hexList = msg[3].map((x) => (x.toString('hex')));
            const needHex = hexList.filter((x) => (!(x in ctx.annByHash)));
            //console.log('>INV need: ' + needHex.length);
            //console.log("need: " + needHex.join('\n'));
            needHex.forEach((x) => {
                getData(ctx, peer, x);
                //sendPeerMsg(ctx, peer, [ctx.mut.seq++, 'GET_DATA', new Buffer(x, 'hex')]);
            });
            return;
        }
        case 'DATA': {
            if (!peer.outgoing) {
                console.log("Data from an incoming connection");
                return;
            }
            onData(ctx, msg[0], peer, msg[2]);
            //ctx.mut.onAnnounce(peer, msg[2]);
        }
    }
};

const mkPeer = (ctx, socket, isOutgoing) => {
    const peer = {
        id: ctx.mut.peerIdSeq++,
        socket: socket,
        outgoing: isOutgoing,
        mut: {
            timeOfLastMessage: now(),
            sendArmed: false,
            acceptAnnouncesArmed: false,
            msgsOnWire: 0
        },
        outstandingRequests: [],
        msgQueue: [],
    };
    socket.peer = peer;
    return peer;
};

const incoming = (ctx, socket) => {
    if (socket.upgradeReq.url !== '/cjdnsnode_websocket') {
        socket.close();
        return;
    }
    const peer = mkPeer(ctx, socket, false);
    console.log("Incoming connection");
    sendPeerMsg(ctx, peer, [0, 'HELLO', ctx.version]);
    ctx.peers.push(peer);
    const hashes = ctx.annHashesOrdered.map((x) => (new Buffer(x, 'hex')));
    while (hashes.length) {
        const h = hashes.splice(0, 128);
        sendPeerMsg(ctx, peer, [0, 'INV', 0, h]);
    }
    socket.on('message', function(message) {
        try {
            handleMessage(ctx, peer, message);
        } catch (e) {
            console.log(e.stack);
            dropPeer(ctx, peer);
        }
    });
    socket.on('close', function (evt) {
        dropPeer(ctx, peer);
    });
};

const connectTo = (ctx, url) => {
    const socket = new WebSocket(url, {
        perMessageDeflate: false
    });
    socket.on('error', (e) => {
        console.log(e);
        setTimeout(() => { connectTo(ctx, url); }, 10000);
    });
    nThen((waitFor) => {
        socket.on('open', waitFor());
    }).nThen((waitFor) => {
        console.log('Connected to ' + url);
        const peer = mkPeer(ctx, socket, true);
        ctx.peers.push(peer);
        socket.on('message', function(message) {
            try {
                handleMessage(ctx, peer, message);
            } catch (e) {
                console.log(e.stack);
                dropPeer(ctx, peer);
            }
        });
        socket.on('close', function (evt) {
            dropPeer(ctx, peer);
            setTimeout(() => { connectTo(ctx, url); }, 1000);
        });
        sendPeerMsg(ctx, peer, [0, 'OLLEH', ctx.version]);
    });
};

const addAnn = (ctx, hash, binary) => {
    ctx.annByHash[hash] = binary;
    if (ctx.annHashesOrdered.indexOf(hash) > -1) {
        console.log("Tried to add hash [" + hash + "] multiple times");
        return;
    }
    ctx.annHashesOrdered.push(hash);
    ctx.peers.forEach((p) => {
        if (p.outgoing) { return; }
        sendPeerMsg(ctx, p, [0, 'INV', 0, [ new Buffer(hash, 'hex') ] ]);
    });
};

const deleteAnn = (ctx, hash) => {
    for (;;) {
        const i = ctx.annHashesOrdered.indexOf(hash);
        if (i > -1) {
            ctx.annHashesOrdered.splice(i, 1);
        } else { break; }
    }
    delete ctx.annByHash[hash];
};

const pingCycle = (ctx) => {
    ctx.peers.forEach((p) => {
        const lag = now() - p.mut.timeOfLastMessage;
        if (lag > DROP_AFTER_MS) {
            dropPeer(ctx, p);
        } else if (lag > PING_AFTER_MS) {
            const seq = ctx.mut.seq++;
            sendPeerMsg(ctx, p, [seq, 'PING']);
            console.log('<PING ' + seq);
        }
    });
};

const runServer = (ctx, httpServer) => {
    const wsSrv = new WebSocket.Server({ server: httpServer });
    wsSrv.on('connection', (socket) => { incoming(ctx, socket); });
};

const create = module.exports.create = () => {
    const ctx = Object.freeze({
        peers: [],
        annByHash: {},
        annHashesOrdered: [],
        msgpack: Msgpack(),
        version: 1,
        mut: {
            seq: +new Date(),
            peerIdSeq: 0,
            pingCycle: undefined,
            onAnnounce: (x,y)=>{},
        }
    });
    ctx.mut.pingCycle = setInterval(() => { pingCycle(ctx); }, PING_CYCLE_MS);

    return {
        connectTo: (url /*:string*/) => { connectTo(ctx, url); },
        addAnn: (hash /*:string*/, binary /*:Buffer*/) => { addAnn(ctx, hash, binary); },
        deleteAnn: (hash /*:string*/) => { deleteAnn(ctx, hash); },
        runServer: (httpServer /*:Http.Server*/) => { runServer(ctx, httpServer); },
        onAnnounce: (handler /*:function*/) => { ctx.mut.onAnnounce = handler; },
        info: () => ({
            peers: ctx.peers.map((p) => ({
                addr: p.socket._socket.remoteAddress,
                outstandingRequests: p.outstandingRequests.length,
                msgsOnWire: p.mut.msgsOnWire,
                msgQueue: p.msgQueue.length
            })),
            announcements: ctx.annHashesOrdered.length,
            annByHashLen: Object.keys(ctx.annByHash).length
        })
    };
};

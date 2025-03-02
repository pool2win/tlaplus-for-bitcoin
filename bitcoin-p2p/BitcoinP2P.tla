--------------------------- MODULE BitcoinP2P ---------------------------
EXTENDS Naturals, Sequences

CONSTANT Nodes, Headers, Blocks, Transactions
VARIABLES knownBlocks, knownTransactions, knownHeaders, messages

(*--initial conditions--*)
Init == 
    /\ knownHeaders = [n \in Nodes |-> {}]
    /\ knownBlocks = [n \in Nodes |-> {}]
    /\ knownTransactions = [n \in Nodes |-> {}]
    /\ messages = {}

(*--actions--*)

(* Node n sends an inventory of a block to peers
   We send a single block in the inventory message for now *)
SendBlocksInv(n, b) ==
    /\ b \in Blocks
    /\ messages' = messages \union {[type |-> "inv", from |-> n, data |-> b]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

(* Node n sends an inventory of a header to peers
   We send a single header in the inventory message for now *)
SendHeadersInv(n, h) ==
    /\ h \in Headers
    /\ messages' = messages \union {[type |-> "inv", from |-> n, data |-> h]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

(* Node n sends an inventory of a transaction to peers
   We send a single transaction in the inventory message for now *)
SendTxInv(n, tx) ==
    /\ tx \in Transactions
    /\ messages' = messages \union {[type |-> "inv", from |-> n, data |-> tx]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

RequestHeaders(m, n, h) ==
    /\ h \in Headers
    /\ [type |-> "inv", from |-> m, data |-> h] \in messages
    /\ messages' = messages \union {[type |-> "getheaders", from |-> m, to |-> n, data |-> h]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

SendHeaders(m, n, h) ==
    /\ h \in Headers
    /\ [type |-> "getheaders", from |-> n, to |-> m, data |-> h] \in messages
    /\ messages' = messages \union {[type |-> "headers", from |-> n, to |-> m, data |-> h]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

(* Node n requests a block from peer m 
   Sent in response to an inventory message 
   m requests the block from n
   Note: In reality, the data part is the block hash, it doesn't matter in TLA spec *)
RequestBlock(m, n, b) ==
    /\ b \in Blocks 
    /\ [type |-> "inv", from |-> m, data |-> b] \in messages
    /\ messages' = messages \union {[type |-> "getdata", from |-> m, to |-> n, data |-> b]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

(* Node m sends a block to peer n
   Sent in response to a getdata message *)
SendBlock(m, n, b) ==
    /\ b \in knownBlocks[m]
    /\ [type |-> "getdata", from |-> n, to |-> m, data |-> b] \in messages
    /\ messages' = messages \union {[type |-> "block", from |-> m, to |-> n, data |-> b]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

RequestTx(n, tx) ==
    /\ tx \in Transactions
    /\ tx \notin knownTransactions[n]
    /\ messages' = messages \union {[type |-> "getdata", from |-> n, data |-> tx]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

SendTx(m, n, tx) ==
    /\ tx \in knownTransactions[m]
    /\ tx \notin knownTransactions[n]
    /\ [type |-> "getdata", from |-> n, to |-> m, data |-> tx] \in messages
    /\ messages' = messages \union {[type |-> "tx", from |-> m, to |-> n, data |-> tx]}
    /\ UNCHANGED<<knownHeaders, knownBlocks, knownTransactions>>

ReceiveHeaders(m, n, h) ==
    /\ h \in Headers
    /\ [type |-> "headers", from |-> m, to |-> n, data |-> h] \in messages
    /\ knownHeaders' = [knownHeaders EXCEPT ![n] = @ \union {h}]
    /\ UNCHANGED<<knownBlocks, knownTransactions, messages>>

ReceiveBlock(m, n, b) ==
    /\ b \in Blocks
    /\ b \notin knownBlocks[n]
    /\ [type |-> "block", from |-> m, to |-> n, data |-> b] \in messages
    /\ knownBlocks' = [knownBlocks EXCEPT ![n] = @ \union {b}]
    /\ UNCHANGED<<knownTransactions, messages>>

ReceiveTx(m, n, tx) ==
    /\ tx \in Transactions
    /\ tx \notin knownTransactions[n]
    /\ [type |-> "tx", from |-> m, to |-> n, data |-> tx] \in messages
    /\ knownTransactions' = [knownTransactions EXCEPT ![n] = @ \union {tx}]
    /\ UNCHANGED<<knownBlocks, messages>>

Next == 
    \/ \E n \in Nodes, b \in Blocks : SendBlocksInv(n, b)
    \/ \E n \in Nodes, b \in Headers : SendHeadersInv(n, b)
    \/ \E m, n \in Nodes, b \in Blocks : RequestBlock(m, n,b)
    \/ \E m, n \in Nodes, b \in Blocks : SendBlock(m, n, b)
    \/ \E n \in Nodes, tx \in Transactions : RequestTx(n, tx)
    \/ \E m, n \in Nodes, tx \in Transactions : SendTx(m, n, tx)
    \/ \E m, n \in Nodes, tx \in Transactions : ReceiveTx(m, n, tx)
(*--safety properties--*)

NoDuplicateHeaders ==
    \A n \in Nodes, h \in Headers :
        [type |-> "headers", to |-> n, data |-> h] \in messages => h \notin knownHeaders[n]


(* A node should never receive a block it already has *)
NoDuplicateBlocks == 
    \A n \in Nodes, b \in Blocks :
        [type |-> "block", to |-> n, data |-> b] \in messages => b \notin knownBlocks[n]

(* A node should never receive a transaction it already has *)
NoDuplicateTx == 
    \A n \in Nodes, tx \in Transactions :
        [type |-> "tx", to |-> n, data |-> tx] \in messages => tx \notin knownTransactions[n]

(*--properties to check--*)
Spec == Init /\ [][Next]_<<knownBlocks, knownTransactions, messages>>
===========================================================================

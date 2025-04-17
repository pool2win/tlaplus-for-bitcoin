-------------------------------- MODULE BitcoinChain --------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Nodes,      \* Set of nodes in the network
    MaxBlocks,  \* Maximum number of blocks that can be created. We need this to cap the model run.
    GenesisHash \* Hash of the genesis block

VARIABLES 
    blocksByNode,   \* blocksByNode[n] is the set of blocks known by node n
    chainsByNode,   \* chainsByNode[n] is the DAG of blocks for node n
    tipsByNode,     \* tipsByNode[n] is the current tip of the chain for node n
    workByNode,     \* workByNode[n] is a function mapping each block to its cumulative work
    confirmedByNode,\* confirmedByNode[n] is the set of confirmed blocks for node n
    network,        \* network[n] is the set of blocks in transit to node n
    nextBlockId     \* Counter used to generate unique block IDs

vars == <<blocksByNode, chainsByNode, tipsByNode, workByNode, confirmedByNode, network, nextBlockId>>

\* Type definitions
Block == [id: Nat, prevHash: Nat, nonce: Nat, timestamp: Nat]
Chain == [blocks: SUBSET Nat, edges: SUBSET (Nat \X Nat)]

\* Helper functions
WorkFor(b) == 1  \* Simplified work calculation, each block contributes 1 unit of work

\* Initial state
Init ==
    /\ blocksByNode = [n \in Nodes |-> {[id |-> 0, prevHash |-> GenesisHash, nonce |-> 0, timestamp |-> 0]}]
    /\ chainsByNode = [n \in Nodes |-> [blocks |-> {0}, edges |-> {}]]
    /\ tipsByNode = [n \in Nodes |-> 0]
    /\ workByNode = [n \in Nodes |-> [i \in {0} |-> 1]]  \* Initialize work for genesis block to 1
    /\ confirmedByNode = [n \in Nodes |-> {}]
    /\ network = [n \in Nodes |-> {}]
    /\ nextBlockId = 1

\* Action: Create a new block
CreateBlock(n) ==
    /\ nextBlockId < MaxBlocks
    /\ LET 
           newBlock == [id |-> nextBlockId, 
                       prevHash |-> tipsByNode[n], 
                       nonce |-> nextBlockId,  \* Simplified nonce
                       timestamp |-> nextBlockId]  \* Simplified timestamp
           updatedChain == [
                blocks |-> chainsByNode[n].blocks \union {nextBlockId},
                edges |-> chainsByNode[n].edges \union {<<tipsByNode[n], nextBlockId>>}
           ]
           newWork == workByNode[n][tipsByNode[n]] + WorkFor(newBlock)
           updatedWork == [workByNode[n] EXCEPT ![nextBlockId] = newWork]
           prevTip == tipsByNode[n] \* Previous tip before creating the new block
       IN
       \* Update the blocks known by the local node
       /\ blocksByNode' = [blocksByNode EXCEPT ![n] = @ \union {newBlock}]
       \* Update the chain for the local node
       /\ chainsByNode' = [chainsByNode EXCEPT ![n] = updatedChain]
       \* Update the tip for the local node
       /\ tipsByNode' = [tipsByNode EXCEPT ![n] = nextBlockId]
       \* Track total work for the new block at this node, even if it is a constant for now
       /\ LET 
            newWorkMap == [b \in DOMAIN workByNode[n] \union {nextBlockId} |->
                IF b = nextBlockId THEN newWork ELSE workByNode[n][b]]
            IN
                workByNode' = [workByNode EXCEPT ![n] = newWorkMap]       
       \* The new block will be received by all other nodes in the network
       /\ network' = [m \in Nodes |-> IF m # n THEN network[m] \union {newBlock} ELSE network[m]]
       \* Update the global nextBlockId
       /\ nextBlockId' = nextBlockId + 1
       \* Local node immediately confirms the previous tip
       /\ confirmedByNode' = [confirmedByNode EXCEPT ![n] = confirmedByNode[n] \union {prevTip}]

\* Action: Receive a block from the network
ReceiveBlockWithPreviousKnown(n, block) ==
    /\ block.prevHash \in chainsByNode[n].blocks
    /\
        LET 
            prevBlock == block.prevHash
            updatedChain == [
                                blocks |-> chainsByNode[n].blocks \union {block.id},
                                edges |-> chainsByNode[n].edges \union {<<prevBlock, block.id>>}
                           ]
            newWork == workByNode[n][tipsByNode[n]] + WorkFor(block)
            newTip == IF newWork > workByNode[n][tipsByNode[n]]
                     THEN block.id
                     ELSE tipsByNode[n]
        IN
        \* Add the block to the local node's known blocks
        /\ blocksByNode' = [blocksByNode EXCEPT ![n] = @ \union {block}]
        \* Take the next block in the receieve queue
        /\ network' = [network EXCEPT ![n] = @ \ {block}]
        \* Update the chain for the local node by adding a back ref to the previous block
        /\ chainsByNode' = [chainsByNode EXCEPT ![n] = updatedChain]
        \* Update the work seen by the node up to the block
        /\ LET 
            newWorkMap == [b \in DOMAIN workByNode[n] \union {block.id} |->
                IF b = block.id THEN newWork ELSE workByNode[n][b]]
            IN
                workByNode' = [workByNode EXCEPT ![n] = newWorkMap]     
        \* Confirm the previous tip if we have a new tip
        /\ IF newWork > workByNode[n][tipsByNode[n]] THEN 
                /\ confirmedByNode' = [confirmedByNode EXCEPT ![n] = confirmedByNode[n] \union {tipsByNode[n]}]
              ELSE
                /\ confirmedByNode' = confirmedByNode
        \* Update the tip for the local node
        /\ tipsByNode' = [tipsByNode EXCEPT ![n] = block.id]
        /\ UNCHANGED <<nextBlockId>>

\* Next state relation
Next ==
    \/ \E n \in Nodes: CreateBlock(n)
    \/ \E n \in Nodes: \E block \in network[n]: ReceiveBlockWithPreviousKnown(n, block)

\* Invariants
TypeInvariant ==
    /\ \A n \in Nodes:
        /\ nextBlockId \in Nat
        /\ tipsByNode[n] \in Nat
        /\ chainsByNode[n].blocks \subseteq Nat
        /\ chainsByNode[n].edges \subseteq (Nat \X Nat)
        /\ \A blockId \in DOMAIN workByNode[n]: 
               /\ blockId \in Nat
               /\ workByNode[n][blockId] \in Nat
        /\ confirmedByNode[n] \subseteq Nat
        /\ network[n] \subseteq Block
        /\ \A b \in blocksByNode[n]: 
            /\ b.id \in Nat
            /\ b.prevHash \in Nat
            /\ b.nonce \in Nat
            /\ b.timestamp \in Nat

\* Properties
TipHasMostWork ==
    \A n \in Nodes:
        \A b \in chainsByNode[n].blocks:
            workByNode[n][tipsByNode[n]] >= workByNode[n][b]

\* Complete specification
Spec == Init /\ [][Next]_vars

=============================================================================
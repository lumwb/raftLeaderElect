----------------------------- MODULE RaftLeaderElect -----------------------------
EXTENDS Integers, Naturals, FiniteSets
            
CONSTANT Servers, Term \* input id of servers and number of election rounds

VARIABLES 
    serverState, \* serverState[id] is the state of server: follower, leader, candidate
    currentTerm, \* currentTerm[id] is the current term of server: 
    votedFor, \* votedFor[id] is the server id votedFor in currentTerm. 
    msgs
  

Maximum(S) == 
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n \geq m
            
Majority == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

\* returns the next term if within set S else return current term 
ChooseTerm(S, term) ==
    IF term + 1 \in S THEN term + 1
        ELSE term

Messages ==
    [type : {"appendEntriesRPC"}, leaderId : Servers, term : Nat]
        \cup
    [type: {"requestVoteRPC"}, candidateId : Servers, term : Nat]
        \cup
    [type: {"replyRequestVoteRPC"}, term : Nat, fromServer : Servers, toServer : Servers]


RLTypeOK ==
    /\ serverState \in [Servers -> {"follower", "leader", "candidate"}] 
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {0}]
    /\ msgs \subseteq Messages   
            
RLInit ==
    /\ serverState = [id \in Servers |-> "follower"]
    /\ currentTerm = [id \in Servers |-> 0]
    /\ votedFor = [id \in Servers |-> 0]
    /\ msgs = {}
    
Send(m) == msgs' = msgs \cup {m}

\*before election should be in follower state
ElectionTimeout(id) == 
    LET nextTerm == ChooseTerm(Term, currentTerm[id])
    IN
        /\ nextTerm /= currentTerm[id] \* ignore if unable to increment term
        /\ serverState[id] = "follower"
        /\ currentTerm' = [currentTerm EXCEPT ![id] = nextTerm]
        /\ votedFor' = [votedFor EXCEPT ![id] = id]
        /\ serverState' = [serverState EXCEPT ![id] = "candidate"]
        /\ Send([type |-> "requestVoteRPC", candidateId |-> id, term |-> currentTerm'[id]])
    
    
BothLeader( i, j ) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ serverState[i] = "leader"
    /\ serverState[j] = "leader"

OneLeader ==
    ~\E i, j \in Servers : BothLeader(i, j)

ReceiveElectionTimeout(id) ==
    /\ \E m \in msgs:
        /\ m.type = "requestVoteRPC"
        /\
            \/ 
                /\ m.term > currentTerm[id]
                /\ votedFor' = [votedFor EXCEPT ![id] = m.candidateId]
                /\ currentTerm' = [currentTerm EXCEPT ![id] = m.term]
                /\ serverState' = [serverState EXCEPT ![id] = "follower"]
                /\ Send([type |-> "replyRequestVoteRPC", term |-> m.term, fromServer |-> id, toServer |-> m.candidateId])
            \/
                /\ m.term = currentTerm[id]
                /\ (votedFor[id] = 0) \/ (votedFor[id] = m.candidateId)
                /\ votedFor' = [votedFor EXCEPT ![id] = m.candidateId]
                /\ serverState' = [serverState EXCEPT ![id] = "follower"]
                /\ Send([type |-> "replyRequestVoteRPC", term |-> m.term, fromServer |-> id, toServer |-> m.candidateId])
                /\ UNCHANGED currentTerm
            

DecideLeader(id) ==
    /\ \E MS \in Majority :
        LET electionResults == {m \in msgs : 
                                    /\ m.type = "replyRequestVoteRPC"
                                    /\ m.term  = currentTerm[id]
                                    /\ m.toServer = id
                                    /\ m.fromServer \in MS}
        IN  /\ \A voterId \in MS : \E m \in electionResults : m.fromServer = voterId
            /\ serverState[id] = "candidate"
            /\ serverState' = [serverState EXCEPT ![id] = "leader"]
            /\ UNCHANGED <<currentTerm, votedFor, msgs>>


RLNext ==
    \E id \in Servers:
        \/ ElectionTimeout(id)
        \/ ReceiveElectionTimeout(id)
        \/ DecideLeader(id)
        
    
RLSpec == RLInit /\ [][RLNext]_<<serverState, currentTerm, msgs>>
=============================================================================
\* Modification History
\* Last modified Tue Nov 02 15:01:55 SGT 2021 by lumweiboon
\* Last modified Tue Jul 06 21:46:29 SGT 2021 by lumwb
\* Created Thu Jul 01 15:06:26 SGT 2021 by lumwb

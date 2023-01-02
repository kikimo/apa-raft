-------- MODULE Raft -------------

EXTENDS FiniteSets, Integers, Apalache, TLC

CONSTANTS
    \* @type: Set(Str);
    Servers,
	\* @type: Int;
	MaxTerm

\* role definitions
Follower == "Follower"

Candidate == "Candidate"

Leader == "Leader"

\* msg types
VoteReq == "VoteReq"

VoteResp == "VoteResp"

\* a non-exist peer
None == "None"

(*
 @typeAlias: raftMsg = {
	mType: Str,
	term: Int,
	src: Str,
	dst: Str,
	prevLogIndex: Int,
	prevLogTerm: Int,
	entries: Seq(Int),
	succ: Bool
 };
*)
Raft_typedefs == TRUE

VARIABLES
    \* @type: Str -> Str;
    role,

    \* @type: Str -> Int;
    currentTerm,
    \* @type: Str -> Str;
    votedFor,
    \* @type: Str -> Seq(Int);
    logs,

    \* @type: Set($raftMsg);
    msgs

\* Majority == { s \in SUBSET Servers :  Cardinality(s) = Cardinality(Servers) \div 2 + 1}

BecomeCandidate(s) ==
  /\ role[s] = Follower
  /\ currentTerm[s] < MaxTerm
  /\ role' = [ role EXCEPT ![s] = Candidate ]
  /\ currentTerm' = [ currentTerm EXCEPT ![s] = currentTerm[s] + 1 ]
  /\ votedFor' = [ votedFor EXCEPT ![s] = s  ]
  /\ UNCHANGED << logs, msgs >>

SendMsg(m) == msgs' = {m} \union msgs

\* become follower or update term
BecomeFollower(s) ==
  \E m \in msgs:
    /\ m.dst = s
    /\ m.term > currentTerm[s]
	/\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
	/\ role' = [ role EXCEPT ![s] = Follower  ]
    /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
	/\ UNCHANGED << logs, msgs >>

RequestVote(s) ==
  /\ role[s] = Candidate
  /\ \E p \in Servers\{s}:
	   LET
         m == [
           mType |-> VoteReq,
           term |-> currentTerm[s],
           src |-> s,
           dst |-> p,
           prevLogIndex |-> 0,
           prevLogTerm |-> 0,
           entries |-> << >>,
           succ |-> FALSE
         ]
	   IN
         /\ m \notin msgs
         /\ SendMsg(m)
         /\ UNCHANGED << role, currentTerm, votedFor, logs >>

ResponseVote(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.mType = VoteReq
       /\ votedFor[s] = None
       /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]
       /\ LET
            vresp == [
              mType |-> VoteResp,
              term |-> currentTerm[s],
              src |-> s,
              dst |-> m.src,
              prevLogIndex |-> 0,
              prevLogTerm |-> 0,
              entries |-> << >>,
              succ |-> TRUE
            ]
          IN	     
            /\ SendMsg(vresp)
            /\ UNCHANGED << role, currentTerm, logs >>

BecomeLeader(s) ==
  /\ role[s] = Candidate
  /\ LET
       voteResps == { m \in msgs : /\ m.dst = s
                                   /\ m.mType = VoteResp
								   /\ m.succ = TRUE
								   /\ m.term = currentTerm[s] }
       peers == { m.src : m \in voteResps } \union {s}
     IN
       \* /\ \E quorum \in Majority: quorum \subseteq peers
	   /\ Cardinality(peers) >= Cardinality(Servers) \div 2 + 1
	   /\ role' = [ role EXCEPT ![s] = Leader ]
	   /\ UNCHANGED << currentTerm, votedFor, logs, msgs >>

Init ==
  /\ role = [ s \in Servers |-> Follower ]
  /\ currentTerm = [ s \in Servers |-> 0 ]
  /\ votedFor = [ s \in Servers |-> None ]
  /\ logs = [ s \in Servers |-> << 0 >> ]
  /\ msgs = {}

Next ==
  \/ \E s \in Servers: BecomeCandidate(s)
  \/ \E s \in Servers: BecomeFollower(s)
  \/ \E s \in Servers: RequestVote(s)
  \/ \E s \in Servers: ResponseVote(s)
  \/ \E s \in Servers: BecomeLeader(s)

\* invariants
TwoLeaderInATerm ==
  \E s1, s2 \in Servers:
    /\ s1 # s2
	/\ currentTerm[s1] = currentTerm[s2]
	/\ role[s1] = Leader
	/\ role[s2] = Leader

NoSplitBrain == ~ TwoLeaderInATerm

NoLeaderElected == \A s \in Servers: role[s] # Leader

Inv ==
  /\ NoSplitBrain
  \* /\ NoLeaderElected

==================================


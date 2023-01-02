-------- MODULE Raft -------------

EXTENDS FiniteSets, Integers, Apalache, TLC, Sequences

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Int;
    MaxTerm,
    \* @type: Int;
    MaxLogSize

\* role definitions
Follower == "Follower"

Candidate == "Candidate"

Leader == "Leader"

\* msg types
VoteReq == "VoteReq"

VoteResp == "VoteResp"

AppendReq == "AppendReq"

AppendResp == "AppendResp"

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
   lastLogIndex: Int,
   lastLogTerm: Int,
   entries: Seq(Int),
   leaderCommit: Int,
   succ: Bool
 };
*)
Raft_typedefs == TRUE


MajorSize == Cardinality(Servers) \div 2 + 1

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
    msgs,

    \* @type: Str -> Str -> Int;
    nextIndex,

    \* @type: Str -> Str -> Int;
    matchIndex,

    \* @type: Str -> Int;
    commitIndex

\* Majority == { s \in SUBSET Servers :  Cardinality(s) = Cardinality(Servers) \div 2 + 1}

BecomeCandidate(s) ==
  /\ role[s] = Follower
  /\ currentTerm[s] < MaxTerm
  /\ role' = [ role EXCEPT ![s] = Candidate ]
  /\ currentTerm' = [ currentTerm EXCEPT ![s] = currentTerm[s] + 1 ]
  /\ votedFor' = [ votedFor EXCEPT ![s] = s  ]
  /\ UNCHANGED << logs, msgs, nextIndex, matchIndex, commitIndex >>

SendMsg(m) == msgs' = {m} \union msgs

\* become follower or update term
BecomeFollower(s) ==
  \E m \in msgs:
    /\ m.dst = s
    /\ m.term > currentTerm[s]
	/\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
	/\ role' = [ role EXCEPT ![s] = Follower  ]
    /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
	/\ UNCHANGED << logs, msgs, nextIndex, matchIndex, commitIndex >>

RequestVote(s) ==
  /\ role[s] = Candidate
  /\ \E p \in Servers\{s}:
	   LET
         lastLogIndex == Len(logs[s])
         lastLogTerm == logs[s][lastLogIndex]
         m == [
           mType |-> VoteReq,
           term |-> currentTerm[s],
           src |-> s,
           dst |-> p,
           prevLogIndex |-> 0,
           prevLogTerm |-> 0,
           lastLogIndex |-> lastLogIndex,
           lastLogTerm |-> lastLogTerm,
           entries |-> << >>,
           leaderCommit |-> 0,
           succ |-> FALSE
         ]
	   IN
         /\ m \notin msgs
         /\ SendMsg(m)
         /\ UNCHANGED << role, currentTerm, votedFor, logs, nextIndex, matchIndex, commitIndex >>

\* @type: (Str, $raftMsg) => Bool;
CanVote(s, m) ==
  LET
    lastLogIndex == Len(logs[s])
    lastLogTerm == logs[s][lastLogIndex]
  IN
    \/ m.lastLogTerm > lastLogTerm
	\/ /\ m.lastLogTerm = lastLogTerm
	   /\ m.lastLogIndex >= lastLogIndex

ResponseVote(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.mType = VoteReq
       /\ votedFor[s] = None
       /\ CanVote(s, m)
       /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]
       /\ LET
            vresp == [
              mType |-> VoteResp,
              term |-> currentTerm[s],
              src |-> s,
              dst |-> m.src,
              prevLogIndex |-> 0,
              prevLogTerm |-> 0,
              lastLogIndex |-> 0,
              lastLogTerm |-> 0,
              entries |-> << >>,
              leaderCommit |-> 0,
              succ |-> TRUE
            ]
          IN	     
            /\ SendMsg(vresp)
            /\ UNCHANGED << role, currentTerm, logs, nextIndex, matchIndex, commitIndex >>

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
	   /\ nextIndex' = [ nextIndex EXCEPT ![s] = [ p \in Servers |-> Len(logs[s]) + 1 ] ]
	   /\ matchIndex' = [ matchIndex EXCEPT ![s] = [ p \in Servers |-> 1 ] ]
	   /\ UNCHANGED << currentTerm, votedFor, logs, msgs, commitIndex >>

ClientReq(s) ==
  /\ role[s] = Leader
  /\ Len(logs[s]) < MaxLogSize
  /\ logs' = [ logs EXCEPT ![s] = Append(logs[s], currentTerm[s]) ]
  /\ matchIndex' = [ matchIndex EXCEPT ![s][s] = Len(logs[s]) + 1 ] 
  /\ UNCHANGED << role, currentTerm, votedFor, msgs, nextIndex, commitIndex >>

LeaderAppendEntry(s) ==
  /\ role[s] = Leader
  /\ \E p \in Servers\{s}:
       /\ nextIndex[s][p] <= Len(logs[s]) + 1
       /\ LET
            prevLogIndex == nextIndex[s][p] - 1
            prevLogTerm == logs[s][prevLogIndex]
            entries == SubSeq(logs[s], nextIndex[s][p], Len(logs[s]))
            m == [
              mType |-> AppendReq,
              term |-> currentTerm[s],
              src |-> s,
              dst |-> p,
              prevLogIndex |-> prevLogIndex,
              prevLogTerm |-> prevLogTerm,
              lastLogIndex |-> 0,
              lastLogTerm |-> 0,
              entries |-> entries,
              leaderCommit |-> commitIndex[s],
              succ |-> FALSE
            ]
          IN
            /\ m \notin msgs
			/\ SendMsg(m)
			/\ UNCHANGED << role, currentTerm, votedFor, logs, nextIndex, matchIndex, commitIndex >>

\* @type: (Str, $raftMsg) => Bool;
IsLogMatch(s, m) ==
  /\ m.prevLogIndex <= Len(logs[s])
  /\ m.prevLogTerm = logs[s][m.prevLogIndex]

\* @type: (Int, Int) => Int;
Min(a, b) ==
  IF a < b THEN a ELSE b

FollowerAppendEntry(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.mType = AppendReq
       /\ IF IsLogMatch(s, m) THEN
            LET
              accResp == [
                mType |-> AppendResp,
                term |-> currentTerm[s],
                src |-> s,
                dst |-> m.src,
                prevLogIndex |-> m.prevLogIndex + Len(m.entries),
                prevLogTerm |-> 0,
                lastLogIndex |-> 0,
                lastLogTerm |-> 0,
                entries |-> << >>,
                leaderCommit |-> 0,
                succ |-> TRUE
              ]

              newLog == SubSeq(logs[s], 1, m.prevLogIndex) \o m.entries
              appendNew == Len(newLog) > Len(logs[s])
              truncated == /\ Len(newLog) <= Len(logs[s])
                           /\ newLog # SubSeq(logs[s], 1, Len(newLog))
              updateLog == appendNew \/ truncated
              newCommitIndex == Min(Len(newLog), m.leaderCommit)
            IN
              /\ accResp \notin msgs
              /\ commitIndex' = [ commitIndex EXCEPT ![s] = newCommitIndex ]
              /\ SendMsg(accResp)
              /\ IF updateLog THEN
                   /\ logs' = [ logs EXCEPT ![s] = newLog ]
                   \* /\ Print([ msg |-> m, logs |-> logs[s], entries |-> m.entries, newLog |-> newLog ], TRUE)
                   /\ UNCHANGED << role, currentTerm, votedFor, nextIndex, matchIndex>>
                 ELSE
                   /\ UNCHANGED << role, currentTerm, votedFor, logs, nextIndex, matchIndex >>
          ELSE
            LET
              rejResp == [
                mType |-> AppendResp,
                term |-> currentTerm[s],
                src |-> s,
                dst |-> m.src,
                prevLogIndex |-> m.prevLogIndex - 1,
                prevLogTerm |-> 0,
                lastLogIndex |-> 0,
                lastLogTerm |-> 0,
                entries |-> << >>,
                leaderCommit |-> 0,
                succ |-> FALSE
              ]
            IN
              /\ rejResp \notin msgs
              /\ SendMsg(rejResp)
              /\ UNCHANGED << role, currentTerm, votedFor, logs, nextIndex, matchIndex, commitIndex >>

\* leader handle append response
HandleAppendResp(s) ==
  /\ role[s] = Leader
  /\ \E m \in msgs:
    /\ m.mType = AppendResp
    /\ m.dst = s
    /\ m.term = currentTerm[s]
    /\ IF m.succ THEN
         /\ matchIndex[s][m.src] < m.prevLogIndex
         /\ matchIndex' = [ matchIndex EXCEPT ![s][m.src] = m.prevLogIndex ]
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         \* TODO commit entry if possible
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, logs>>
       ELSE
         \* enabling condition
         /\ m.prevLogIndex + 2 = nextIndex[s][m.src]
         /\ m.prevLogIndex >= matchIndex[s][m.src]
         /\ nextIndex[s][m.src] # m.prevLogIndex + 1
         \* /\ Assert(m.prevLogIndex + 1 > matchIndex[s][m.src], {s, m, matchIndex[s], nextIndex[s]})
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, matchIndex, logs>>

\* optmize me: try commit only on receiving AppendResp
LeaderCommit(s) ==
  /\ role[s] = Leader
  /\ LET
       mset == { p \in Servers: Cardinality({ x \in Servers : matchIndex[s][x] <= matchIndex[s][p] }) >= MajorSize }
       indexes == { matchIndex[s][p] : p \in mset }
       median == CHOOSE idx \in indexes: (\A e \in indexes: idx <= e)
     IN
       /\ median > commitIndex[s]
       \* /\ Print({s, currentTerm[s], median}, TRUE)
       /\ commitIndex' = [ commitIndex EXCEPT ![s] = median ]
       /\ UNCHANGED << role, currentTerm, votedFor, logs, msgs, nextIndex, matchIndex >>

Init ==
  /\ role = [ s \in Servers |-> Follower ]
  /\ currentTerm = [ s \in Servers |-> 0 ]
  /\ votedFor = [ s \in Servers |-> None ]
  /\ logs = [ s \in Servers |-> << 0 >> ]
  /\ msgs = {}
  /\ nextIndex = [ s \in Servers |-> [ t \in Servers |-> 0 ] ]
  /\ matchIndex = [ s \in Servers |-> [ t \in Servers |-> 0 ]]
  /\ commitIndex = [ s \in Servers |-> 1 ]

Next ==
  \/ \E s \in Servers: BecomeCandidate(s)
  \/ \E s \in Servers: BecomeFollower(s)
  \/ \E s \in Servers: RequestVote(s)
  \/ \E s \in Servers: ResponseVote(s)
  \/ \E s \in Servers: BecomeLeader(s)
  \/ \E s \in Servers: ClientReq(s)
  \/ \E s \in Servers: LeaderAppendEntry(s)
  \/ \E s \in Servers: FollowerAppendEntry(s)
  \/ \E s \in Servers: LeaderCommit(s)

\* invariants
TwoLeaderInATerm ==
  \E s1, s2 \in Servers:
    /\ s1 # s2
	/\ currentTerm[s1] = currentTerm[s2]
	/\ role[s1] = Leader
	/\ role[s2] = Leader

NoSplitBrain == ~ TwoLeaderInATerm

NoLeaderElected == \A s \in Servers: role[s] # Leader

\* commit index increasing monotonic
CommitIndexMonoIncr == \A s \in Servers: commitIndex'[s] >= commitIndex[s]

NeverCommit == \A s \in Servers: commitIndex[s] <= 1

Inv ==
  /\ NeverCommit
  \* /\ CommitIndexMonoIncr
  \* /\ NoSplitBrain
  \* /\ NoLeaderElected

==================================


---------- MODULE MC -------------

EXTENDS Apalache

\* Servers == {"s1", "s2", "s3", "s4", "s5"}
Servers == { "s1", "s2", "s3" }

MaxTerm == 3

MaxLogSize == 2

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

INSTANCE Raft

==========================


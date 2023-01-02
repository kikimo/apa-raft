---------- MODULE MC -------------

EXTENDS Apalache

Servers == {"s1", "s2", "s3", "s4", "s5"}
MaxTerm == 4

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

INSTANCE Raft

==========================


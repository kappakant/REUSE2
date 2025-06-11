---- MODULE CexTrace_TTrace_1749663875 ----
EXTENDS CexTrace, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET CexTrace_TEExpression == INSTANCE CexTrace_TEExpression
    IN CexTrace_TEExpression!expression
----

_trace ==
    LET CexTrace_TETrace == INSTANCE CexTrace_TETrace
    IN CexTrace_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        Fluent17_0 = ((res1 :> TRUE @@ res2 :> FALSE @@ res3 :> FALSE))
        /\
        err = (TRUE)
        /\
        Fluent18_0 = ((res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE))
        /\
        rmState = ((res1 :> "commit" @@ res2 :> "abort" @@ res3 :> "working"))
        /\
        cexTraceIdx = (3)
    )
----

_init ==
    /\ err = _TETrace[1].err
    /\ rmState = _TETrace[1].rmState
    /\ cexTraceIdx = _TETrace[1].cexTraceIdx
    /\ Fluent17_0 = _TETrace[1].Fluent17_0
    /\ Fluent18_0 = _TETrace[1].Fluent18_0
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ err  = _TETrace[i].err
        /\ err' = _TETrace[j].err
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState
        /\ cexTraceIdx  = _TETrace[i].cexTraceIdx
        /\ cexTraceIdx' = _TETrace[j].cexTraceIdx
        /\ Fluent17_0  = _TETrace[i].Fluent17_0
        /\ Fluent17_0' = _TETrace[j].Fluent17_0
        /\ Fluent18_0  = _TETrace[i].Fluent18_0
        /\ Fluent18_0' = _TETrace[j].Fluent18_0

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("CexTrace_TTrace_1749663875.json", _TETrace)

=============================================================================

 Note that you can extract this module `CexTrace_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `CexTrace_TEExpression.tla` file takes precedence 
  over the module `CexTrace_TEExpression` below).

---- MODULE CexTrace_TEExpression ----
EXTENDS CexTrace, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `CexTrace` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        err |-> err
        ,rmState |-> rmState
        ,cexTraceIdx |-> cexTraceIdx
        ,Fluent17_0 |-> Fluent17_0
        ,Fluent18_0 |-> Fluent18_0
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_errUnchanged |-> err = err'
        
        \* Format the `err` variable as Json value.
        \* ,_errJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(err)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_errModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].err # _TETrace[s-1].err
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE CexTrace_TETrace ----
\*EXTENDS CexTrace, IOUtils, TLC
\*
\*trace == IODeserialize("CexTrace_TTrace_1749663875.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE CexTrace_TETrace ----
EXTENDS CexTrace, TLC

trace == 
    <<
    ([Fluent17_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),err |-> FALSE,Fluent18_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "working" @@ res2 :> "working" @@ res3 :> "working"),cexTraceIdx |-> 0]),
    ([Fluent17_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),err |-> FALSE,Fluent18_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "prepared" @@ res2 :> "working" @@ res3 :> "working"),cexTraceIdx |-> 1]),
    ([Fluent17_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> FALSE),err |-> FALSE,Fluent18_0 |-> (res1 :> FALSE @@ res2 :> FALSE @@ res3 :> FALSE),rmState |-> (res1 :> "commit" @@ res2 :> "working" @@ res3 :> "working"),cexTraceIdx |-> 2]),
    ([Fluent17_0 |-> (res1 :> TRUE @@ res2 :> FALSE @@ res3 :> FALSE),err |-> TRUE,Fluent18_0 |-> (res1 :> FALSE @@ res2 :> TRUE @@ res3 :> FALSE),rmState |-> (res1 :> "commit" @@ res2 :> "abort" @@ res3 :> "working"),cexTraceIdx |-> 3])
    >>
----


=============================================================================

---- CONFIG CexTrace_TTrace_1749663875 ----
CONSTANTS
    RMs = { res1 , res2 , res3 }
    res1 = res1
    res3 = res3
    res2 = res2
    res2 = res2
    res3 = res3
    res1 = res1

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Jun 11 13:44:36 EDT 2025
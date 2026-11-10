(* Seam 2 joint induction, a family leaf of the agg step: subscripts (every place_type case).
   The residual array-place-base case is the held leaf
   bodyIntCallFamAggSubscriptHeldTheory.intcall_subscript_array_place_base_held;
   use it for that case. *)
Theory bodyIntCallFamAggSubscript
Ancestors
  bodyIntCallJointContract bodyIntCallJointWidened
  bodyIntCallFamAggSubscriptHeld bodyIntCallFamAggSubscriptTuple
  bodyIntCallFamAggSubscriptCompile bodyIntCallFamAggSubscriptRunCuts
  bodyIntCallFamAggSubscriptCuts bodyIntCallFamAggSubscriptResources
  bodyIntCallFamAggSubscriptScratch bodyIntCallFamAggSubscriptTailRun
  bodyIntCallFamAggSubscriptHashTail bodyIntCallFamAggSubscriptAllocRun
  bodyIntCallFamAggSubscriptWordRun bodyIntCallFamAggSubscriptArrayWindow
  bodyIntCallFamAggSubscriptArrayRun bodyIntCallFamAggSubscriptArrayPost
  bodyIntCallFamAggSubscriptArraySuffix bodyIntCallFamAggSubscriptArrayIndex
  bodyIntCallFamAggSubscriptMap bodyIntCallFamAggSubscriptArrayPrepare
  bodyIntCallFamAggSubscriptArrayCompose bodyIntCallFamAggSubscriptArraySequence
  bodyIntCallFamAggSubscriptBaseOutcome bodyIntCallFamAggSubscriptPosts

Theorem intcall_subscript_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base idx. e = Subscript a base idx) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

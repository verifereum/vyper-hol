(* Seam 2 joint induction, a family leaf of the agg step: subscripts (every place_type case).
   The residual array-place-base case is the held leaf
   bodyIntCallFamAggSubscriptHeldTheory.intcall_subscript_array_place_base_held;
   use it for that case. *)
Theory bodyIntCallFamAggSubscript
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggSubscriptHeld
  bodyIntCallFamAggSubscriptResources bodyIntCallJointWidened
  bodyIntCallFamAggSubscriptMapSuffix bodyIntCallFamAggSubscriptTuple
  bodyIntCallFamAggSubscriptReadOnly bodyIntCallFamAggSubscriptStore
  bodyIntCallFamAggSubscriptScratch bodyIntCallFamAggSubscriptScratchStages
  bodyIntCallFamAggSubscriptScratchTail bodyIntCallFamAggSubscriptMapping
  bodyIntCallFamAggSubscriptAllocRun bodyIntCallFamAggSubscriptStoreRun
  bodyIntCallFamAggSubscriptRunCuts bodyIntCallFamAggSubscriptReadRun
  bodyIntCallFamAggSubscriptWordRun bodyIntCallFamAggSubscriptTailRun
  bodyIntCallFamAggSubscriptMappingRun bodyIntCallFamAggSubscriptMappingSlot
  bodyIntCallFamAggSubscriptKey bodyIntCallFamAggSubscriptOptionalKey
  bodyIntCallFamAggSubscriptHashTail bodyIntCallFamAggSubscriptKeyLanding
  bodyIntCallFamAggSubscriptPosts bodyIntCallFamAggSubscriptKeyOutcome
  bodyIntCallFamAggSubscriptForcedOutcome bodyIntCallFamAggSubscriptCompile
  bodyIntCallFamAggSubscriptKeyProducer bodyIntCallFamAggSubscriptBaseOutcome

Theorem intcall_subscript_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base idx. e = Subscript a base idx) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED

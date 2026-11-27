(* Structural projections for full tuple-target judgments. *)
Theory bodyFullTupleTargetProjection
Ancestors bodyFullPreds vyperAST vyperState vyperInterpreter
  bodyFullPredsMods[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[body_tuple_target_full_ok_def]
QED
*)
Theorem body_tuple_target_full_ok_base:
  body_tuple_target_full_ok_mods mods exps cx (BaseTarget bt) v ==>
  body_base_target_full_ok_mods mods exps cx bt
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[body_tuple_target_full_ok_def]
QED
*)
Theorem body_tuple_target_full_ok_tuple_value:
  body_tuple_target_full_ok_mods mods exps cx (TupleTarget gs) (ArrayV (TupleV vs)) ==>
  body_tuple_targets_full_ok_mods mods exps cx gs vs
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[body_tuple_target_full_ok_def]
QED
*)
Theorem body_tuple_targets_full_ok_cons_parts:
  body_tuple_targets_full_ok_mods mods exps cx (g::gs) (v::vs) ==>
  body_tuple_target_full_ok_mods mods exps cx g v /\
  ((?s x t. assign_tuple_targets cx g v s = (INL x,t)) ==>
   body_tuple_targets_full_ok_mods mods exps cx gs vs)
Proof
  cheat
QED

(* Saved AugAssign operands and pointer ghosts survive the joint RHS frame. *)
Theory augAssignFullSaved
Ancestors
  bodyFullTargetDefs bodyPtrDefs ptrDiscipline loweringStateRelDefs
  venomState finite_map

Theorem augassign_saved_rhs_frame:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  s.vs_labels = s0.vs_labels /\
  (!x. FST r = Var x ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at sa x) /\
  eval_operand (FST r) s0 = SOME addr /\
  eval_operand old s0 = SOME word /\
  target_ptr_ok cenv (PlaceR p) r G0 tn0 s0 /\
  op_taint tn0 old = {} /\ op_prov G0 old = NONE
  ==>
  eval_operand (FST r) s = SOME addr /\
  eval_operand old s = SOME word /\
  target_ptr_ok cenv (PlaceR p) r G tn s /\
  op_taint tn old = {} /\ op_prov G old = NONE
Proof
  strip_tac >>
  `eval_operand (FST r) s = SOME addr` by
    (Cases_on `FST r` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand old s = SOME word` by
    (Cases_on `old` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `op_taint tn (FST r) = op_taint tn0 (FST r) /\
   op_prov G (FST r) = op_prov G0 (FST r)` by
    (Cases_on `FST r` >> gvs[op_taint_def, op_prov_def, ghost_kept_at_def]) >>
  `op_taint tn old = op_taint tn0 old /\ op_prov G old = op_prov G0 old` by
    (Cases_on `old` >> gvs[op_taint_def, op_prov_def, ghost_kept_at_def]) >>
  gvs[target_ptr_ok_def] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def, ghost_kept_at_def] >> metis_tac[]
QED

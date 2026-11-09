(* Memory-safe tails with allocation posts at the same endpoint. *)
Theory bodyMemBopRestWordTailMem
Ancestors
  bodyMemBopRestWordPath exprSimBopRestWordTail

Theorem rest_word_fixed_tail_mem:
  compile_var_array_membership cenv needleop vv (ArrayT ty (Fixed n)) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv s /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\ loc <> LocCalldata /\
  expr_type e = ArrayT ty (Fixed n) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Fixed n)) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Fixed n)) (ArrayV av) /\ value_has_type et needle /\
  eval_operand needleop s = SOME (typed_val_to_w256 et needle) /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. needleop = Var z \/ vv_operand vv = Var z ==> not_fresh_at sm z) /\
  n < dimword (:256) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path T execctx fn s 0 (OK t) /\
      alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      t.vs_current_bb = ct.cs_current_bb /\
      t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
      vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv t /\
      eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
      eval_operand (vv_operand vv) t = SOME baseword /\
      eval_operand out t = SOME (bool_to_word
        (if is_in then evaluate_in_array (ArrayTV et (Fixed n)) needle av
         else ~evaluate_in_array (ArrayTV et (Fixed n)) needle av))
Proof
  strip_tac >>
  `read_result cx (Value (ArrayV av)) es' = (INL (ArrayV av), es')` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all (Q.INST [`memory` |-> `T`, `tv` |-> `Value (ArrayV av)`]
               rest_word_fixed_tail) >>
  disch_then (qspec_then `execctx` strip_assume_tac) >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_dynamic_tail_mem:
  compile_var_array_membership cenv needleop vv (ArrayT ty (Dynamic cap)) is_in sm = (out,ct) /\
  fn_has_code sm ct fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv s /\
  loc = (case vv_location vv of SOME l => l | NONE => LocMemory) /\ loc <> LocCalldata /\
  expr_type e = ArrayT ty (Dynamic cap) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et (Dynamic cap)) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\ value_has_type et needle /\
  eval_operand needleop s = SOME (typed_val_to_w256 et needle) /\
  eval_operand (vv_operand vv) s = SOME baseword /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. needleop = Var z \/ vv_operand vv = Var z ==> not_fresh_at sm z) /\
  cap < dimword (:256) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path T execctx fn s 0 (OK t) /\
      alloca_history fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      t.vs_current_bb = ct.cs_current_bb /\
      t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
      vv_post ctx func cenv cx e es sa sm s0 es' (Value (ArrayV av)) vv t /\
      eval_operand needleop t = SOME (typed_val_to_w256 et needle) /\
      eval_operand (vv_operand vv) t = SOME baseword /\
      eval_operand out t = SOME (bool_to_word
        (if is_in then evaluate_in_array (ArrayTV et (Dynamic cap)) needle av
         else ~evaluate_in_array (ArrayTV et (Dynamic cap)) needle av))
Proof
  strip_tac >>
  `read_result cx (Value (ArrayV av)) es' = (INL (ArrayV av), es')` by
    simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all (Q.INST [`memory` |-> `T`, `tv` |-> `Value (ArrayV av)`]
               rest_word_dynamic_tail) >>
  disch_then (qspec_then `execctx` strip_assume_tac) >>
  drule_all rest_word_marked_allocation_posts >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

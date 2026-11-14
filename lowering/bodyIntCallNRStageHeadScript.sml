(* Deterministic heads of the interleaved argument traversal. *)
Theory bodyIntCallNRStageHead
Ancestors
  bodyIntCallNRStageFragments bodyIntCallNRStageStores
  bodyIntCallFamCallIntStageInterface bodyIntCallForcingReadOnly
  exprLoweringProps loweringPosts

Theorem intcall_stage_current_head_stack:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce fp.jc_cx ty r vv es s /\
  read_result fp.jc_cx r es = (INL v,es) /\ is_word_type ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  fn_has_code sa sb fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    eval_operand op u = SOME (typed_val_to_w256 tv v) /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  `vv_holds ce fp.jc_cx ty (Value v) vv es s` by
    (irule vv_holds_materialise >> goal_assum (drule_at Any) >> simp[]) >>
  `sa.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sa`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  drule_all intcall_stage_expr_word_force >> strip_tac >>
  qexists_tac `u` >> gvs[expr_val_rel_def] >> metis_tac[]
QED

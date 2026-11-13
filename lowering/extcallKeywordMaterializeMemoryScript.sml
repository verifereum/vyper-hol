(* A nonword default's immediate source read and concrete materializer. *)
Theory extcallKeywordMaterializeMemory
Ancestors
  extcallMaterializeMemory extcallLoweredCaptureMemory
  exprSimMemDefs stmtReasonVvMemory exprSimUnwrapProps exprSimMemorySource
  exprSimProps loweringPosts exprSimHypsDefs exprSimDefs exprLowering
  valueTypingMemoryProps gasSummary fragGasMode vyperState compileEnv

Theorem extcall_vv_bound_lowered_value[local]:
  vv_store_bound cx ty lt ee raw vv s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) lt = SOME tv /\ val_wf tv v ==>
  vv_store_bound cx lt lt ee (Value v) vv s
Proof
  strip_tac >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  fs[vv_store_bound_def] >>
  simp[vv_store_bound_def, read_result_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  `type_memory_size tv = 0 \/
   w2n w + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >>
  decide_tac
QED

Theorem extcall_default_keyword_read_mem:
  compile_materialize_vv ce (lowered_value_type ce e) vv sm = (op,sb) /\
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ptv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type ltv v) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
  type_memory_size ltv < dimword (:256) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tag p. vv = LocatedValue tag p ==>
    (p.ptr_location <> LocMemory \/ is_word_type tag ==> tag = lowered_value_type ce e) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))) ==>
  ?v z w. gas_marked_exec T (ctx,func) (read_result cx raw)
      (ee,s) [] (INL v) ee (OK z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand op z = SOME w /\
    w2n w + type_memory_size ltv <= z.vs_alloca_next /\
    expr_val_rel cx (lowered_value_type ce e) v op z /\ expr_store_bound cx (lowered_value_type ce e) v op z /\
    stmt_state_rel ctx func ce cx ee z /\ alloca_history func z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid b sz off len. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sm.cs_next_id /\ b <= off /\ off + len <= b + sz ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name b sz off len. local_region ce ee.scopes s name b sz /\
      b <= off /\ off + len <= b + sz ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name io itv iv off len. ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) /\
      io <= off /\ off + len <= io + type_memory_size itv ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule vv_post_read_ok >> strip_tac >>
  `value_has_type ltv v /\ val_wf ltv v` by
    metis_tac[value_has_type_memory_wf] >>
  drule_all vv_post_read_result >> strip_tac >>
  `vv_holds ce cx (post_value_type ce e) (Value v) vv ee s /\
   vv_storage_live cx vv ee s /\ stmt_state_rel ctx func ce cx ee s` by
    gvs[vv_post_def] >>
  `!tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory ==>
    post_value_type ce e = lowered_value_type ce e` by
    (rpt strip_tac >> gvs[vv_holds_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
   ~is_word_type (post_value_type ce e)` by simp[] >>
  `vv_holds ce cx (lowered_value_type ce e) (Value v) vv ee s` by
    (drule_all extcall_nonword_lowered_holds >> simp[]) >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e)
    ee (Value v) vv s` by
    (drule_all extcall_vv_bound_lowered_value >> simp[]) >>
  drule_all extcall_materialize_vv_mem >> strip_tac >>
  `gas_marked_exec T (ctx,func) (read_result cx raw)
    (ee,s) [] (INL v) ee (OK z)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     drule read_result_gas_obs >> simp[]) >>
  qexistsl_tac [`v`, `z`, `w`] >> simp[] >>
  fs[arithmeticTheory.ADD_COMM] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

(* Common actual endpoint for argument unwrap. *)
Theory bodyIntCallStageUnwrap
Ancestors bodyIntCallStageUnwrapCopy bodyIntCallStageHead bodyIntCallStageCompile

Theorem intcall_stage_unwrap:
  unwrap_value ce vv sa = (op,sn) /\ vv_type vv = ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sn func /\ local_ptrs_reserved ce sa /\
  expr_sim_inv ce cx env es /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,vv)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v w z. gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ eval_operand op z = SOME w /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) z.vs_memory) /\
    stmt_state_rel ctx func ce cx es z /\
    intcall_held_args ce cx a sn es z H /\ wb_frame ce es sa s z /\
    ~z.vs_halted /\ z.vs_current_bb = sn.cs_current_bb /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
      aid NOTIN FDOM z.vs_allocas)
Proof
  strip_tac >> Cases_on `vv`
  >- (irule bodyIntCallStageUnwrapReadTheory.intcall_stage_unwrap_readonly >> metis_tac[]) >>
  rename1 `LocatedValue sty p` >>
  Cases_on `is_word_type sty \/ p.ptr_location = LocMemory`
  >- (irule bodyIntCallStageUnwrapReadTheory.intcall_stage_unwrap_readonly >> metis_tac[]) >>
  gvs[contextTheory.vv_type_def] >> Cases_on `p.ptr_location`
  >- gvs[]
  >- (drule intcall_stage_unwrap_storage >> simp[] >>
      disch_then (qspec_then `sty` mp_tac) >> simp[] >>
      disch_then irule >> metis_tac[])
  >- (drule intcall_stage_unwrap_storage >> simp[] >>
      disch_then (qspec_then `sty` mp_tac) >> simp[] >>
      disch_then irule >> metis_tac[])
  >- (drule_all intcall_stage_unwrap_code >> simp[]) >>
  gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def,
      loweringPostsTheory.vv_holds_def]
QED

Theorem intcall_stage_unwrap_compiler:
  unwrap_value ce vv sa = (op,sn) /\ local_ptrs_reserved ce sa /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
  local_ptrs_reserved ce sn /\ (!x. op = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >> conj_tac
  >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
      qexists_tac `sa` >> simp[] >>
      mp_tac (Q.SPECL [`ce`,`vv`,`sa`] exprLoweringPropsTheory.ci_mono_unwrap_value) >>
      simp[exprLoweringPropsTheory.ci_mono_def]) >>
  rpt strip_tac >> irule exprOperandVarTheory.compiler_unwrap_value_var >>
  qexistsl_tac [`ce`,`op`,`sa`,`vv`] >> simp[] >> Cases_on `vv` >>
  gvs[contextTheory.vv_operand_def]
QED

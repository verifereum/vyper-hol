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

Theorem intcall_stage_memory_head:
  unwrap_value ce vv sa = (op,sm) /\ vv_type vv = ty /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sn) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword(:256) /\
  (!aid. sa.cs_next_id <= aid ==> aid NOTIN FDOM s.vs_allocas) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm si func /\ fn_has_code si sn func /\
  local_ptrs_reserved ce sa /\ expr_sim_inv ce cx env es /\
  fn_directly_calls ctx func.fn_name name /\ MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,vv)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v w t inst lb.
    gas_marked_path F ctx func s 0 (OK t) /\
    read_result cx raw es = (INL v,es) /\
    value_has_type tv v /\ val_wf tv v /\
    eval_operand buf.buf_operand t = SOME w /\ w2n w = lb /\
    val_in_memory tv v lb t.vs_memory /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sa s t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    local_ptrs_reserved ce sn /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x t = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
      aid NOTIN FDOM t.vs_allocas) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sn.cs_next_id /\
    FLOOKUP t.vs_allocas sm.cs_next_id =
      SOME (lb,MAX 32 (type_memory_bytes ce ty)) /\
    type_memory_size tv <= MAX 32 (type_memory_bytes ce ty) /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint lb (MAX 32 (type_memory_bytes ce ty)) b sz)
Proof
  strip_tac >>
  `sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`vv`,`sa`] exprLoweringPropsTheory.ci_mono_unwrap_value) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `sa.cs_next_id NOTIN FDOM s.vs_allocas /\ sm.cs_next_id NOTIN FDOM s.vs_allocas` by simp[] >>
  drule_all intcall_stage_unwrap >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def] >>
  drule_all intcall_stage_unwrap_compiler >> strip_tac >>
  `sm.cs_next_id NOTIN FDOM z.vs_allocas` by simp[] >>
  `MAX 32 (type_memory_bytes ce ty) < dimword(:256)` by
    simp[arithmeticTheory.MAX_LT,wordsTheory.dimword_def] >>
  drule_all bodyIntCallStageHeadTheory.intcall_stage_alloc_store_map >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `si.cs_next_var <= sn.cs_next_var /\ si.cs_next_id <= sn.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`,`op`,`buf.buf_operand`,`ty`,`ty`,`si`]
      exprLoweringPropsTheory.ci_mono_compile_store_memory) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `wb_frame ce es sa s t` by suspend "frame" >>
  `z.vs_alloca_next < dimword(:256)` by
    (gvs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     metis_tac[exprLoweringPropsTheory.alloca_room_next_lt]) >>
  qexistsl_tac [`v`,`n2w z.vs_alloca_next`,`t`,`inst`,`z.vs_alloca_next`] >>
  simp[] >> rpt conj_tac
  >- suspend "path"
  >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
      qexists_tac `sm` >> simp[] >> decide_tac)
  >- metis_tac[freshWritesTheory.not_fresh_at_mono]
  >- (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono])
  >> metis_tac[]
QED

Resume intcall_stage_memory_head[frame]:
  irule exprSimConvertBytesTheory.convert_wb_frame_trans >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume intcall_stage_memory_head[path]:
  metis_tac[fragGasModeTheory.gas_marked_path_then,arithmeticTheory.ADD_CLAUSES]
QED
Finalise intcall_stage_memory_head

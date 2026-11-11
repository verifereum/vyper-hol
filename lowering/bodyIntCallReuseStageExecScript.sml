(* Reuse-safe argument staging execution interfaces. *)
Theory bodyIntCallReuseStageExec
Ancestors
  bodyIntCallReuseStorageExec bodyIntCallReuseCodeExec bodyIntCallReuseStoreExec
  bodyIntCallStageUnwrap bodyIntCallStageOwned bodyIntCallStageUnwrapRead
  bodyIntCallHeldArgs

Theorem intcall_reuse_unwrap:
  unwrap_value ce vv sa = (op,sn) /\ vv_type vv = ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty < dimword(:256) /\
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
      FLOOKUP z.vs_allocas aid = SOME entry)
Proof
  strip_tac >> Cases_on `vv`
  >- (drule intcall_stage_unwrap_readonly >> simp[] >>
      disch_then drule_all >> strip_tac >>
      qexistsl_tac [`v`,`w`,`t'`] >> simp[]) >>
  rename1 `LocatedValue sty p` >>
  Cases_on `is_word_type sty \/ p.ptr_location = LocMemory`
  >- (`p.ptr_location = LocMemory \/ is_word_type sty` by metis_tac[] >>
      drule intcall_stage_unwrap_readonly >> simp[] >>
      disch_then drule_all >> strip_tac >>
      qexistsl_tac [`v`,`w`,`t`] >> simp[]) >>
  gvs[contextTheory.vv_type_def] >> Cases_on `p.ptr_location`
  >- gvs[]
  >- (drule intcall_reuse_unwrap_storage >> simp[] >>
      disch_then (qspec_then `sty` mp_tac) >> simp[] >>
      disch_then irule >> metis_tac[])
  >- (drule intcall_reuse_unwrap_storage >> simp[] >>
      disch_then (qspec_then `sty` mp_tac) >> simp[] >>
      disch_then irule >> metis_tac[])
  >- (drule_all intcall_reuse_unwrap_code >> simp[]) >>
  gvs[intcall_held_args_def,loweringPostsTheory.vv_holds_def]
QED

Theorem intcall_reuse_word_owned:
  unwrap_value ce vv sa = (op,sn) /\ vv_type vv = ty /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty < dimword(:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sn func /\ local_ptrs_reserved ce sa /\
  expr_sim_inv ce cx env es /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,vv)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v w z. gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ eval_operand op z = SOME w /\
    staged_arg ce func es sa sn z (ty,tv,v,T,op) /\
    value_has_type tv v /\ val_wf tv v /\ w = typed_val_to_w256 tv v /\
    stmt_state_rel ctx func ce cx es z /\ local_ptrs_reserved ce sn /\
    intcall_held_args ce cx a sn es z H /\ wb_frame ce es sa s z /\
    ~z.vs_halted /\ z.vs_current_bb = sn.cs_current_bb /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry)
Proof
  strip_tac >> drule_all intcall_reuse_unwrap >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def] >>
  drule_all intcall_stage_unwrap_compiler >> strip_tac >>
  qexistsl_tac [`v`,`w`,`z`] >> simp[staged_arg_def] >> gvs[]
QED

Theorem intcall_reuse_memory_owned:
  unwrap_value ce vv sa = (op,sm) /\ vv_type vv = ty /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sn) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword(:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm si func /\ fn_has_code si sn func /\
  local_ptrs_reserved ce sa /\ expr_sim_inv ce cx env es /\
  fn_directly_calls ctx func.fn_name name /\ MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,vv)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v t. gas_marked_path F ctx func s 0 (OK t) /\
    read_result cx raw es = (INL v,es) /\
    staged_arg ce func es sa sn t (ty,tv,v,F,buf.buf_operand) /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sa s t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\ local_ptrs_reserved ce sn /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x t = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >> drule_all intcall_reuse_unwrap >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def] >>
  drule_all intcall_stage_unwrap_compiler >> strip_tac >>
  `MAX 32 (type_memory_bytes ce ty) < dimword(:256)` by
    simp[arithmeticTheory.MAX_LT,wordsTheory.dimword_def] >>
  drule_all intcall_reuse_alloc_store >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`vv`,`sa`] exprLoweringPropsTheory.ci_mono_unwrap_value) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `si.cs_next_var <= sn.cs_next_var /\ si.cs_next_id <= sn.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`,`op`,`buf.buf_operand`,`ty`,`ty`,`si`]
      exprLoweringPropsTheory.ci_mono_compile_store_memory) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  qexistsl_tac [`v`,`t`] >> simp[] >> suspend "finish"
QED
Resume intcall_reuse_memory_owned[finish]:
  conj_tac >- metis_tac[fragGasModeTheory.gas_marked_path_then,arithmeticTheory.ADD_0] >>
  conj_tac >- suspend "descriptor" >>
  conj_tac >- (irule exprSimConvertBytesTheory.convert_wb_frame_trans >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
    qexists_tac `sm` >> simp[] >> decide_tac) >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
Resume intcall_reuse_memory_owned[descriptor]:
  `b < dimword(:256)` by
    (`alloca_inv t /\ alloca_room ctx func t` by
       fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     drule exprLoweringPropsTheory.alloca_room_next_lt >> strip_tac >>
     fs[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sn x` by
    (simp[] >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `si` >> simp[]) >>
  `!n lo sz. local_region ce es.scopes t n lo sz ==>
    regions_disjoint b (MAX 32 (type_memory_bytes ce ty)) lo sz` by
    metis_tac[staged_buffer_local_disjoint] >>
  simp[staged_arg_def] >> qexists_tac `n2w b` >> simp[] >>
  conj_tac >- (qpat_x_assum `eval_operand buf.buf_operand t = _` mp_tac >> simp[]) >>
  qexistsl_tac [`sm.cs_next_id`,`b`,`MAX 32 (type_memory_bytes ce ty)`] >>
  simp[] >> metis_tac[]
QED
Finalise intcall_reuse_memory_owned

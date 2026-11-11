(* Return storage is separate from every later staged memory argument. *)
Theory bodyIntCallStageReturn
Ancestors
  bodyIntCallStageEndpoint bodyIntCallStageAllocation bodyIntCallStageOwned
  allocaSiteResource venomState loweringHalt
  exprSimConvertBytes loweringPosts venomMemDefs compileEnv

Theorem staged_arg_old_allocation_disjoint:
  staged_arg ce func es a sm t (ty,tv,v,F,op) /\
  alloca_inv t /\ rid < a.cs_next_id /\
  FLOOKUP t.vs_allocas rid = SOME (rb,cap) /\
  eval_operand op t = SOME w /\ rsz <= cap ==>
  compileEnv$regions_disjoint rb rsz (w2n w) (type_memory_size tv)
Proof
  simp[staged_arg_def] >> strip_tac >>
  `rid <> aid` by decide_tac >>
  gvs[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def,
      compileEnvTheory.regions_disjoint_def] >>
  first_x_assum (drule_at Any) >>
  disch_then (qspec_then `inst.inst_id` mp_tac) >> simp[] >> decide_tac
QED

Theorem staged_return_frame:
  wb_frame ce es sm s t /\ not_fresh_at sm x /\
  eval_operand (Var x) s = SOME w /\
  FLOOKUP s.vs_allocas rid = SOME (rb,cap) /\
  alloca_inv t /\ rsz <= cap ==>
  eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_allocas rid = SOME (rb,cap) /\
  rb + rsz <= t.vs_alloca_next
Proof
  simp[wb_frame_def, venomStateTheory.eval_operand_def] >> strip_tac >>
  `FLOOKUP t.vs_allocas rid = SOME (rb,cap)` by metis_tac[] >>
  drule_all alloca_site_registered_below >> strip_tac >>
  simp[]
QED

Theorem intcall_stage_return_endpoint:
  compile_alloc_buffer nb sm = (buf,si) /\ fn_has_code sm si func /\
  compile_stage_intcall_args ce (MAP (\(ty,raw,vv). vv) H) flags
    (MAP (\(ty,raw,vv). ty) H) si = (ops,sn) /\
  LENGTH flags = LENGTH H /\
  EVERY (\(ty,raw,vv). vv_type vv = ty /\
    type_memory_bytes ce ty < dimword(:256) /\
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
         type_memory_bytes ce ty = type_memory_size tv) H /\
  LIST_REL (\(ty,raw,vv) flag. flag ==> is_word_type ty) H flags /\
  intcall_held_args ce cx a sm es s H /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code si sn func /\ local_ptrs_reserved ce sm /\
  expr_sim_inv ce cx env es /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ nb < dimword(:256) /\ rsz <= nb /\
  (!aid. sm.cs_next_id <= aid ==> aid NOTIN FDOM s.vs_allocas) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t D inst.
    gas_marked_path F ctx func s 0 (OK t) /\
    EVERY (staged_arg ce func es si sn t) D /\
    MAP (\(ty,tv,v,flag,op). op) D = ops /\
    LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
      ty' = ty /\ flag' = flag /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      read_result cx raw es = (INL v,es)) (ZIP(H,flags)) D /\
    stmt_state_rel ctx func ce cx es t /\ wb_frame ce es sm s t /\
    local_ptrs_reserved ce sn /\
    (!aid. sn.cs_next_id <= aid ==> aid NOTIN FDOM t.vs_allocas) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (s.vs_alloca_next,buf.buf_size) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\ sm.cs_next_id < si.cs_next_id /\
    s.vs_alloca_next + rsz <= t.vs_alloca_next /\
    (!ty tv v op w. MEM (ty,tv,v,F,op) D /\
       eval_operand op t = SOME w ==>
       compileEnv$regions_disjoint s.vs_alloca_next rsz
         (w2n w) (type_memory_size tv))
Proof
  strip_tac >>
  `sm.cs_next_id NOTIN FDOM s.vs_allocas` by simp[] >>
  drule_all intcall_stage_allocation >> strip_tac >>
  `!aid. si.cs_next_id <= aid ==> aid NOTIN FDOM u.vs_allocas` by
    (rpt strip_tac >>
     `sm.cs_next_id <= aid /\ aid <> sm.cs_next_id` by gvs[] >>
     `aid NOTIN FDOM s.vs_allocas` by simp[] >>
     qpat_x_assum `u = _ with vs_inst_idx := _`
       (fn th => gvs[th, venomStateTheory.update_var_def,
                     finite_mapTheory.FDOM_FUPDATE])) >>
  drule_all intcall_stage_args_endpoint >> strip_tac >>
  `alloca_inv t` by gvs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `eval_operand buf.buf_operand t = SOME (n2w s.vs_alloca_next) /\
   FLOOKUP t.vs_allocas sm.cs_next_id = SOME (s.vs_alloca_next,nb) /\
   s.vs_alloca_next + rsz <= t.vs_alloca_next` by
    (qpat_assum `wb_frame ce es si u t`
       (mp_then Any mp_tac staged_return_frame) >>
     disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     disch_then (qspecl_then [`x`,`n2w s.vs_alloca_next`,`rsz`] mp_tac) >>
     gvs[]) >>
  `wb_frame ce es sm s t` by
    (irule convert_wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`es`,`u`,`si`] >> simp[]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`t`,`D`,`inst`] >> simp[] >> conj_tac
  >- metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0] >>
  rpt strip_tac >>
  `staged_arg ce func es si sn t (ty,tv,v,F,op)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule staged_arg_old_allocation_disjoint >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[]
QED

(* Return allocation followed by separated staging, at one actual endpoint. *)
Theory bodyIntCallStageDistinctReturn
Ancestors
  bodyIntCallStageDistinctEndpoint bodyIntCallStageReturn bodyIntCallStageAllocation
  bodyIntCallReuseAllocation bodyIntCallReuseHeldFrame
  bodyIntCallStageOwned allocaSiteResource venomState loweringHalt
  exprSimConvertBytes loweringPosts venomMemDefs compileEnv

Theorem intcall_stage_return_distinct_endpoint:
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
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t D inst b.
    gas_marked_path F ctx func s 0 (OK t) /\
    EVERY (staged_arg ce func es si sn t) D /\
    MAP (\(ty,tv,v,flag,op). op) D = ops /\
    LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
      ty' = ty /\ flag' = flag /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      read_result cx raw es = (INL v,es)) (ZIP(H,flags)) D /\
    stmt_state_rel ctx func ce cx es t /\ wb_frame ce es sm s t /\
    local_ptrs_reserved ce sn /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,buf.buf_size) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\ sm.cs_next_id < si.cs_next_id /\
    b + rsz <= t.vs_alloca_next /\
    (!ty tv v op w. MEM (ty,tv,v,F,op) D /\
       eval_operand op t = SOME w ==>
       compileEnv$regions_disjoint b rsz
         (w2n w) (type_memory_size tv)) /\
    (!i j. i < LENGTH D /\ j < LENGTH D /\ i <> j ==>
      (\(ty,tv,v,flag,op) (ty',tv',v',flag',op').
        ~flag /\ ~flag' ==>
        !w w'. eval_operand op t = SOME w /\ eval_operand op' t = SOME w' ==>
        compileEnv$regions_disjoint (w2n w) (type_memory_size tv)
          (w2n w') (type_memory_size tv')) (EL i D) (EL j D))
Proof
  strip_tac >>
  drule_all intcall_reuse_allocation >> strip_tac >>
  `wb_frame ce es sm s u /\ intcall_held_args ce cx a si es u H` by
    (irule intcall_held_outside_write_frame >> simp[] >>
     `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
      contract_storage u = contract_storage s /\
      contract_transient u = contract_transient s` by
       (qpat_x_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
        simp[venomStateTheory.venom_state_component_equality,
          venomStateTheory.contract_storage_def,venomStateTheory.contract_transient_def]) >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`b`,`nb`] >> simp[] >>
         `!n lo sz. local_region ce es.scopes u n lo sz <=>
            local_region ce es.scopes s n lo sz` by
           (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
            qexists_tac `sm` >> simp[]) >>
         gvs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
     conj_tac >- (drule compile_alloc_buffer_parts >> simp[]) >>
     qexists_tac `func` >>
     gvs[exprLoweringPropsTheory.stmt_state_rel_def,state_rel_def]) >>
  drule_all intcall_stage_args_distinct_endpoint >> strip_tac >>
  `alloca_inv t` by gvs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `eval_operand buf.buf_operand t = SOME (n2w b) /\
   FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,nb) /\
   b + rsz <= t.vs_alloca_next` by
    (qpat_assum `wb_frame ce es si u t`
       (mp_then Any mp_tac staged_return_frame) >>
     disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     disch_then (qspecl_then [`x`,`n2w b`,`rsz`] mp_tac) >>
     gvs[]) >>
  `wb_frame ce es sm s t` by
    (irule convert_wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`es`,`u`,`si`] >> simp[]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`t`,`D`,
    `mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [x]`,`b`] >>
  simp[venomInstTheory.mk_inst_def] >> conj_tac
  >- metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0] >>
  rpt strip_tac >>
  `staged_arg ce func es si sn t (ty,tv,v,F,op)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule staged_arg_old_allocation_disjoint >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[]
QED

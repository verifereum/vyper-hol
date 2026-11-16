Theory bodyFullAbiEncodeWordStage
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeStore bodyFullPathHistory
  bodyPtrMakeArrayWordStore wordArgsPtr exprSimHash exprSimWordArgs
  bodyFullAllocaFresh bodyFullUnwrapRun exprSimAlloc
  abiBuiltinAllocation emitHelper emitHelperProps exprLoweringProps loweringHalt fragExec
  fragGasOriginPtrLoop compileEnv
  bodyPtrDefs loweringStateRelDefs ptrDiscipline venomMemDefs
  venomExecSemantics venomState venomInst finite_map pred_set

Theorem abi_encode_word_stage_origin:
  compile_alloc_buffer 32 sm = (buf,sn) /\
  emit_void MSTORE [buf.buf_operand;op] sn = ((),sh) /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce sm /\ cs_extends origin sm /\
  stmt_state_rel (H0 : (bool # bytes32 # type_value) list # num list)
    ctx func ce cx ee s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand op s = SOME w /\ op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel (Hentry : (bool # bytes32 # type_value) list # num list)
    ctx func ce cx es s0 /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ wb_frame ce es ee origin s0 s /\
  ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
  ?q b u Gu tnu.
    buf.buf_operand = Var q /\ not_fresh_at sh q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
    u.vs_inst_idx = LENGTH sh.cs_current_insts /\
    eval_operand (Var q) u = SOME (n2w b) /\ ptr_covers Gu tnu q u 32 /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,32) /\
    b+32 < dimword(:256) /\ b+32 <= u.vs_alloca_next /\
    (!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==> mem_word_at b mem = w) /\
    alloca_history func u /\ allocas_from lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!H : (bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx func ce cx ee s ==> stmt_state_rel H ctx func ce cx ee u) /\
    (!H : (bool # bytes32 # type_value) list # num list. !D.
      stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at D lo ret ce cx ee G tn s ==>
      ghost_inv_at D lo ret ce cx ee Gu tnu u) /\
    ghost_kept_at lo ce es origin G0 tn0 s0 Gu tnu /\
    wb_frame ce es ee origin s0 u /\
    (pure_frame ce func es origin s0 s ==> pure_frame ce func es origin s0 u) /\
    (!x. not_fresh_at sm x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `cs_extends sm sn` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sn sh` by
    (irule cs_extends_same_block >>
     drule emit_void_extends >>
     simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sh func` by
    metis_tac[fn_has_code_split] >>
  `32 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  drule_all (INST_TYPE [beta |-> ``:256``] abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`, `explicit`, `PG`, `G`] strip_assume_tac) >>
  `t.vs_labels = s.vs_labels /\ t.vs_halted = s.vs_halted` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = s`
      (SUBST1_TAC o SYM) >> simp[]) >>
  rename1 `lookup_var q t = SOME a` >>
  `eval_operand op t = SOME w /\ op_taint tn' op = {}` by
    (Cases_on `op` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `sh.cs_current_bb = sn.cs_current_bb /\
   sh.cs_current_insts = sn.cs_current_insts ++
     [mk_inst sn.cs_next_id MSTORE [buf.buf_operand;op] []] /\
   sh.cs_blocks = sn.cs_blocks` by
    (qpat_assum `emit_void _ _ sn = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
       emit_def, comp_return_def]) >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst sn.cs_next_id MSTORE [Var q;op] [])` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND,
      get_instruction_def, listTheory.EL_APPEND_EQN]) >>
  qabbrev_tac `u = (mstore (w2n a) w t) with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `tnu = step_taint (mk_inst sn.cs_next_id MSTORE [Var q;op] [])
    t (mstore (w2n a) w t) tn'` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G',tn') [] (OK u,G',tnu)` by
    (gen_tac >> simp[NoAsms, Abbr `u`, Abbr `tnu`] >>
     irule abi_encode_mstore_origin_path >> goal_assum (drule_at Any) >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def,
       codegenRelTheory.fixed_source_write_range_def, eval_operand_def] >>
     gvs[mk_inst_def] >> decide_tac) >>
  qexistsl_tac [`q`, `w2n a`, `u`, `G'`, `tnu`] >>
  simp[] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "endpoint" >>
  suspend "resources"
QED

Resume abi_encode_word_stage_origin[fresh]:
  `sh.cs_next_var = sn.cs_next_var` by
    (qpat_assum `emit_void _ _ sn = _` mp_tac >>
     simp[NoAsms, emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[]) >>
  fs[not_fresh_at_def]
QED

Resume abi_encode_word_stage_origin[path]:
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G'`, `t`, `tn'`] >> simp[]
QED

Resume abi_encode_word_stage_origin[endpoint]:
  simp[Abbr `u`, mstore_def]
QED

Resume abi_encode_word_stage_origin[resources]:
  `tnu.t_var = tn'.t_var /\ tnu.t_stor = tn'.t_stor /\
   tnu.t_trans = tn'.t_trans /\
   tnu.t_mem = tn'.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    (drule_all wordLoadStorePtrTheory.mstore_ghost_frame >>
     disch_then (qspecl_then [`ARB`, `G'`, `sn.cs_next_id`] mp_tac) >>
     simp[Abbr `tnu`]) >>
  `(!x. lookup_var x u = lookup_var x t) /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_current_bb = sn.cs_current_bb /\
   u.vs_inst_idx = LENGTH sn.cs_current_insts + 1` by
    simp[Abbr `u`, mstore_def, lookup_var_def] >>
  `ptr_covers G' tnu q u 32` by
    (fs[ptr_covers_def] >> metis_tac[op_taint_def]) >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  simp[eval_operand_def] >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "history" >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "wb" >>
  suspend "pure"
QED

Resume abi_encode_word_stage_origin[robust]:
  rpt strip_tac >> irule mstore_raw_robust_word >>
  goal_assum (drule_at (Pat `lookup_var _ _ = _`)) >>
  qexistsl_tac [`sn.cs_next_id`, `tn'`, `tnu`, `op`] >>
  fs[Abbr `u`, Abbr `tnu`]
QED

Resume abi_encode_word_stage_origin[history]:
  `stmt_state_rel H0 ctx func ce cx ee t` by metis_tac[] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,_,_) _ _`
    (qspec_then `ARB` mp_tac) >>
  disch_then (mp_then Any mp_tac body_full_path_alloca_history) >> simp[]
QED

Resume abi_encode_word_stage_origin[state]:
  rpt strip_tac >>
  `stmt_state_rel H ctx func ce cx ee t` by metis_tac[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  simp[Abbr `u`, stmt_state_rel_inst_idx] >>
  irule literal_mstore_state_rel >>
  simp[] >>
  qexistsl_tac [`w2n a`,
    `mk_inst sm.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sm.cs_next_var)]`,
    `32`] >>
  simp[mk_inst_def] >> fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume abi_encode_word_stage_origin[ghost]:
  rpt strip_tac >>
  `ghost_inv_at D lo ret ce cx ee G' tn' t` by
    (irule alloc_buffer_ghost_inv_at >>
     rpt (first_assum (irule_at Any)) >> simp[] >>
     FAIL_TAC "return pointer reservation diagnostic") >>
  FAIL_TAC "store ghost"
QED

Resume abi_encode_word_stage_origin[kept]:
  FAIL_TAC "kept"
QED

Resume abi_encode_word_stage_origin[wb]:
  FAIL_TAC "wb"
QED

Resume abi_encode_word_stage_origin[pure]:
  FAIL_TAC "pure"
QED

Finalise abi_encode_word_stage_origin

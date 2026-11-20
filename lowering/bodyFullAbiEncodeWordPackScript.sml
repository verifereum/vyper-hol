Theory bodyFullAbiEncodeWordPack
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeFinish bodyFullAbiEncodeCopy exprSimAbiEncodeStagedObserver
  exprSimAbiEncodeStateTransport exprSimAbiEncodeOblivious
  abiBuiltinEncodeCode abiEncoderAppend loweringHalt exprSimHash
  emitHelper emitHelperProps exprLoweringProps localPtrsProps freshWrites
  fragExec compileEnv venomState venomExecSemantics venomInst finite_map words arithmetic
  pred_set list rich_list ptrDiscipline bodyPtrDefs loweringStateRelDefs loweringPosts
  bodyFullHashKeccakFixed typedCopyOriginPtrBase

Theorem abi_encode_word_pack_origin:
  lower_abi_encode F mid (Var src) (AbiCopy 32) 32 st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ local_ptrs_reserved ce origin /\ cs_extends origin st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  source_id < st.cs_next_id /\ FLOOKUP s.vs_allocas source_id = SOME (sb,32) /\
  eval_operand (Var src) s = SOME (n2w sb) /\ ptr_covers G tn src s 32 /\
  not_fresh_at st src /\ abi_encoder_admissible (AbiCopy 32) /\
  LENGTH (enc at av) = 32 /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiCopy 32) at av sb 32 mem) /\
  stmt_state_rel (Hentry:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ wb_frame ce es ee origin s0 s /\
  ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
  ?p q t Gt tnt.
    out = Var q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tnt)) /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    eval_operand out t = SOME (n2w p) /\
    ptr_covers Gt tnt q t (32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) /\
    FLOOKUP t.vs_allocas st.cs_next_id =
      SOME (p,(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4)))) /\
    p+(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword(:256) /\
    (!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      mem_word_at p mem = n2w (32+(case mid of NONE => 0 | SOME _ => 4)) /\
      mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4)) 32 mem = enc at av /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)) /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s ==>
      abi_encode_staged_observation H ctx func ce cx ee st out mid
        (32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) p at av s t) /\
    (!H D. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
      ghost_inv_at D lo ret ce cx ee G tn s ==> ghost_inv_at D lo ret ce cx ee Gt tnt t) /\
    ghost_kept_at lo ce es origin G0 tn0 s0 Gt tnt /\ wb_frame ce es ee origin s0 t /\
    (pure_frame ce func es origin s0 s ==> pure_frame ce func es origin s0 t)
Proof
  strip_tac >> pure_rewrite_tac [LET_THM] >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_trace >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ st = (buf,allocated)` >>
  `cs_extends st allocated /\ cs_extends allocated address_st /\
   cs_extends address_st ready /\ cs_extends ready body_end /\ cs_extends body_end final` by
    ((conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     conj_tac >- metis_tac[emit_op_extends, same_blocks_def, cs_extends_same_block, IS_PREFIX_APPEND] >>
     conj_tac >- (Cases_on `mid`
       >- gvs[abi_builtin_encode_method_id_def, comp_return_def, cs_extends_refl] >>
       qpat_x_assum `abi_builtin_encode_method_id _ _ _ = _` mp_tac >>
       simp[NoAsms, abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
         emit_def] >> strip_tac >> gvs[] >>
       simp[cs_extends_def, IS_PREFIX_APPEND]) >>
     conj_tac >- metis_tac[compile_abi_encode_to_buf_extends] >>
     qpat_x_assum `abi_builtin_encode_finish _ _ _ _ = _` mp_tac >>
     simp[NoAsms, abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >> IF_CASES_TAC >> strip_tac >> gvs[] >>
     simp[cs_extends_def, IS_PREFIX_APPEND] >> (gvs[compile_alloc_buffer_extends, emit_op_extends, same_blocks_def, cs_extends_same_block, IS_PREFIX_APPEND, abi_builtin_encode_method_id_def, comp_return_def, cs_extends_refl, NoAsms, comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def, cs_extends_def, compile_abi_encode_to_buf_extends, abi_builtin_encode_finish_def]))) >>
  `fn_has_code st allocated func /\ fn_has_code allocated ready func /\
   fn_has_code ready body_end func /\ fn_has_code body_end final func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `32 * word_size ((case mid of NONE => 0 | SOME _ => 4) + 32) + 32 < dimword(:256)` by
    (Cases_on `mid` >> simp[wordsTheory.dimword_def] >> EVAL_TAC) >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `lookup_var q allocated_s = SOME w` >>
  rename1 `ptr_covers Ga ta q allocated_s _` >>
  `~allocated_s.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `_ with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _;
      vs_inst_idx := _ |> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H0 ctx func ce cx ee allocated_s` by
    (qpat_assum `!H'. stmt_state_rel H' ctx func ce cx ee s ==> _`
      (qspec_then `H0` mp_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp allocated_s` by
    (qpat_assum `stmt_state_rel H0 ctx func ce cx ee allocated_s`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `alloca_inv allocated_s` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `lo <= w2n w` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `lookup_var q allocated_s = SOME (n2w (w2n w))` by simp[] >>
  gvs[] >>
  drule_at (Pat `emit_op ADD _ _ = _`) (SRULE [ADD_COMM] (Q.INST [`maxlen` |-> `32`] abi_encode_setup_tail_origin)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_method_id _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `alloca_inv _`)) >> simp[] >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`w2n w`,`explicit`,`ctx`,`PG`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `ptr_covers Gready tready dp ready_s 32` >>
  `st.cs_next_var <= allocated.cs_next_var /\ st.cs_next_id <= allocated.cs_next_id` by
    (mp_tac (Q.SPECL [`32 * word_size ((case (mid:bytes32 option) of NONE => 0 | SOME _ => 4) + 32) + 32`, `st`]
      ci_mono_compile_alloc_buffer) >> simp[ci_mono_def]) >>
  `not_fresh_at allocated src` by metis_tac[not_fresh_at_mono] >>
  `lookup_var src allocated_s = lookup_var src s /\
   FLOOKUP Ga src = FLOOKUP G src /\ op_taint ta (Var src) = op_taint tn (Var src)` by
    (qpat_x_assum `!x. not_fresh_at st x ==> _` drule >> simp[]) >>
  `ptr_covers Ga ta src allocated_s 32` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `ptr_covers Gready tready src ready_s 32` by
    (qpat_x_assum `!x n. not_fresh_at allocated x /\ _ ==> _` irule >> simp[]) >>
  `eval_operand (Var src) ready_s = SOME (n2w sb)` by
    (qpat_assum `!op. _ ==> eval_operand op ready_s = _ /\ _` (qspec_then `Var src` mp_tac) >>
     simp[eval_operand_def] >> gvs[eval_operand_def]) >>
  `sb+32 <= s.vs_alloca_next` by
    (`alloca_inv s` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
     fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `regions_disjoint (w2n w)
      (32 * word_size ((case mid of NONE => 0 | SOME _ => 4)+32)+32) sb 32` by
    (qpat_assum `!aid b len. aid < st.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `source_id` >> simp[]) >>
  `!mem. mem_agree_outside tready.t_mem ready_s.vs_memory mem ==>
     abi_encoder_window_input (AbiCopy 32) at av sb 32 mem` by
    suspend "robust_input" >>
  suspend "tail"
QED

Resume abi_encode_word_pack_origin[robust_input]:
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_bytes_at sb 32 mem = enc at av` by
    (rpt strip_tac >>
     qpat_x_assum `!mem. _ ==> abi_encoder_window_input _ _ _ _ _ _` drule >>
     simp[Once abiEncoderWindowTheory.abi_encoder_window_input_cases] >>
     rpt strip_tac >> gvs[]) >>
  drule representationCleanPtrTheory.robust_mem_bytes_at_clean >> strip_tac >>
  `allocated_s.vs_memory = s.vs_memory` by
    (qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _; vs_allocas := _;
       vs_alloca_next := _|> = s` mp_tac >> simp[venom_state_component_equality]) >>
  `!i. sb <= i /\ i < sb+32 ==> i NOTIN tready.t_mem` by
    (rpt strip_tac >>
     `i NOTIN tn.t_mem` by metis_tac[] >>
     `i NOTIN ta.t_mem` by
       (qpat_assum `!i. i IN ta.t_mem <=> _` (qspec_then `i` mp_tac) >>
        gvs[] >> decide_tac) >> gvs[]) >>
  `mem_bytes_at sb 32 ready_s.vs_memory = mem_bytes_at sb 32 s.vs_memory` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
          typedMemoryCopyTheory.typed_copy_frame_def] >> strip_tac >>
     first_x_assum irule >>
     fs[regions_disjoint_def] >> Cases_on `mid` >> gvs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  rpt strip_tac >>
  irule abiEncoderWindowTheory.abi_encoder_window_input_bytewise >>
  qexists_tac `s.vs_memory` >> reverse conj_tac
  >- (qpat_assum `!mem. _ ==> abi_encoder_window_input _ _ _ _ _ _` irule >>
      simp[mem_agree_outside_def]) >>
  rpt strip_tac >>
  `mem_bytes_at a 1 ready_s.vs_memory = mem_bytes_at a 1 mem` by
    (fs[mem_agree_outside_def] >> metis_tac[]) >>
  drule_all representationCleanPtrTheory.mem_bytes_at_eq_byte >> simp[]
QED

Resume abi_encode_word_pack_origin[tail]:
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (Cases_on `mid` >> gvs[]) >>
  `local_ptrs_reserved ce ready /\
   (!x. not_fresh_at origin x ==> not_fresh_at ready x) /\
   (!x. not_fresh_at st x ==> not_fresh_at ready x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono, LESS_EQ_TRANS] >>
  `emit_void MCOPY [data_ptr;Var src;Lit 32w] ready = ((),body_end) /\ len = Lit 32w` by
    (qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     simp[abiEncoderTheory.compile_abi_encode_child_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> gvs[]) >>
  `local_ptrs_rel func ce ee.scopes allocated_s /\ alloca_room ctx func allocated_s` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
      stateRelProjTheory.stmt_state_rel_alloca_room] >>
  `!name b sz. local_region ce ee.scopes allocated_s name b sz ==>
      regions_disjoint (w2n w + 32) (case mid of NONE => 0 | SOME _ => 32) b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region ce ee.scopes allocated_s name b len ==> _` drule >>
     Cases_on `mid` >> simp[regions_disjoint_def, vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `local_ptrs_rel func ce ee.scopes ready_s /\ alloca_room ctx func ready_s` by
    (conj_tac
     >- (qpat_x_assum `!ce es. local_ptrs_rel _ _ _ allocated_s /\ _ ==> _` irule >>
         simp[] >> fs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]) >>
     metis_tac[alloca_room_fields]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    fs[wb_frame_def, locals_kept_def] >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==> b+sz <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s name b sz` by
       metis_tac[wordArgsPtrTheory.wb_frame_local_regions] >>
     metis_tac[bodyMemoryDefsTheory.body_local_region_frontier]) >>
  `!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < origin.cs_next_id ==>
     b+sz <= s.vs_alloca_next` by
    (`alloca_inv s0` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
     fs[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 Ga ta` by
    (irule bodyFullAllocaFreshTheory.alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G`,`w2n w + (32 * word_size ((case mid of NONE => 0 | SOME _ => 4)+32)+32)`,`s`,`tn`] >>
     simp[] >> metis_tac[not_fresh_at_mono]) >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 Gready tready` by
    (qpat_x_assum `!ce es origin G0 tn0 s0. ghost_kept_at _ _ _ _ _ _ _ Ga ta /\ _ ==> _` irule >>
     simp[] >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `ghost_kept_at lo ce ee origin G0 tn0 s0 Gready tready` by
    (`!name b sz. local_region ce es.scopes s0 name b sz <=>
       local_region ce ee.scopes s0 name b sz` by
       simp[tupleMemoryFrameTheory.local_region_scopes_domain] >>
     qpat_assum `ghost_kept_at lo ce es origin G0 tn0 s0 Gready tready` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> asm_rewrite_tac[]) >>
  qabbrev_tac `k = case mid of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `N = 32 * word_size (k+32) + 32` >>
  qmatch_asmsub_abbrev_tac `eval_operand data_ptr ready_s = SOME (n2w d)` >>
  `d+32 <= w2n w+N` by
    (simp[Abbr `d`, Abbr `N`, Abbr `k`] >>
     Cases_on `mid` >> EVAL_TAC >> decide_tac) >>
  `d < dimword (:256) /\ d+32 <= ready_s.vs_alloca_next /\
   sb+32 <= ready_s.vs_alloca_next` by decide_tac >>
  qpat_x_assum `data_ptr = Var dp` SUBST_ALL_TAC >>
  `lookup_var dp ready_s = SOME (n2w d) /\ lookup_var src ready_s = SOME (n2w sb)` by
    (conj_tac
     >- qpat_assum `eval_operand (Var dp) ready_s = SOME (n2w d)`
          (ACCEPT_TAC o REWRITE_RULE [eval_operand_def]) >>
     qpat_assum `eval_operand (Var src) ready_s = SOME (n2w sb)`
       (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
  `ready_s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt] >>
  `sb < dimword (:256)` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ready_s` by
    (qpat_assum `typed_copy_state_frame _ _ _ allocated_s ready_s`
      (rewrite_tac o single o MATCH_MP typed_copy_state_frame_allocas_below_fmp) >>
     first_assum ACCEPT_TAC) >>
  drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst ready.cs_next_id MCOPY [Var dp; Var src; Lit 32w] []` >>
  qabbrev_tac `u = mcopy d sb 32 ready_s` >>
  qabbrev_tac `copied = u with vs_inst_idx := SUC ready_s.vs_inst_idx` >>
  qabbrev_tac `tc = step_taint i ready_s u tready` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (ready_s,Gready,tready) [] (OK copied,Gready,tc)` by suspend "copy_path" >>
  suspend "copy_effect"
QED

Resume abi_encode_word_pack_origin[copy_path]:
  gen_tac >>
  `w2n (n2w d:256 word) = d /\ w2n (n2w sb:256 word) = sb` by simp[] >>
  simp[NoAsms, Abbr `i`, Abbr `u`, Abbr `copied`, Abbr `tc`] >>
  `w2n (32w:256 word) = 32` by simp[] >>
  qpat_assum `w2n (n2w d:256 word) = d` (fn hd =>
    qpat_assum `w2n (n2w sb:256 word) = sb` (fn hs =>
      qpat_assum `w2n (32w:256 word) = 32` (fn hn =>
        irule (GEN_ALL (PURE_REWRITE_RULE [hd, hs, hn]
          (Q.INST [`a` |-> `n2w sb`, `b` |-> `n2w d`, `n` |-> `32w`]
            (SPEC_ALL abi_encode_mcopy_origin_path))))))) >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def,
    codegenRelTheory.fixed_source_write_range_def,
    codegenRelTheory.sized_source_write_range_def,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def, eval_operand_def,
    op_taint_def, ADD_COMM] >>
  qexists_tac `bb` >> simp[mk_inst_def] >> gvs[]
QED

Resume abi_encode_word_pack_origin[copy_effect]:
  `typed_copy_state_frame ready d 32 ready_s copied` by
    simp[NoAsms, Abbr `copied`, Abbr `u`, typedMemoryCopyTheory.typed_copy_mcopy_state_frame] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp copied` by
    (qpat_assum `typed_copy_state_frame ready d 32 ready_s copied`
      (rewrite_tac o single o MATCH_MP typed_copy_state_frame_allocas_below_fmp) >>
     first_assum ACCEPT_TAC) >>
  `~copied.vs_halted /\ copied.vs_current_bb = body_end.cs_current_bb /\
   copied.vs_inst_idx = LENGTH body_end.cs_current_insts /\
   copied.vs_allocas = ready_s.vs_allocas /\ copied.vs_alloca_next = ready_s.vs_alloca_next /\
   (!x. lookup_var x copied = lookup_var x ready_s)` by
    simp[Abbr `copied`, Abbr `u`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  `allocas_from lo copied /\ alloca_inv copied` by
    (conj_tac
     >- (pure_rewrite_tac[allocas_from_def] >>
         qpat_assum `copied.vs_allocas = ready_s.vs_allocas` SUBST1_TAC >>
         qpat_assum `allocas_from lo ready_s`
           (ACCEPT_TAC o PURE_REWRITE_RULE [allocas_from_def])) >>
     irule localPtrsPropsTheory.alloca_inv_fields >>
     qexists_tac `ready_s` >> simp[]) >>
  `tc.t_var = tready.t_var /\ tc.t_stor = tready.t_stor /\
   tc.t_trans = tready.t_trans /\ tc.t_imm = tready.t_imm /\
   tc.t_mem = (tready.t_mem DIFF {j | d <= j /\ j < d+32}) UNION
      {d+j | j < 32 /\ sb+j IN tready.t_mem}` by suspend "copy_taint" >>
  `lookup_var q copied = SOME (n2w (w2n w)) /\ ptr_covers Gready tc q copied N` by
    (conj_tac
     >- simp[GSYM eval_operand_def] >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`Gready`,`ready_s`,`tready`] >>
     `op_taint tc (Var q) = op_taint tready (Var q)` by
       (qpat_assum `tc.t_var = tready.t_var`
         (fn th => simp[NoAsms, op_taint_def, th])) >>
     simp[]) >>
  `not_fresh_at body_end q` by suspend "finish_fresh" >>
  suspend "finish"
QED

Resume abi_encode_word_pack_origin[copy_taint]:
  `eval_operand (Lit 32w) ready_s = SOME 32w` by simp[eval_operand_def] >>
  qpat_assum `eval_operand (Var dp) ready_s = SOME (n2w d)`
    (mp_then Any mp_tac fragExecPtrTheory.mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand (Var src) ready_s = SOME (n2w sb)`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit 32w) ready_s = SOME 32w`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`ARB`,`Gready`,`tready`,`ready.cs_next_id`] mp_tac) >>
  simp[Abbr `tc`, Abbr `i`, Abbr `u`] >>
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Resume abi_encode_word_pack_origin[finish_fresh]:
  qpat_assum `emit_void MCOPY _ ready = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  `allocated.cs_next_var <= ready.cs_next_var` by
    (qpat_assum `compile_alloc_buffer N st = _`
       (mp_then Any mp_tac abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
     disch_then (strip_assume_tac o CONJUNCT2) >>
     qpat_assum `emit_op ALLOCA _ st = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     Cases_on `mid` >> simp[]) >>
  irule not_fresh_at_mono >> qexists_tac `allocated` >> simp[]
QED

Resume abi_encode_word_pack_origin[finish]:
  qmatch_asmsub_abbrev_tac `lo <= p` >>
  `p+32 <= copied.vs_alloca_next /\ p < dimword(:256)` by
    (fs[Abbr `d`] >> decide_tac) >>
  `32 <= N` by simp[Abbr `N`] >>
  `ptr_covers Gready tc q copied 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `N` >> simp[]) >>
  `32+k < dimword(:256)` by (Cases_on `mid` >> simp[Abbr `k`, dimword_def]) >>
  qpat_assum `len = Lit 32w` SUBST_ALL_TAC >>
  drule_at (Pat `abi_builtin_encode_finish _ _ _ _ = _`)
    (Q.INST [`len` |-> `32`] abi_encode_finish_origin) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`func`,`explicit`,`ctx`,`PG`] mp_tac) >>
  impl_tac >- simp[eval_operand_def, op_taint_def] >>
  strip_tac >>
  qmatch_asmsub_rename_tac `typed_copy_state_frame body_end p 32 copied t` >>
  qmatch_asmsub_rename_tac `tnt.t_mem = tc.t_mem DIFF _` >>
  qmatch_asmsub_rename_tac `ptr_covers Gfinal tnt q t 32` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gfinal,tnt)` by
    (gen_tac >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gready`,`copied`,`tc`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gready`,`ready_s`,`tready`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Ga`,`allocated_s`,`ta`] >> simp[]) >>
  `ptr_covers Gfinal tnt q t N` by
    (qpat_assum `!x n. not_fresh_at body_end x /\ _ ==> _` irule >> simp[]) >>
  `alloca_history func copied` by
    (`step_inst_base i ready_s = OK u` by
       simp[Abbr `i`, Abbr `u`, stmtReasonMemoryTheory.step_mcopy_eq, eval_operand_def] >>
     `lookup_block ready_s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb ready_s.vs_inst_idx = SOME i` by metis_tac[] >>
     drule_all allocaHistoryTheory.alloca_history_base_step >>
     simp[Abbr `i`, Abbr `copied`, mk_inst_def, is_terminator_def]) >>
  suspend "output_resources"
QED

Resume abi_encode_word_pack_origin[output_resources]:
  `p+32 <= d` by simp[Abbr `d`] >>
  `!mem. mem_agree_outside tready.t_mem ready_s.vs_memory mem ==>
      mem_bytes_at sb 32 mem = enc at av` by
    (qx_gen_tac `mem` >> disch_tac >>
     qpat_assum `!mem. mem_agree_outside tready.t_mem ready_s.vs_memory mem ==> _`
       (qspec_then `mem` mp_tac) >>
     qpat_assum `mem_agree_outside tready.t_mem ready_s.vs_memory mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowTheory.abi_encoder_window_copy_iff, SF CONJ_ss]) >>
  `mem_bytes_at sb 32 ready_s.vs_memory = enc at av` by
    (qpat_assum `!mem. _ ==> mem_bytes_at sb 32 mem = _`
       (qspec_then `ready_s.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
  `mem_bytes_at d 32 copied.vs_memory = enc at av` by
    simp[Abbr `copied`, Abbr `u`, valueEncodingPropsTheory.mcopy_mem_bytes_at_same] >>
  `!a n. a+n <= p \/ p+32 <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n copied.vs_memory` by
    (qpat_assum `typed_copy_state_frame body_end p 32 copied t`
       (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
          typedMemoryCopyTheory.typed_copy_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `mem_bytes_at d 32 t.vs_memory = enc at av` by
    (qpat_assum `!a n. _ ==> _ = mem_bytes_at a n copied.vs_memory`
       (qspecl_then [`d`,`32`] mp_tac) >> simp[]) >>
  `tc.t_mem = tready.t_mem DIFF {j | d <= j /\ j < d+32}` by suspend "copy_clean" >>
  `!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      mem_bytes_at d 32 mem = enc at av` by suspend "payload_clean" >>
  `(case mid of NONE => T | SOME selector =>
     !mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
       mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)` by
    suspend "selector_window" >>
  suspend "protected"
QED

Resume abi_encode_word_pack_origin[copy_clean]:
  `!j. sb <= j /\ j < sb+32 ==> j NOTIN tready.t_mem` by
    (qpat_assum `!mem. mem_agree_outside tready.t_mem ready_s.vs_memory mem ==>
       mem_bytes_at sb 32 mem = _`
       (ACCEPT_TAC o MATCH_MP representationCleanPtrTheory.robust_mem_bytes_at_clean)) >>
  `!j. j < 32 ==> sb+j NOTIN tready.t_mem` by
    (qx_gen_tac `off` >> disch_tac >>
     qpat_assum `!i. sb <= i /\ i < sb+32 ==> i NOTIN tready.t_mem`
       (qspec_then `sb+off` irule) >> decide_tac) >>
  `{d+j | j < 32 /\ sb+j IN tready.t_mem} = {}` by
    (qpat_assum `!j. j < 32 ==> sb+j NOTIN tready.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EXTENSION, GSPECIFICATION, SF CONJ_ss]) >>
  qpat_assum `tc.t_mem = _ UNION _` SUBST1_TAC >> simp[]
QED

Resume abi_encode_word_pack_origin[payload_clean]:
  `!j. d <= j /\ j < d+32 ==> j NOTIN tnt.t_mem` by
    (qx_gen_tac `j` >> strip_tac >>
     qpat_assum `tnt.t_mem = _` SUBST1_TAC >>
     qpat_assum `tc.t_mem = _ DIFF _` SUBST1_TAC >>
     simp[IN_DIFF]) >>
  rpt strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 mem` by
    (irule logStoreDataOriginPtrTheory.mem_agree_outside_window >>
     qexists_tac `tnt.t_mem` >> simp[]) >> simp[]
  >> (metis_tac[])
QED

Resume abi_encode_word_pack_origin[selector_window]:
  namedCases_on `mid` ["", "selector"] >- simp[] >>
  `p+36 <= d` by fs[Abbr `d`, Abbr `k`] >>
  `mem_word_at (p+32) ready_s.vs_memory = selector << 224` by
    (qpat_assum `(case SOME selector of NONE => T | SOME _ => _)`
       (qspec_then `ready_s.vs_memory` mp_tac o SRULE []) >>
     simp[mem_agree_outside_def]) >>
  `mem_bytes_at (p+32) 4 ready_s.vs_memory =
      abi_builtin_encode_method_bytes selector` by
    metis_tac[mload_def, valueEncodingDefsTheory.mem_word_at_def,
      abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_window] >>
  `mem_bytes_at (p+32) 4 copied.vs_memory = mem_bytes_at (p+32) 4 ready_s.vs_memory` by
    (qpat_assum `typed_copy_state_frame ready d 32 ready_s copied`
      (mp_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def]) >>
     strip_tac >> first_x_assum (qspecl_then [`p+32`,`4`] mp_tac) >> simp[]) >>
  `mem_bytes_at (p+32) 4 t.vs_memory = mem_bytes_at (p+32) 4 copied.vs_memory` by
    (qpat_assum `!a n. _ ==> _ = mem_bytes_at a n copied.vs_memory`
       (qspecl_then [`p+32`,`4`] mp_tac) >> simp[]) >>
  `!j. p+32 <= j /\ j < p+36 ==> j NOTIN tnt.t_mem` by
    (qx_gen_tac `j` >> strip_tac >>
     qpat_assum `tnt.t_mem = _` SUBST1_TAC >>
     qpat_assum `tc.t_mem = _ DIFF _` SUBST1_TAC >>
     qpat_assum `tready.t_mem = _` SUBST1_TAC >>
     simp[IN_DIFF] >> decide_tac) >>
  simp[NoAsms] >> rpt strip_tac >>
  `mem_bytes_at (p+32) 4 t.vs_memory = mem_bytes_at (p+32) 4 mem` by
    (irule logStoreDataOriginPtrTheory.mem_agree_outside_window >>
     qexists_tac `tnt.t_mem` >> simp[]) >>
  metis_tac[]
QED

Resume abi_encode_word_pack_origin[protected]:
  `p+32+(case mid of NONE => 0 | SOME _ => 32) <= p+N` by
    (Cases_on `mid` >> simp[Abbr `N`, Abbr `k`, vfmConstantsTheory.word_size_def]) >>
  `typed_copy_state_frame allocated p N allocated_s ready_s` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`p+32`,`case mid of NONE => 0 | SOME _ => 32`] >> simp[]) >>
  `ci_mono allocated ready /\ ci_mono allocated body_end` by suspend "frame_fresh" >>
  `typed_copy_state_frame allocated p N ready_s copied` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`d`,`32`] >> simp[] >>
     irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
     qexists_tac `ready` >> simp[ci_mono_def]) >>
  `typed_copy_state_frame allocated p N copied t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`p`,`32`] >> simp[] >>
     irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
     qexists_tac `body_end` >> simp[ci_mono_def]) >>
  `typed_copy_state_frame allocated p N allocated_s t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
     qexists_tac `copied` >> simp[] >>
     irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
     qexists_tac `ready_s` >> simp[]) >>
  suspend "frame_posts"
QED

Resume abi_encode_word_pack_origin[frame_fresh]:
  qpat_assum `compile_alloc_buffer N st = _`
    (mp_then Any mp_tac abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  qpat_assum `emit_op ALLOCA _ st = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_void MCOPY _ ready = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  `cs_extends allocated ready /\ cs_extends allocated body_end` by
    metis_tac[cs_extends_trans] >>
  Cases_on `mid` >> simp[ci_mono_def]
QED

Resume abi_encode_word_pack_origin[frame_posts]:
  qpat_assum `typed_copy_state_frame allocated p N allocated_s t`
    (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def]) >>
  `copy_static t = copy_static allocated_s` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|> = allocated_s` (SUBST1_TAC o SYM) >>
     simp[exprSimStorageCopyTheory.copy_static_def]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [q]) (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer N st = _`
       (mp_then Any strip_assume_tac abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
     qpat_assum `emit_op ALLOCA _ st = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `q = STRING #"%" (toString st.cs_next_var)` by gvs[] >>
     qpat_assum `compile_alloc_buffer N st = _`
       (mp_then Any mp_tac exprSimAllocTheory.buffer_alloc_code) >> simp[]) >>
  `!H. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s ==>
       stmt_state_rel H ctx func ce cx ee t` by
    (qx_gen_tac `H` >> disch_tac >>
     `stmt_state_rel H ctx func ce cx ee allocated_s` by
       (qpat_assum `!H'. stmt_state_rel H' ctx func ce cx ee s ==> _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     irule bodyPtrMakeArrayCopyStateFrameTheory.literal_copy_window_stmt_state_rel >>
     qexistsl_tac [`st.cs_next_id`, `p`, `N`, `q`, `st`, `allocated`, `allocated_s`] >>
     simp[] >> rpt strip_tac >>> NTH_GOAL (metis_tac[not_fresh_at_mono]) 1 >>> NTH_GOAL (simp[not_fresh_at_mono]) 2 >>> NTH_GOAL (simp[not_fresh_at_mono]) 2 >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  suspend "assemble_posts"
QED

Resume abi_encode_word_pack_origin[assemble_posts]:
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gfinal x = FLOOKUP G x /\ op_taint tnt (Var x) = op_taint tn (Var x)` by
    suspend "old_vars" >>
  `allocated_s.vs_memory = s.vs_memory` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_inst_idx := _; vs_allocas := _;
         vs_alloca_next := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!a n. a+n <= p \/ p+N <= a ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    (qpat_assum `!a n. _ ==> _ = mem_bytes_at a n allocated_s.vs_memory` mp_tac >> simp[]) >>
  `!name b sz. local_region ce ee.scopes s name b sz ==>
    regions_disjoint p N b sz` by suspend "local_sep" >>
  `!name b sz. local_region ce ee.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> qpat_assum `!a n. _ ==> _ = mem_bytes_at a n s.vs_memory` irule >>
     qpat_assum `!name b sz. local_region ce ee.scopes s name b sz ==> regions_disjoint p N b sz`
       drule >> simp[regions_disjoint_def, DISJ_COMM]) >>
  `!aid b sz. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> qpat_assum `!a n. _ ==> _ = mem_bytes_at a n s.vs_memory` irule >>
     qpat_assum `!aid b len. aid < st.cs_next_id /\ _ ==> regions_disjoint p N b len`
       (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> simp[regions_disjoint_def]) >>
  `pure_frame ce func ee st s t` by
    (pure_rewrite_tac[pure_frame_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!a n. _ ==> _ = mem_bytes_at a n s.vs_memory` irule >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz`
       (qspecl_then [`mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [q]`, `p`, `N`] mp_tac) >>
     simp[mk_inst_def, regions_disjoint_def, DISJ_COMM]) >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,N) /\
   p+N <= t.vs_alloca_next /\ t.vs_alloca_next < dimword(:256) /\
   s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\ allocas_from lo t` by
    (simp[] >> pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `allocas_from lo copied` (mp_tac o PURE_REWRITE_RULE [allocas_from_def]) >>
     asm_rewrite_tac[]) >>
  `!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
     mem_word_at p mem = n2w (k+32) /\ mem_bytes_at d 32 mem = enc at av /\
     (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)` by
    (qx_gen_tac `mem` >> disch_tac >> conj_tac
     >- (qpat_assum `!mem. _ ==> mem_word_at p mem = _` (qspec_then `mem` mp_tac) >>
         simp[ADD_COMM]) >>
     conj_tac >- (qpat_assum `!mem. _ ==> mem_bytes_at d 32 mem = _` irule >> simp[]) >>
     namedCases_on `mid` ["", "sel"] >- simp[] >>
     qpat_assum `(case SOME sel of NONE => T | SOME selector =>
         !mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==> _)`
       (qspec_then `mem` mp_tac o SRULE []) >> simp[]) >>
  qexistsl_tac [`p`,`t`,`Gfinal`,`tnt`] >>
  qpat_assum `Abbrev (d = p + (k + 32))`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "return_posts"
QED

Resume abi_encode_word_pack_origin[old_vars]:
  `!x. not_fresh_at st x ==> not_fresh_at allocated x /\ not_fresh_at body_end x` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  qx_gen_tac `x` >> disch_tac >>
  qpat_assum `!x. not_fresh_at st x ==> not_fresh_at allocated x /\ _`
    (qspec_then `x` (drule_then strip_assume_tac)) >>
  qpat_assum `!x. not_fresh_at body_end x ==> lookup_var x t = _ /\ _`
    (qspec_then `x` (drule_then strip_assume_tac)) >>
  qpat_assum `!op. _ ==> eval_operand op ready_s = _ /\ _`
    (qspec_then `Var x` (drule_then strip_assume_tac o
       SRULE [eval_operand_def, op_prov_def])) >>
  qpat_assum `!x. not_fresh_at st x ==> lookup_var x allocated_s = _ /\ _`
    (qspec_then `x` (drule_then strip_assume_tac)) >>
  `op_taint tc (Var x) = op_taint tready (Var x)` by
    (qpat_assum `tc.t_var = tready.t_var`
       (fn th => simp[NoAsms, op_taint_def, th])) >>
  asm_rewrite_tac[]
QED

Resume abi_encode_word_pack_origin[local_sep]:
  rpt strip_tac >>
  qpat_assum `!name b len. local_region ce ee.scopes allocated_s name b len ==> regions_disjoint p N b len` irule >>
  qexists_tac `name` >>
  irule exprSimPropsTheory.local_region_frame_fwd >>
  qexistsl_tac [`s`,`st`,`ee.scopes`] >> simp[]
QED

Resume abi_encode_word_pack_origin[return_posts]:
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
       FLOOKUP t.vs_allocas aid = SOME row` by
    (qpat_assum `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> _`
       mp_tac >> simp[]) >>
  `t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_requests = s.vs_requests /\ t.vs_data_section = s.vs_data_section /\
   t.vs_immutables = s.vs_immutables /\
   abi_encode_semantic_obs t = abi_encode_semantic_obs s` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_inst_idx := _;
         vs_allocas := _; vs_alloca_next := _|> = s` (SUBST1_TAC o SYM) >>
     qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
         vs_current_bb := _; vs_inst_idx := _|> = allocated_s` (SUBST1_TAC o SYM) >>
     simp[exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def]) >>
  conj_tac >- suspend "staged_observation" >>
  suspend "remaining_frames"
QED

Resume abi_encode_word_pack_origin[staged_observation]:
  `p+32+k = d` by
    (qpat_assum `Abbrev (d = _)`
       (SUBST1_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `mem_agree_outside tnt.t_mem t.vs_memory t.vs_memory` by
    simp[mem_agree_outside_def] >>
  qpat_assum `!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
       mem_word_at p mem = _ /\ _`
    (qspec_then `t.vs_memory` (drule_then strip_assume_tac)) >>
  qx_gen_tac `H` >> disch_tac >>
  pure_rewrite_tac [abi_encode_staged_observation_def] >>
  qpat_assum `Abbrev (k = _)`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  conj_tac
  >- (qpat_assum `!H. stmt_state_rel H ctx func ce cx ee s ==>
          stmt_state_rel H ctx func ce cx ee t` irule >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `allocated_s.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _`
        (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!aid b sz. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
        irule >> first_assum (irule_at Any) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `p+32+k = d` SUBST1_TAC >> asm_rewrite_tac[]) >>
  (simp[])
QED

Resume abi_encode_word_pack_origin[remaining_frames]:
  (* The three writes only remove taint from the allocation's taint set. *)
  `tnt.t_mem SUBSET tready.t_mem /\ tnt.t_mem SUBSET ta.t_mem` by
    (qpat_assum `tnt.t_mem = tc.t_mem DIFF _` SUBST1_TAC >>
     qpat_assum `tc.t_mem = tready.t_mem DIFF _` SUBST1_TAC >>
     qpat_assum `tready.t_mem = ta.t_mem DIFF _` SUBST1_TAC >>
     simp[SUBSET_DEF, IN_DIFF]) >>
  `!j. j < s.vs_alloca_next /\ j IN tnt.t_mem ==> j IN tn.t_mem` by
    (rpt strip_tac >>
     `j IN ta.t_mem` by metis_tac[SUBSET_DEF] >>
     qpat_assum `!j. j IN ta.t_mem <=> _` (qspec_then `j` mp_tac) >> simp[]) >>
  conj_tac
  >- suspend "ghost_window" >>
  conj_tac
  >- (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
      qexistsl_tac [`Gready`,`tready`] >> simp[] >> qx_gen_tac `x` >> disch_tac >>
      `not_fresh_at st x` by
        (irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
      `not_fresh_at body_end x` by
        (irule not_fresh_at_mono >> qexists_tac `allocated` >>
         qpat_assum `ci_mono allocated body_end` (strip_assume_tac o SRULE [ci_mono_def]) >>
         simp[] >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
      qpat_assum `!x. not_fresh_at body_end x ==> lookup_var x t = _ /\ _`
        (drule_then strip_assume_tac) >>
      `op_taint tc (Var x) = op_taint tready (Var x)` by
        simp[op_taint_def] >> simp[]) >>
  conj_tac
  >- (irule wb_frame_allocating_tail >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl_tac [`s`,`ee.scopes`,`st`] >> simp[] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >> irule exprSimPropsTheory.pure_frame_trans >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ee`,`st`,`s`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `wb_frame ce es ee origin s0 s`
    (mp_then Any irule exprSimWordArgsTheory.wb_frame_vars) >> simp[]
QED

Resume abi_encode_word_pack_origin[ghost_window]:
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func ce ee.scopes s` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `stor_taint_ok_at D tnt t` by
    (qpat_assum `ghost_inv_at D lo ret ce cx ee G tn s`
       (mp_then Any mp_tac (cj 4 (iffLR ghost_inv_at_def))) >>
     simp[stor_taint_ok_at_def]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!a n. _ ==> _ = mem_bytes_at a n s.vs_memory`
       (qspecl_then [`0`,`lo`] irule) >> simp[]) >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w` by
    (qx_gen_tac `x` >> gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  `!x. not_fresh_at st x ==> FLOOKUP Gfinal x = FLOOKUP G x /\
      op_taint tnt (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> asm_rewrite_tac[]) >>
  `!name b len. local_region ce ee.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tnt.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!name b sz. local_region ce ee.scopes s name b sz ==> _ = _`
           irule >> goal_assum (drule_at Any)) >>
     qx_gen_tac `addr` >> strip_tac >>
     drule_all bodyMemoryDefsTheory.body_local_region_frontier >> strip_tac >>
     qpat_assum `!j. j < s.vs_alloca_next /\ j IN tnt.t_mem ==> _`
       (qspec_then `addr` irule) >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `!i. i < lo /\ i IN tnt.t_mem ==> i IN tn.t_mem` by
    (qx_gen_tac `addr` >> strip_tac >>
     qpat_assum `!j. j < s.vs_alloca_next /\ j IN tnt.t_mem ==> _`
       (qspec_then `addr` irule) >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  irule bodyPtrBytestringBuiltinsWindowGhostTheory.ghost_inv_at_local_window_transport >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`ee`,`func`,`s`,`st`,`tn`] >>
  simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_word_pack_origin

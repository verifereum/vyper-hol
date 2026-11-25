Theory bodyAbiEncodeWordPackEffectsMods
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeFinish bodyFullAbiEncodeCopy
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  typedCopyOriginPtrBase[qualified,ignore_grammar]
  exprSimProps bodyFullAllocaFresh
  abiBuiltinAllocation entryDecodeStructure reasonCopySourcePtr decoderGhostFramePtr
  typedMemoryCopy valueEncodingProofs allocaHistory wordArgsPtr bodyMemoryDefs tupleMemoryFrame
  bodyFullUnwrapRun bodyPtrMakeArrayCopyStateFrame bodyPtrMakeArrayPrimitiveInstall
  stateRelProj exprSimStorageCopy exprSimAlloc venomMemDefs exprSimWordArgs
  abiBuiltinEncodeCode abiBuiltinEncodeMethod abiEncoderAppend abiEncoderMemory loweringHalt exprSimHash
  emitHelper emitHelperProps exprLoweringProps localPtrsProps freshWrites
  fragGasOriginPtrLoop fragExec compileEnv venomState venomExecSemantics venomInst finite_map words arithmetic
  pred_set list rich_list ptrDiscipline bodyPtrDefs loweringStateRelDefs loweringPosts

(* The output windows and frame facts refer to the same path endpoint. *)
Theorem abi_encode_word_pack_effects_mods:
  lower_abi_encode mid 32
    (\dst. comp_ignore_bind (emit_void MSTORE [dst;value]) (comp_return (Lit 32w)))
    st = (out,final) /\
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
  eval_operand value s = SOME word /\ op_taint tn value = {} /\
  (!x. value = Var x ==> not_fresh_at st x) /\
  enc at av = word_to_bytes word T /\ LENGTH (enc at av) = 32 /\
  stmt_state_rel (Hentry:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ wb_frame ce es ee origin s0 s /\
  ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
  let k = case mid of NONE => 0 | SOME _ => 4 in
  let N = 32 + 32 * word_size (32+k) in
  ?p q t Gt tnt.
    out = Var q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tnt)) /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    eval_operand out t = SOME (n2w p) /\ ptr_covers Gt tnt q t N /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,N) /\
    p+N <= t.vs_alloca_next /\ t.vs_alloca_next < dimword(:256) /\
    (!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      mem_word_at p mem = n2w (32+k) /\
      mem_bytes_at (p+32+k) 32 mem = enc at av /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)) /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s ==>
      stmt_state_rel H ctx func ce cx ee t) /\
    (!name b n. local_region ce ee.scopes t name b n ==> p+N <= b \/ b+n <= p) /\
    st.cs_next_id < final.cs_next_id /\
    ghost_kept_at lo ce es origin G0 tn0 s0 Gt tnt /\ wb_frame ce es ee origin s0 t /\
    (pure_frame ce func es origin s0 s ==> pure_frame ce func es origin s0 t) /\
    pure_frame ce func ee st s t /\
    (!a n. a+n <= p \/ p+N <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!name b n. local_region ce ee.scopes s name b n ==> regions_disjoint p N b n) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
    (!aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tnt (Var x) = op_taint tn (Var x)) /\
    (!j. j < s.vs_alloca_next /\ j IN tnt.t_mem ==> j IN tn.t_mem) /\
    t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    tnt.t_stor = tn.t_stor /\ tnt.t_trans = tn.t_trans /\ tnt.t_imm = tn.t_imm
Proof
  strip_tac >> pure_rewrite_tac [LET_THM] >>
  drule lower_abi_encode_trace >> BETA_TAC >> strip_tac >>
  drule abi_builtin_encode_setup_trace >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ st = (buf,allocated)` >>
  `emit_void MSTORE [data_ptr;value] ready = ((),body_end) /\ len = Lit 32w` by
    (qpat_x_assum `comp_ignore_bind _ _ _ = _` mp_tac >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >> pairarg_tac >> gvs[]) >>
  `ci_mono allocated method_st` by
    metis_tac[ci_mono_abi_builtin_encode_method_id, pairTheory.SND] >>
  `cs_extends allocated method_st` by fs[ci_mono_def] >>
  `cs_extends st allocated /\ cs_extends method_st ready /\
   cs_extends ready body_end /\ cs_extends body_end final` by
    (drule abi_builtin_encode_finish_shape >> strip_tac >>
     metis_tac[compile_alloc_buffer_extends, ci_mono_emit_op, ci_mono_emit_void,
       ci_mono_def, cs_extends_same_block, inst_extends_def, pairTheory.SND]) >>
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
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
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
  rename1 `ptr_covers Gready tready dp ready_s _` >>
  suspend "setup_inputs"
QED

Resume abi_encode_word_pack_effects_mods[setup_inputs]:
  `ptr_covers Gready tready dp ready_s 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qpat_assum `ptr_covers Gready tready dp ready_s _` (irule_at Any) >>
     Cases_on `mid` >> EVAL_TAC) >>
  `st.cs_next_var <= allocated.cs_next_var /\ st.cs_next_id <= allocated.cs_next_id` by
    (mp_tac (Q.SPECL [`32 * word_size ((case (mid:bytes32 option) of NONE => 0 | SOME _ => 4) + 32) + 32`, `st`]
      ci_mono_compile_alloc_buffer) >> simp[ci_mono_def]) >>
  `eval_operand value allocated_s = SOME word /\ op_taint ta value = {}` by
    (Cases_on `value`
     >- (qpat_assum `eval_operand (Lit _) s = _` mp_tac >>
         simp[NoAsms, eval_operand_def, op_taint_def])
     >- (rename1 `eval_operand (Var v) s = _` >>
         `not_fresh_at st v` by metis_tac[] >>
         qpat_assum `!x. not_fresh_at st x ==> lookup_var x allocated_s = _ /\ _`
           (qspec_then `v` (drule_then strip_assume_tac)) >>
         asm_rewrite_tac[eval_operand_def] >>
         qpat_assum `eval_operand (Var v) s = _` (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
     qpat_assum `eval_operand (Label _) s = _` mp_tac >>
     qpat_assum `allocated_s with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|> = s` (SUBST1_TAC o SYM) >>
     simp[NoAsms, eval_operand_def, op_taint_def]) >>
  `eval_operand value ready_s = SOME word /\ op_taint tready value = {}` by
    (qpat_assum `!op. _ ==> eval_operand op ready_s = _ /\ _`
       (qspec_then `value` mp_tac) >>
     impl_tac >- metis_tac[not_fresh_at_mono] >> simp[]) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (Cases_on `mid` >> gvs[]) >>
  `local_ptrs_reserved ce ready /\
   (!x. not_fresh_at origin x ==> not_fresh_at ready x) /\
   (!x. not_fresh_at st x ==> not_fresh_at ready x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono, LESS_EQ_TRANS] >>
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
  suspend "setup_kept"
QED

Resume abi_encode_word_pack_effects_mods[setup_kept]:
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
  qabbrev_tac `k = case mid of NONE => 0 | SOME _ => 4` >>
  qabbrev_tac `N = 32 * word_size (k+32) + 32` >>
  qabbrev_tac `p = w2n (w:bytes32)` >>
  qabbrev_tac `d = p+(k+32)` >>
  suspend "payload"
QED

Resume abi_encode_word_pack_effects_mods[payload]:
  `p+32 <= d /\ d+32 <= p+N` by
    (simp[Abbr `d`, Abbr `N`, Abbr `k`] >>
     Cases_on `mid` >> EVAL_TAC >> decide_tac) >>
  `d < dimword (:256) /\ d+32 <= ready_s.vs_alloca_next` by decide_tac >>
  qpat_x_assum `data_ptr = Var dp` SUBST_ALL_TAC >>
  `lookup_var dp ready_s = SOME (n2w d)` by fs[eval_operand_def] >>
  `ready_s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ready_s` by
    (qpat_assum `typed_copy_state_frame _ _ _ allocated_s ready_s`
      (rewrite_tac o single o MATCH_MP typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp) >>
     first_assum ACCEPT_TAC) >>
  drule_all bodyPtrMakeArrayPrimitiveInstallTheory.emit_void_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst ready.cs_next_id MSTORE [Var dp;value] []` >>
  qabbrev_tac `u = mstore d word ready_s` >>
  mp_tac (Q.INST [`a` |-> `ready`,`b` |-> `body_end`,`s` |-> `ready_s`,
    `dst` |-> `dp`,`p` |-> `d`,`w` |-> `word`,`G` |-> `Gready`,`tn` |-> `tready`]
    abi_encode_payload_word_origin) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`saved`,`tf`] strip_assume_tac) >>
  qabbrev_tac `copied = saved` >>
  qabbrev_tac `tc = tf` >>
  `typed_copy_state_frame ready d 32 ready_s copied` by
    (simp_tac (srw_ss()) [Abbr `copied`] >>
     qpat_assum `saved = _` SUBST1_TAC >>
     simp[NoAsms, typedMemoryCopyTheory.typed_copy_mstore_state_frame]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp copied` by
    (qpat_assum `typed_copy_state_frame ready d 32 ready_s copied`
      (rewrite_tac o single o MATCH_MP typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp) >>
     first_assum ACCEPT_TAC) >>
  `copied.vs_allocas = ready_s.vs_allocas /\ copied.vs_alloca_next = ready_s.vs_alloca_next /\
   (!x. lookup_var x copied = lookup_var x ready_s)` by
    simp[Abbr `copied`, Abbr `u`, mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
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
   tc.t_mem = tready.t_mem DIFF {j | d <= j /\ j < d+32}` by simp[Abbr `tc`] >>
  `lookup_var q copied = SOME (n2w p) /\ ptr_covers Gready tc q copied N` by
    (conj_tac
     >- simp[Abbr `p`, GSYM eval_operand_def] >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`Gready`,`ready_s`,`tready`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_assum `!x. lookup_var x copied = _` (ACCEPT_TAC o Q.SPEC `q`)) >>
     qpat_assum `tc.t_var = tready.t_var` (fn th => simp[NoAsms, op_taint_def, th])) >>
  `not_fresh_at body_end q` by suspend "finish_fresh" >>
  suspend "finish"
QED

Resume abi_encode_word_pack_effects_mods[finish_fresh]:
  qpat_assum `emit_void MSTORE _ ready = _`
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

Resume abi_encode_word_pack_effects_mods[finish]:
  `p+32 <= copied.vs_alloca_next /\ p < dimword(:256)` by decide_tac >>
  `32 <= N` by simp[Abbr `N`] >>
  `ptr_covers Gready tc q copied 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `N` >> simp[]) >>
  `32+k < dimword(:256)` by (Cases_on `mid` >> simp[Abbr `k`, dimword_def]) >>
  mp_tac (Q.INST [`a` |-> `body_end`,`b` |-> `final`,`s` |-> `copied`,
    `root` |-> `q`,`len` |-> `32`,`lenop` |-> `Lit 32w`,
    `G` |-> `Gready`,`tn` |-> `tc`] abi_encode_finish_origin) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def, op_taint_def] >>
  strip_tac >>
  qmatch_asmsub_rename_tac `typed_copy_state_frame body_end p 32 copied t` >>
  qmatch_asmsub_rename_tac `tnt.t_mem = tc.t_mem DIFF _` >>
  qmatch_asmsub_rename_tac `ptr_covers Gfinal tnt q t 32` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK ready_s,Gready,tready)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Ga`,`allocated_s`,`ta`] >> asm_rewrite_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK copied,Gready,tc)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gready`,`ready_s`,`tready`] >>
     asm_simp_tac bool_ss [Abbr `copied`, Abbr `tc`]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gfinal,tnt)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gready`,`copied`,`tc`] >> asm_rewrite_tac[]) >>
  `ptr_covers Gfinal tnt q t N` by
    (qpat_assum `!x n. not_fresh_at body_end x /\ _ ==> _` irule >> simp[]) >>
  `alloca_history func copied` by
    (`step_inst_base i ready_s = OK u` by
       simp[Abbr `i`, Abbr `u`, Once step_inst_base_def, exec_write2_def, mk_inst_def, eval_operand_def, w2n_n2w] >>
     `lookup_block ready_s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb ready_s.vs_inst_idx = SOME i` by metis_tac[] >>
     drule_all allocaHistoryTheory.alloca_history_base_step >>
     simp[Abbr `i`, Abbr `copied`, mk_inst_def, is_terminator_def]) >>
  suspend "output_resources"
QED

Resume abi_encode_word_pack_effects_mods[output_resources]:
  `d = p+32+k` by (qpat_assum `Abbrev (d = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> decide_tac) >>
  `mem_bytes_at d 32 copied.vs_memory = enc at av` by
    (qpat_assum `!mem. mem_agree_outside tc.t_mem copied.vs_memory mem ==> _`
      (qspec_then `copied.vs_memory` mp_tac) >>
     simp[Abbr `copied`, mem_agree_outside_def, valueEncodingProofsTheory.mem_bytes_at_word]) >>
  `!a n. a+n <= p \/ p+32 <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n copied.vs_memory` by
    (qpat_assum `typed_copy_state_frame body_end p 32 copied t`
       (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
          typedMemoryCopyTheory.typed_copy_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `mem_bytes_at d 32 t.vs_memory = enc at av` by
    (qpat_assum `!a n. _ ==> _ = mem_bytes_at a n copied.vs_memory`
       (qspecl_then [`d`,`32`] mp_tac) >> simp[]) >>
  `!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      mem_bytes_at d 32 mem = enc at av` by suspend "payload_clean" >>
  `(case mid of NONE => T | SOME selector =>
     !mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
       mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)` by
    suspend "selector_window" >>
  suspend "protected"
QED

Resume abi_encode_word_pack_effects_mods[payload_clean]:
  `!j. d <= j /\ j < d+32 ==> j NOTIN tnt.t_mem` by
    (qx_gen_tac `j` >> strip_tac >>
     qpat_assum `tnt.t_mem = _` SUBST1_TAC >>
     qpat_assum `tc.t_mem = _ DIFF _` SUBST1_TAC >>
     simp[IN_DIFF]) >>
  rpt strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 mem` by
    (irule logStoreDataOriginPtrTheory.mem_agree_outside_window >>
     qexists_tac `tnt.t_mem` >> simp[]) >>
  qpat_assum `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 mem`
    (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC
QED

Resume abi_encode_word_pack_effects_mods[selector_window]:
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

Resume abi_encode_word_pack_effects_mods[protected]:
  `p+32+(case mid of NONE => 0 | SOME _ => 32) <= p+N` by
    (Cases_on `mid` >> simp[Abbr `N`, Abbr `k`, vfmConstantsTheory.word_size_def]) >>
  `typed_copy_state_frame allocated p N allocated_s ready_s` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`p+32`,`case mid of NONE => 0 | SOME _ => 32`] >> simp[]) >>
  `ci_mono allocated ready /\ ci_mono allocated body_end` by suspend "frame_fresh" >>
  `typed_copy_state_frame allocated d 32 ready_s copied` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
     qexists_tac `ready` >> asm_rewrite_tac[] >> fs[ci_mono_def]) >>
  `typed_copy_state_frame allocated p 32 copied t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
     qexists_tac `body_end` >> asm_rewrite_tac[] >> fs[ci_mono_def]) >>
  `typed_copy_state_frame allocated p N ready_s copied` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`d`,`32`] >> asm_rewrite_tac[] >> decide_tac) >>
  `typed_copy_state_frame allocated p N copied t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`p`,`32`] >> asm_rewrite_tac[] >> decide_tac) >>
  `typed_copy_state_frame allocated p N allocated_s copied` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
     qexists_tac `ready_s` >> asm_rewrite_tac[]) >>
  `typed_copy_state_frame allocated p N allocated_s t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
     qexists_tac `copied` >> asm_rewrite_tac[]) >>
  suspend "frame_posts"
QED

Resume abi_encode_word_pack_effects_mods[frame_fresh]:
  qpat_assum `compile_alloc_buffer N st = _`
    (mp_then Any mp_tac abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  qpat_assum `emit_op ALLOCA _ st = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_void MSTORE _ ready = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  `cs_extends allocated ready /\ cs_extends allocated body_end` by
    metis_tac[cs_extends_trans] >>
  Cases_on `mid` >> simp[ci_mono_def]
QED

Resume abi_encode_word_pack_effects_mods[frame_posts]:
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
     `q = STRING #"%" (toString st.cs_next_var)` by
       (qpat_assum `buf.buf_operand = Var q` mp_tac >>
        qpat_assum `buf.buf_operand = Var (STRING _ _)`
          (fn th => simp[NoAsms, th])) >>
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
     asm_rewrite_tac[] >>
     rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `st` >> asm_rewrite_tac[] >> fs[ci_mono_def]) >>
  suspend "assemble_posts"
QED

Resume abi_encode_word_pack_effects_mods[assemble_posts]:
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
  `t.vs_allocas = allocated_s.vs_allocas /\
   t.vs_alloca_next = allocated_s.vs_alloca_next` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|> = allocated_s` (SUBST1_TAC o SYM) >>
     simp[NoAsms]) >>
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row` by
    (qpat_assum `t.vs_allocas = allocated_s.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocated_s.vs_allocas = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b` by suspend "new_rows" >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,N) /\
   p+N <= t.vs_alloca_next /\ t.vs_alloca_next < dimword(:256) /\
   s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\ allocas_from lo t` by
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- asm_rewrite_tac[]
     >- asm_rewrite_tac[]
     >- (qpat_assum `t.vs_alloca_next = copied.vs_alloca_next` SUBST1_TAC >>
         qpat_assum `copied.vs_alloca_next = ready_s.vs_alloca_next` SUBST1_TAC >>
         first_assum ACCEPT_TAC)
     >- asm_rewrite_tac[]
     >- (qpat_assum `fn_inst_ids_distinct func /\ alloca_history func copied ==> alloca_history func t`
           irule >> asm_rewrite_tac[]) >>
     PURE_REWRITE_TAC [allocas_from_def] >>
     qpat_assum `allocas_from lo allocated_s` (mp_tac o PURE_REWRITE_RULE [allocas_from_def]) >>
     asm_rewrite_tac[]) >>
  `pure_frame ce func ee st s t` by
    (pure_rewrite_tac[pure_frame_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!a n. _ ==> _ = mem_bytes_at a n s.vs_memory` irule >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz`
       (qspecl_then [`mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [q]`, `p`, `N`] mp_tac) >>
     simp[mk_inst_def, regions_disjoint_def, DISJ_COMM]) >>
  suspend "endpoint_extras"
QED

Resume abi_encode_word_pack_effects_mods[old_vars]:
  `!x. not_fresh_at st x ==> not_fresh_at allocated x /\ not_fresh_at body_end x` by
    (qpat_assum `ci_mono allocated body_end`
       (strip_assume_tac o PURE_REWRITE_RULE [ci_mono_def]) >>
     qx_gen_tac `x` >> disch_tac >> conj_tac
     >- (irule not_fresh_at_mono >> qexists_tac `st` >> asm_rewrite_tac[]) >>
     irule not_fresh_at_mono >> qexists_tac `st` >> asm_rewrite_tac[] >> decide_tac) >>
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

Resume abi_encode_word_pack_effects_mods[local_sep]:
  rpt strip_tac >>
  qpat_assum `!name b len. local_region ce ee.scopes allocated_s name b len ==> regions_disjoint p N b len` irule >>
  qexists_tac `name` >>
  irule exprSimPropsTheory.local_region_frame_fwd >>
  qexistsl_tac [`s`,`st`,`ee.scopes`] >> simp[]
QED

Resume abi_encode_word_pack_effects_mods[new_rows]:
  qpat_assum `t.vs_allocas = allocated_s.vs_allocas` SUBST1_TAC >>
  qpat_assum `allocated_s.vs_allocas = _` SUBST1_TAC >>
  rpt gen_tac >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id = NONE` >>
  simp[abiBuiltinAllocationTheory.abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  Cases_on `aid = st.cs_next_id` >> simp[]
QED

Resume abi_encode_word_pack_effects_mods[endpoint_extras]:
  `!j. j < s.vs_alloca_next /\ j IN tnt.t_mem ==> j IN tn.t_mem` by
    (qpat_assum `tnt.t_mem = tc.t_mem DIFF _` SUBST1_TAC >>
     qpat_assum `tc.t_mem = tready.t_mem DIFF _` SUBST1_TAC >>
     qpat_assum `tready.t_mem = ta.t_mem DIFF _` SUBST1_TAC >>
     simp[IN_DIFF] >> rpt strip_tac >>
     `~(s.vs_alloca_next <= j)` by decide_tac >>
     qpat_assum `!i. i IN ta.t_mem <=> _` (qspec_then `j` mp_tac) >> simp[]) >>
  `t.vs_data_section = s.vs_data_section /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_inst_idx := _;
         vs_allocas := _; vs_alloca_next := _|> = s` (SUBST1_TAC o SYM) >>
     qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
         vs_current_bb := _; vs_inst_idx := _|> = allocated_s` (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) []) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `allocated_s.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `tnt.t_stor = tn.t_stor /\ tnt.t_trans = tn.t_trans /\ tnt.t_imm = tn.t_imm` by
    asm_rewrite_tac[] >>
  suspend "select_endpoint"
QED

Resume abi_encode_word_pack_effects_mods[select_endpoint]:
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
  `st.cs_next_id < final.cs_next_id` by
    (qpat_assum `abi_builtin_encode_finish _ _ k body_end = ((),final)`
       (strip_assume_tac o MATCH_MP abi_builtin_encode_finish_shape) >>
     qpat_assum `emit_void MSTORE _ ready = ((),body_end)`
       (strip_assume_tac o MATCH_MP emit_void_next_id) >>
     qpat_assum `final.cs_next_id = _` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `body_end.cs_next_id = _` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `st.cs_next_id <= ready.cs_next_id` mp_tac >>
     Cases_on `0 < k` >> simp[NoAsms]) >>
  `!name b n. local_region ce ee.scopes t name b n ==> p+N <= b \/ b+n <= p` by
    suspend "local_post" >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 Gfinal tnt` by suspend "ghost_kept" >>
  `wb_frame ce es ee origin s0 t` by suspend "wb_post" >>
  `(pure_frame ce func es origin s0 s ==> pure_frame ce func es origin s0 t)` by
    suspend "pure_post" >>
  qexistsl_tac [`p`,`t`,`Gfinal`,`tnt`] >>
  `32 + k = k + 32` by decide_tac >>
  `32 + 32 * word_size (k+32) = N` by simp[Abbr `N`] >>
  qpat_assum `Abbrev (k = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `32+k = k+32` SUBST1_TAC >>
  qpat_assum `32 + 32 * word_size (k+32) = N` SUBST1_TAC >>
  qpat_assum `Abbrev (d = p+(k+32))`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `enc at av = word_to_bytes word T`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC)
QED

Resume abi_encode_word_pack_effects_mods[local_post]:
  rpt gen_tac >> disch_tac >>
  `local_region ce ee.scopes s name b n` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`t`,`st`,`ee.scopes`] >>
     simp_tac bool_ss [EQ_REFL] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `lookup_var x t = lookup_var x s` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!name b sz. local_region ce ee.scopes s name b sz ==>
       loweringStateRelDefs$regions_disjoint p N b sz`
    (qspecl_then [`name`,`b`,`n`] (drule_then mp_tac)) >>
  simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume abi_encode_word_pack_effects_mods[ghost_kept]:
  `tnt.t_mem SUBSET tready.t_mem` by
    (qpat_assum `tnt.t_mem = tc.t_mem DIFF _` SUBST1_TAC >>
     qpat_assum `tc.t_mem = tready.t_mem DIFF _` SUBST1_TAC >>
     simp[SUBSET_DEF, IN_DIFF]) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  qexistsl_tac [`Gready`,`tready`] >> simp[] >> qx_gen_tac `x` >> disch_tac >>
  `not_fresh_at st x` by
    (irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
  `not_fresh_at body_end x` by
    (irule not_fresh_at_mono >> qexists_tac `allocated` >>
     qpat_assum `ci_mono allocated body_end` (strip_assume_tac o SRULE [ci_mono_def]) >>
     simp[] >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  qpat_assum `!x. not_fresh_at body_end x ==> lookup_var x t = _ /\ _`
    (drule_then strip_assume_tac) >>
  `op_taint tc (Var x) = op_taint tready (Var x)` by simp[op_taint_def] >>
  simp[]
QED

Resume abi_encode_word_pack_effects_mods[wb_post]:
  match_mp_tac (Q.INST [`cenv` |-> `ce`, `es'` |-> `ee`, `sa` |-> `origin`,
    `sm` |-> `st`, `scopes` |-> `ee.scopes`] wb_frame_allocating_tail) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_gen_tac `x` >> disch_tac >>
  qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _`
    (qspec_then `x` (drule_then (ACCEPT_TAC o cj 1)))
QED

Resume abi_encode_word_pack_effects_mods[pure_post]:
  disch_tac >>
  match_mp_tac (Q.SPECL [`ce`,`func`,`es`,`ee`,`origin`,`st`,`s0`,`s`,`t`]
    exprSimPropsTheory.pure_frame_trans) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `wb_frame ce es ee origin s0 s`
    (ACCEPT_TAC o cj 1 o MATCH_MP (iffLR wb_frame_def))
QED

Finalise abi_encode_word_pack_effects_mods

(* Physical setup after the output allocation.  No execution is selected per horizon. *)
Theory bodyFullAbiEncodeSetupTail
Ancestors
  bodyFullAbiEncodeOffset bodyFullAbiEncodeStore bodyFullPathHistory abiBuiltinAllocation
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission abiBuiltinEncodeCode typedMemoryCopy exprSimProps
  wordArgsPtr bodyFullUnwrapRun exprLoweringProps localPtrsProps bodyPtrMakeArrayWordStore exprSimPtrTopLevelImmutableCopy
  fragExec fragGasOriginPtr wordLoadStorePtr robustCopyTransportPtr
  emitHelper emitHelperProps compileEnv venomState venomExecSemantics
  instMemFrontier memSafeRun unitTransformDefs contextCodegenRel codegenRel
  words arithmetic finite_map pred_set ptrDiscipline venomInst bodyPtrDefs pair freshWrites
  loweringStateRelDefs logInstSeqPtr

Theorem abi_encode_setup_add_run[local]:
  emit_op ADD [Var root;Lit (n2w off)] a = (Var q,b) /\
  lookup_var root s = SOME w ==>
  run_inst_seq (emitted_insts a b) s = OK (update_var q (w+n2w off) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def]
QED

Theorem abi_encode_setup_store_run[local]:
  emit_void MSTORE [Var root;Lit w] a = ((),b) /\
  lookup_var root s = SOME (n2w p) /\ p < dimword(:256) ==>
  run_inst_seq (emitted_insts a b) s = OK (mstore p w s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, w2n_n2w]
QED

Theorem abi_encode_setup_run_join[local]:
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  c.cs_current_insts = b.cs_current_insts ++ emitted_insts b c /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b c) /\
  run_inst_seq (emitted_insts a b) s = OK x /\
  m = (x with vs_inst_idx := LENGTH b.cs_current_insts) /\
  run_inst_seq (emitted_insts b c) m = OK y ==>
  ?raw. run_inst_seq (emitted_insts a c) s = OK raw /\
        (y with vs_inst_idx := LENGTH c.cs_current_insts) =
        (raw with vs_inst_idx := LENGTH c.cs_current_insts)
Proof
  strip_tac >> drule_all emitted_insts_append >> strip_tac >>
  `LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts a b)` by
    simp[] >>
  qexists_tac `y with vs_inst_idx := x.vs_inst_idx` >> simp[] >>
  irule run_inst_seq_append_advanced >> gvs[]
QED

Theorem abi_encode_payload_word_origin:
  emit_void MSTORE [Var dst;value] a = ((),b) /\ fn_has_code a b func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var dst s = SOME (n2w p) /\ p < dimword(:256) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\
  p+32 <= s.vs_alloca_next ==>
  ?t tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf)) /\
    t = (mstore p w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    tf = (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> mem_word_at p mem = w) /\
    (!D d ce cx es.
      ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
      lo <= p /\ (!name base sz. local_region ce es.scopes s name base sz ==>
        regions_disjoint p 32 base sz) ==>
      ghost_inv_at D lo d ce cx es G tf t) /\
    (!ce es origin G0 tn0 s0.
      ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G tf)
Proof
  strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  qexistsl_tac [`mstore p w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}`] >>
  simp[] >> conj_tac >- suspend "path" >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "inv" >>
  rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> simp[op_taint_def, SUBSET_DEF]
QED

Resume abi_encode_payload_word_origin[path]:
  gen_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst a.cs_next_id MSTORE [Var dst;value] [])` by simp[] >>
  drule_at (Pat `get_instruction _ _ = _`) abi_encode_mstore_origin_path >>
  simp[eval_operand_def, op_taint_def, w2n_n2w,
    SRULE [eval_operand_def, op_taint_def] toplevel_immutable_mstore_ghost_frame] >>
  disch_then irule >> simp[] >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    sized_source_write_range_def, fixed_source_write_range_def,
    eval_operand_def, w2n_n2w, ADD_COMM] >>
  fs[op_taint_def]
QED

Resume abi_encode_payload_word_origin[robust]:
  rpt strip_tac >>
  `step_taint (mk_inst a.cs_next_id MSTORE [Var dst;value] []) s (mstore p w s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32})` by
    (drule_all (SRULE [eval_operand_def, w2n_n2w] toplevel_immutable_mstore_ghost_frame) >>
     simp[]) >>
  drule_at (Pat `lookup_var _ _ = _`) mstore_raw_robust_word >>
  simp[w2n_n2w] >> disch_then irule >>
  qexistsl_tac [`a.cs_next_id`, `tn`, `value`] >>
  simp[eval_operand_def, op_taint_def]
QED

Resume abi_encode_payload_word_origin[inv]:
  rpt strip_tac >>
  `ghost_kept_at lo ce es a G tn s G tn` by simp[ghost_kept_at_refl] >>
  drule_at (Pat `lookup_var _ _ = _`) (cj 1 abi_encode_mstore_frame_at) >>
  simp[eval_operand_def, op_taint_def, w2n_n2w,
    SRULE [eval_operand_def, op_taint_def] toplevel_immutable_mstore_ghost_frame] >>
  disch_then irule >>
  simp[] >> conj_tac
  >- gvs[] >>
  fs[op_taint_def] >> metis_tac[]
QED

Finalise abi_encode_payload_word_origin

(* The selector occupies a full MSTORE word, even though only four bytes are
   included in the encoded payload.  Allocation is deliberately a caller step. *)
Theorem abi_encode_setup_tail_origin_run:
  k = (case mid of NONE => 0 | SOME w => 4) /\
  N = 32 + 32 * word_size (maxlen+k) /\
  write_len = (case mid of NONE => 0 | SOME w => 32) /\
  abi_builtin_encode_method_id mid (Var root) a = ((),method_st) /\
  emit_op ADD [Var root;Lit (n2w (32+k))] method_st = (data,ready) /\
  fn_has_code a ready func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ alloca_inv s /\
  lookup_var root s = SOME (n2w p) /\ not_fresh_at a root /\
  ptr_covers G tn root s N /\ lo <= p /\
  p+N <= s.vs_alloca_next /\ p+N < dimword(:256) ==>
  ?dp t G' tn'.
    (?raw. run_inst_seq (emitted_insts a ready) s = OK raw /\
           t = (raw with vs_inst_idx := LENGTH ready.cs_current_insts)) /\
    data = Var dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand data t = SOME (n2w (p+32+k)) /\
    ptr_covers G' tn' dp t (N-(32+k)) /\
    ptr_covers G' tn' root t N /\
    eval_operand (Var root) t = SOME (n2w p) /\ not_fresh_at ready dp /\
    (case mid of NONE => T | SOME w =>
      !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
        mem_word_at (p+32) mem = w << 224) /\
    typed_copy_state_frame a (p+32) write_len s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv t /\ allocas_from lo t /\
    tn'.t_mem = tn.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
      eval_operand op t = eval_operand op s /\
      op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op) /\
    (!x n. not_fresh_at a x /\ ptr_covers G tn x s n ==>
      ptr_covers G' tn' x t n) /\
    (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
    (fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func t) /\
    (!ce es.
      local_ptrs_rel func ce es.scopes s /\
      (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
        not_fresh_at a x) /\
      (!name b sz. local_region ce es.scopes s name b sz ==>
        regions_disjoint (p+32) write_len b sz) ==>
      local_ptrs_rel func ce es.scopes t) /\
    (!D d ce cx es.
      ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
      (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
        not_fresh_at a x) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
      (!name b sz. local_region ce es.scopes s name b sz ==>
        regions_disjoint (p+32) write_len b sz) ==>
      ghost_inv_at D lo d ce cx es G' tn' t) /\
    (!ce es origin G0 tn0 s0.
      ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
      (!x. not_fresh_at origin x ==> not_fresh_at a x) ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G' tn')
Proof
  strip_tac >> Cases_on `mid`
  >- suspend "none" >> suspend "some"
QED

Resume abi_encode_setup_tail_origin_run[none]:
  gvs[abi_builtin_encode_method_id_def, comp_return_def] >>
  `32+maxlen <= 32+32*word_size maxlen` by
    (mp_tac (Q.SPEC `maxlen` le_word_size_mul) >> decide_tac) >>
  `w2n (n2w p : bytes32)+32 < dimword(:256)` by
    (simp[w2n_n2w] >> decide_tac) >>
  drule_at (Pat `emit_op _ _ _ = _`)
    (Q.INST [`off` |-> `32`] (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  simp[] >> disch_then (qspecl_then [`32*word_size maxlen`, `explicit`, `ctx`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `data = Var dp` >>
  `!x. not_fresh_at a x ==> x <> dp` by
    (drule_all emit_op_fetch_boundary >> strip_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `lookup_var dp t = _` >>
  `!x n. not_fresh_at a x /\ ptr_covers G tn x s n ==>
    ptr_covers G' tn' x t n` by
    (rpt strip_tac >> `x <> dp` by metis_tac[] >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `alloca_inv t` by
    (irule alloca_inv_fields >> qexists_tac `s` >>
     simp[Abbr `t`, update_var_def]) >>
  `allocas_from lo t` by
    (gvs[Abbr `t`, update_var_def, allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`dp`, `t`, `G'`, `tn'`] >>
  conj_tac >-
    (qexists_tac `update_var dp (n2w p + 32w) s` >>
     conj_tac >- (irule abi_encode_setup_add_run >> qexists_tac `root` >> simp[]) >>
     simp[Abbr `t`]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `t`, update_var_def, eval_operand_def] >>
  conj_tac >- suspend "none_frame" >>
  conj_tac >- suspend "none_history" >>
  conj_tac >- suspend "none_locals" >>
  conj_tac >- suspend "none_inv" >>
  suspend "none_kept"
QED

Resume abi_encode_setup_tail_origin_run[none_frame]:
  simp[typed_copy_state_frame_def, typed_copy_frame_def, lookup_var_def,
    FLOOKUP_UPDATE, venom_state_component_equality] >> rpt strip_tac >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin_run[none_history]:
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[body_full_path_alloca_history]
QED

Resume abi_encode_setup_tail_origin_run[none_locals]:
  rpt strip_tac >> irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> `p' <> dp` by metis_tac[] >> simp[]
QED

Resume abi_encode_setup_tail_origin_run[none_inv]:
  rpt strip_tac >> gvs[update_var_def] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin_run[none_kept]:
  rpt strip_tac >> gvs[update_var_def] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin_run[some]:
  gvs[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [Var root;Lit 32w] a = (midop,store_st)` >>
  `cs_extends a store_st /\ cs_extends store_st method_st /\ cs_extends method_st ready` by
    (metis_tac[ci_mono_def, ci_mono_emit_op, ci_mono_emit_void, SND]) >>
  `fn_has_code a store_st func /\ fn_has_code store_st method_st func /\
    fn_has_code method_st ready func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `36+maxlen <= 32+32*word_size (maxlen+4)` by
    (mp_tac (Q.SPEC `maxlen+4` le_word_size_mul) >> decide_tac) >>
  mp_tac abi_builtin_rounded_selector_store >> strip_tac >>
  `w2n (n2w p : bytes32)+32 < dimword(:256)` by
    (simp[w2n_n2w] >> decide_tac) >>
  drule_at (Pat `emit_op ADD [Var root;Lit 32w] a = _`)
    (Q.INST [`off` |-> `32`] (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (drule_at (Pat `ptr_covers G tn root s _`)) >>
  disch_then (drule_at (Pat `fn_has_code a store_st _`)) >>
  disch_then (drule_at (Pat `allocas_from _ s`)) >>
  simp[] >> disch_then (qspecl_then [`32`, `explicit`, `ctx`, `PG`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `midop = Var mp` >>
  qmatch_asmsub_abbrev_tac `lookup_var mp s1 = _` >>
  `allocas_from lo s1 /\ p+32+32 <= s1.vs_alloca_next` by
    (fs[Abbr `s1`, update_var_def] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[Abbr `s1`, update_var_def, allocas_below_fmp_def]) >>
  qpat_x_assum `midop = Var mp` SUBST_ALL_TAC >>
  rename1 `ptr_covers G1 tn1 mp (update_var mp _ s) 32` >>
  `ptr_covers G1 tn1 mp s1 32` by
    fs[ptr_covers_def, Abbr `s1`, lookup_var_def] >>
  mp_tac (Q.INST [`a` |-> `store_st`, `b` |-> `method_st`, `s` |-> `s1`,
    `p` |-> `p+32`, `dst` |-> `mp`, `value` |-> `Lit (x << 224)`,
    `w` |-> `x << 224`, `G` |-> `G1`, `tn` |-> `tn1`]
    abi_encode_payload_word_origin) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [eval_operand_def, op_taint_def] >>
      simp[Abbr `s1`, update_var_def] >> decide_tac) >>
  strip_tac >>
  rename1 `s2 = (mstore (p+32) _ s1 with vs_inst_idx := SUC s1.vs_inst_idx)` >>
  rename1 `gas_origin_ptr_path _ (s1,G1,tn1) [] (OK s2,G1,tn2)` >>
  `!v. not_fresh_at a v ==> v <> mp` by
    (drule_all emit_op_fetch_boundary >> strip_tac >> gvs[]) >>
  `lookup_var root s2 = SOME (n2w p)` by
    (`root <> mp` by metis_tac[] >>
     fs[mstore_def, Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers G1 tn2 root s2 (32 * word_size (maxlen+4)+32)` by
    (`root <> mp` by metis_tac[] >>
     gvs[ptr_covers_def, Abbr `s1`, mstore_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]) >>
  `allocas_from lo s2` by
    (fs[mstore_def, allocas_from_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `s2 = (mstore _ _ s1 with vs_inst_idx := _)` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s1` mp_tac >>
     simp[NoAsms, mstore_def, write_memory_with_expansion_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  `w2n (n2w p : bytes32)+36 < dimword(:256)` by
    (simp[w2n_n2w] >> decide_tac) >>
  mp_tac (Q.SPECL [`method_st`,`ready`,`data`,`root`,`36`,`s2`,`n2w p`,
    `G1`,`tn2`,`32*word_size (maxlen+4)+32`,`32*word_size (maxlen+4)-4`,
    `lo`,`explicit`,`ctx`,`func`,`PG`] abi_encode_owned_offset_origin) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp_tac (srw_ss()) [NoAsms] >> decide_tac) >>
  disch_then (qx_choosel_then [`dp`,`t`,`G'`,`tn'`] strip_assume_tac) >>
  `a.cs_next_var <= method_st.cs_next_var` by
    (metis_tac[ci_mono_def, ci_mono_emit_op, ci_mono_emit_void, SND, LESS_EQ_TRANS]) >>
  `!v. not_fresh_at a v ==> v <> dp` by
    (gen_tac >> disch_tac >>
     mp_tac (Q.INST [`opc` |-> `ADD`, `args` |-> `[Var root; Lit 36w]`,
       `sm` |-> `method_st`, `sb` |-> `ready`, `sa` |-> `a`, `tmp` |-> `dp`,
       `x` |-> `v`] emit_op_old_var_separate) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    metis_tac[gas_origin_ptr_path_append, listTheory.APPEND] >>
  `root <> dp` by metis_tac[] >>
  `root <> mp` by metis_tac[] >>
  `p < dimword(:256)` by decide_tac >>
  `lookup_var root t = SOME (n2w p) /\ FLOOKUP G' root = FLOOKUP G1 root /\
    op_taint tn' (Var root) = op_taint tn2 (Var root)` by
    (qpat_assum `!x. x <> dp ==> lookup_var x t = _ /\ _`
       (qspec_then `root` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[]) >>
  `ptr_covers G' tn' root t (32*word_size (maxlen+4)+32)` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G1`,`s2`,`tn2`] >> asm_rewrite_tac[]) >>
  `w2n (n2w p : bytes32) = p` by simp[w2n_n2w] >>
  `eval_operand data t = SOME (n2w (p+36))` by
    (qpat_assum `lookup_var dp t = _` mp_tac >>
     qpat_assum `data = Var dp` (fn data_eq =>
       qpat_assum `w2n (n2w p : bytes32) = p` (fn p_eq =>
         simp_tac bool_ss [data_eq, p_eq, eval_operand_def]))) >>
  `eval_operand (Var root) t = SOME (n2w p)` by
    (simp_tac bool_ss [eval_operand_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    mem_word_at (p+32) mem = x << 224` by
    (qpat_assum `t.vs_memory = s2.vs_memory` SUBST1_TAC >>
     qpat_assum `tn'.t_mem = tn2.t_mem` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func t` by
    (strip_tac >> qpat_assum `!D. gas_origin_ptr_path _ (s,_,_) [] (OK t,_,_)`
       (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `32*word_size (maxlen+4)+32-36 = 32*word_size (maxlen+4)-4` by decide_tac >>
  qexistsl_tac [`dp`,`t`,`G'`,`tn'`] >>
  conj_tac >- suspend "some_run" >>
  qpat_assum `32*word_size (maxlen+4)+32-36 = _` (fn th =>
    simp[NoAsms, arithmeticTheory.ADD_ASSOC, th]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "some_posts"
QED

Resume abi_encode_setup_tail_origin_run[some_run]:
  qpat_assum `emit_op ADD _ a = _` (strip_assume_tac o MATCH_MP emit_op_extends) >>
  qpat_assum `emit_void MSTORE _ store_st = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_assum `emit_op ADD _ method_st = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  `lookup_var mp s1 = SOME (n2w (p+32))` by simp[Abbr `s1`, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  `run_inst_seq (emitted_insts a store_st) s = OK (update_var mp (n2w p + 32w) s)` by
    (irule abi_encode_setup_add_run >> qexists_tac `root` >> asm_rewrite_tac[]) >>
  `run_inst_seq (emitted_insts store_st method_st) s1 = OK (mstore (p+32) (x << 224) s1)` by
    (irule abi_encode_setup_store_run >> conj_tac >- decide_tac >>
     qexists_tac `mp` >> asm_rewrite_tac[]) >>
  `s1 = (update_var mp (n2w p + 32w) s with vs_inst_idx := LENGTH store_st.cs_current_insts)` by
    simp[Abbr `s1`] >>
  `?raw. run_inst_seq (emitted_insts a method_st) s = OK raw /\
         s2 = (raw with vs_inst_idx := LENGTH method_st.cs_current_insts)` by
    (qpat_assum `s2 = _` SUBST1_TAC >>
     `SUC s1.vs_inst_idx = LENGTH method_st.cs_current_insts` by
       (qpat_assum `s2.vs_inst_idx = _` mp_tac >> simp[]) >>
     qpat_assum `SUC s1.vs_inst_idx = _` (pure_once_rewrite_tac o single) >>
     irule abi_encode_setup_run_join >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`store_st`, `s1`, `update_var mp (n2w p + 32w) s`] >>
     simp[mk_inst_def, is_terminator_def]) >>
  `method_st.cs_current_insts = a.cs_current_insts ++ emitted_insts a method_st` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_assum `method_st.cs_current_insts = _` (pure_rewrite_tac o single) >>
     qpat_assum `store_st.cs_current_insts = _` (pure_once_rewrite_tac o single) >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     REFL_TAC) >>
  `run_inst_seq (emitted_insts method_st ready) s2 = OK (update_var dp (n2w p + 36w) s2)` by
    (irule abi_encode_setup_add_run >> qexists_tac `root` >> conj_tac
     >- first_assum ACCEPT_TAC >>
     qpat_assum `data = Var dp` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `t = _` SUBST1_TAC >>
  `SUC s2.vs_inst_idx = LENGTH ready.cs_current_insts` by
    (qpat_assum `t.vs_inst_idx = _` mp_tac >> simp[]) >>
  qpat_assum `SUC s2.vs_inst_idx = _` (pure_once_rewrite_tac o single) >>
  irule abi_encode_setup_run_join >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`method_st`, `s2`, `raw`] >> simp[mk_inst_def, is_terminator_def]
QED

Resume abi_encode_setup_tail_origin_run[some_posts]:
  conj_tac >- suspend "some_frame" >>
  conj_tac >- simp[mstore_def, Abbr `s1`, update_var_def] >>
  conj_tac >- simp[mstore_def, Abbr `s1`, update_var_def] >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >>
    simp[mstore_def, Abbr `s1`, update_var_def]) >>
  conj_tac >- (fs[allocas_from_def, mstore_def, Abbr `s1`, update_var_def] >> metis_tac[]) >>
  conj_tac >- (asm_rewrite_tac[] >> simp[arithmeticTheory.ADD_ASSOC]) >>
  conj_tac >- (qpat_assum `tn'.t_stor = tn2.t_stor` SUBST1_TAC >> asm_rewrite_tac[] >> simp[]) >>
  conj_tac >- (qpat_assum `tn'.t_trans = tn2.t_trans` SUBST1_TAC >> asm_rewrite_tac[] >> simp[]) >>
  conj_tac >- (qpat_assum `tn'.t_imm = tn2.t_imm` SUBST1_TAC >> asm_rewrite_tac[] >> simp[]) >>
  conj_tac >- suspend "some_operands" >>
  conj_tac >- suspend "some_old_cover" >>
  conj_tac >- (rpt strip_tac >> irule abiAllocationHistoryTheory.abi_alloca_history_frame >>
    qexists_tac `s` >> simp[mstore_def, Abbr `s1`, update_var_def]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- suspend "some_locals" >>
  conj_tac >- suspend "some_inv" >>
  suspend "some_kept"
QED

Resume abi_encode_setup_tail_origin_run[some_frame]:
  irule typed_copy_state_frame_trans >> qexists_tac `s2` >> conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `s1` >>
      reverse conj_tac >- simp[typed_copy_mstore_state_frame] >>
      simp[Abbr `s1`, typed_copy_state_frame_def, typed_copy_frame_def,
        update_var_def, lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
      rpt strip_tac >> metis_tac[]) >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin_run[some_operands]:
  qx_gen_tac `operand` >> strip_tac >>
  `!x. operand = Var x ==> not_fresh_at method_st x` by
    metis_tac[not_fresh_at_mono] >>
  qpat_assum `!op. _ ==> eval_operand op t = eval_operand op s2 /\ _`
    (qspec_then `operand` (drule_then strip_assume_tac)) >>
  qpat_assum `!op. _ ==> eval_operand op (update_var mp _ s) = eval_operand op s /\ _`
    (qspec_then `operand` (drule_then strip_assume_tac)) >>
  `eval_operand operand s2 = eval_operand operand (update_var mp (n2w p + 32w) s) /\
    op_taint tn2 operand = op_taint tn1 operand` by
    (qpat_assum `s2 = _` SUBST1_TAC >> qpat_assum `tn2 = _` SUBST1_TAC >>
     Cases_on `operand` >> simp[NoAsms, eval_operand_def, lookup_var_def,
       op_taint_def, mstore_def, Abbr `s1`, update_var_def]) >>
  asm_rewrite_tac[]
QED

Resume abi_encode_setup_tail_origin_run[some_old_cover]:
  qx_genl_tac [`old`,`n`] >> strip_tac >>
  `old <> dp /\ old <> mp` by metis_tac[] >>
  qpat_assum `!x. x <> dp ==> lookup_var x t = _ /\ _`
    (qspec_then `old` (drule_then strip_assume_tac)) >>
  qpat_assum `!x. x <> mp ==> lookup_var x s1 = _ /\ _`
    (qspec_then `old` (drule_then strip_assume_tac)) >>
  `lookup_var old s2 = lookup_var old s1 /\
    op_taint tn2 (Var old) = op_taint tn1 (Var old)` by
    (qpat_assum `s2 = _` SUBST1_TAC >> qpat_assum `tn2 = _` SUBST1_TAC >>
     simp[NoAsms, lookup_var_def, op_taint_def, mstore_def]) >>
  irule decoderGhostFramePtrTheory.ptr_covers_frame >>
  qexistsl_tac [`G`,`s`,`tn`] >> asm_rewrite_tac[]
QED

Resume abi_encode_setup_tail_origin_run[some_locals]:
  rpt strip_tac >>
  `not_scope_ptr ce es.scopes mp /\ not_scope_ptr ce es.scopes dp` by
    (simp[NoAsms, not_scope_ptr_def] >> metis_tac[]) >>
  `local_ptrs_rel func ce es.scopes s1` by
    (simp_tac (srw_ss()) [Abbr `s1`, local_ptrs_rel_inst_idx] >>
     irule local_ptrs_rel_update_var >> asm_rewrite_tac[]) >>
  `!name b sz. local_region ce es.scopes s1 name b sz ==>
    p+32+32 <= b \/ b+sz <= p+32` by
    (rpt gen_tac >> simp_tac bool_ss [local_region_def] >>
     disch_then (qx_choosel_then [`entry`,`v`,`word`] strip_assume_tac) >>
     `v <> mp` by metis_tac[] >>
     `lookup_var v s = SOME word` by
       (qpat_assum `!x. x <> mp ==> lookup_var x s1 = _ /\ _`
          (qspec_then `v` (drule_then strip_assume_tac)) >>
        qpat_assum `lookup_var v s1 = lookup_var v s` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!name b sz. local_region ce es.scopes s name b sz ==> _`
       (qspecl_then [`name`,`b`,`sz`] mp_tac) >>
     simp[NoAsms, local_region_def, regions_disjoint_def] >>
     impl_tac >- (qexistsl_tac [`entry`,`v`,`word`] >> asm_rewrite_tac[]) >>
     simp[]) >>
  `local_ptrs_rel func ce es.scopes s2` by
    (qpat_assum `s2 = _` SUBST1_TAC >> simp_tac (srw_ss()) [local_ptrs_rel_inst_idx] >>
     irule local_ptrs_rel_mstore >> asm_rewrite_tac[]) >>
  qpat_assum `t = _` SUBST1_TAC >> simp_tac (srw_ss()) [local_ptrs_rel_inst_idx] >>
  irule local_ptrs_rel_update_var >> asm_rewrite_tac[]
QED

Resume abi_encode_setup_tail_origin_run[some_inv]:
  rpt strip_tac >>
  `ghost_inv_at D lo d ce cx es G1 tn1 s1` by
    (qpat_assum `!D d ce cx es. _ ==> ghost_inv_at D lo d ce cx es G1 tn1 s1`
       (qspecl_then [`D`,`d`,`ce`,`cx`,`es`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `local_ptrs_rel func ce es.scopes s1` by
    (simp_tac (srw_ss()) [Abbr `s1`, local_ptrs_rel_inst_idx] >>
     irule local_ptrs_rel_update_var >>
     asm_rewrite_tac[not_scope_ptr_def] >> metis_tac[]) >>
  `ghost_inv_at D lo d ce cx es G1 tn2 s2` by
    (qpat_assum `!D d ce cx es. _ ==> ghost_inv_at D lo d ce cx es G1 tn2 s2`
       (qspecl_then [`D`,`d`,`ce`,`cx`,`es`] mp_tac) >>
     simp_tac bool_ss [] >> impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
         qx_genl_tac [`name`,`rb`,`sz`] >> simp_tac bool_ss [local_region_def] >>
         disch_then (qx_choosel_then [`entry`,`v`,`word`] strip_assume_tac) >>
         `v <> mp` by metis_tac[] >>
         `lookup_var v s = SOME word` by
           (qpat_assum `!x. x <> mp ==> lookup_var x s1 = _ /\ _`
              (qspec_then `v` (drule_then strip_assume_tac)) >>
            qpat_assum `lookup_var v s1 = lookup_var v s` (SUBST1_TAC o SYM) >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `!name b sz. local_region ce es.scopes s name b sz ==> _`
           (qspecl_then [`name`,`rb`,`sz`] mp_tac) >>
         simp_tac bool_ss [local_region_def] >> impl_tac
         >- (qexistsl_tac [`entry`,`v`,`word`] >> asm_rewrite_tac[]) >>
         disch_then ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!D d ce cx es. _ ==> ghost_inv_at D lo d ce cx es G' tn' t`
    (qspecl_then [`D`,`d`,`ce`,`cx`,`es`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED

Resume abi_encode_setup_tail_origin_run[some_kept]:
  rpt strip_tac >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G1 tn1` by
    (first_assum irule >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G1 tn2` by metis_tac[] >>
  first_assum irule >> simp[] >> metis_tac[]
QED

Finalise abi_encode_setup_tail_origin_run

Theorem abi_encode_setup_tail_origin:
  k = (case mid of NONE => 0 | SOME w => 4) /\
  N = 32 + 32 * word_size (maxlen+k) /\
  write_len = (case mid of NONE => 0 | SOME w => 32) /\
  abi_builtin_encode_method_id mid (Var root) a = ((),method_st) /\
  emit_op ADD [Var root;Lit (n2w (32+k))] method_st = (data,ready) /\
  fn_has_code a ready func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ alloca_inv s /\
  lookup_var root s = SOME (n2w p) /\ not_fresh_at a root /\
  ptr_covers G tn root s N /\ lo <= p /\
  p+N <= s.vs_alloca_next /\ p+N < dimword(:256) ==>
  ?dp t G' tn'.
    data = Var dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand data t = SOME (n2w (p+32+k)) /\
    ptr_covers G' tn' dp t (N-(32+k)) /\
    ptr_covers G' tn' root t N /\
    eval_operand (Var root) t = SOME (n2w p) /\ not_fresh_at ready dp /\
    (case mid of NONE => T | SOME w =>
      !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
        mem_word_at (p+32) mem = w << 224) /\
    typed_copy_state_frame a (p+32) write_len s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv t /\ allocas_from lo t /\
    tn'.t_mem = tn.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
      eval_operand op t = eval_operand op s /\
      op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op) /\
    (!x n. not_fresh_at a x /\ ptr_covers G tn x s n ==>
      ptr_covers G' tn' x t n) /\
    (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
    (fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func t) /\
    (!ce es.
      local_ptrs_rel func ce es.scopes s /\
      (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
        not_fresh_at a x) /\
      (!name b sz. local_region ce es.scopes s name b sz ==>
        regions_disjoint (p+32) write_len b sz) ==>
      local_ptrs_rel func ce es.scopes t) /\
    (!D d ce cx es.
      ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
      (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
        not_fresh_at a x) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
      (!name b sz. local_region ce es.scopes s name b sz ==>
        regions_disjoint (p+32) write_len b sz) ==>
      ghost_inv_at D lo d ce cx es G' tn' t) /\
    (!ce es origin G0 tn0 s0.
      ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
      (!x. not_fresh_at origin x ==> not_fresh_at a x) ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G' tn')
Proof
  strip_tac >>
  mp_tac (Q.INST [`explicit` |-> `explicit`, `PG` |-> `PG`]
    abi_encode_setup_tail_origin_run) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`dp`,`t`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl_tac [`dp`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

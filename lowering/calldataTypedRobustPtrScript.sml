(* Typed representations at clean decoder endpoints. *)
Theory calldataTypedRobustPtr
Ancestors calldataDecodePtr calldataWordPtr robustCopyTransportPtr exprSimMemoryTransport
  bodyPtrDefs venomMemProofs list valueEncoding valueEncodingDefs valueEncodingProofs valueEncodingProps
  abiEncoder abiDecoderContract venomInst venomState venomExecSemantics words
  codegenRel contextCodegenRel compileEnv loweringStateRelDefs ptrDiscipline ptrSafeRun fragExec finite_map
  abiDecoderBytes abiDecoderBytesTyped abiCanonicalBytes abiDecoderGuards loweringPosts exprSimDefs exprSimProps
  contractABI vyperValue vyperTyping arithmetic abiDecoderClampedTyped
  abiDecoderCoherence abiDecoderTypedContract abiDecoderWordTyped abiDecoderClamp
  valueEncodingTyping abiDecoderReentryPointer abiDecoderPreObservations abiDecoderReentry
  decoderNavigationPtr

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem clean_footprint_val_in_memory_robust:
  !tv v p mem tainted.
    val_wf tv v /\ val_in_memory tv v p mem /\
    (!i. p <= i /\ i < p + val_footprint tv v ==> i NOTIN tainted) ==>
    !mem'. mem_agree_outside tainted mem mem' ==>
      val_in_memory tv v p mem'
Proof
  rpt strip_tac >> irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `p`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < val_footprint tv v` >>
  `p+j NOTIN tainted` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (p+j) 1 mem = mem_bytes_at (p+j) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem calldata_bytestring_decoder_typed_robust_uniform:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  val_wf tv v /\ val_footprint tv v <= C /\
  (?ordinary. run_inst_seq (emitted_insts sa sb) s = OK ordinary /\
    val_in_memory tv v (w2n dw) ordinary.vs_memory) ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem)
Proof
  strip_tac >> drule_all calldata_bytestring_decoder_prefix_framed_uniform >>
  disch_then (qspec_then `PG`
    (qx_choose_then `s'` (qx_choose_then `G'`
      (qx_choose_then `tn'` strip_assume_tac)))) >>
  `val_in_memory tv v (w2n dw) s'.vs_memory` by gvs[] >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> irule clean_footprint_val_in_memory_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s'.vs_memory`, `tn'.t_mem`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem calldata_canonical_bytestring_typed_robust_uniform:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\
  eval_operand src s = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  LENGTH bs <= m /\
  mem_bytes_at srcpos (LENGTH (enc (contractABI$Bytes NONE) (contractABI$BytesV bs)))
    s.vs_call_ctx.cc_calldata = enc (contractABI$Bytes NONE) (contractABI$BytesV bs) /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\
    eval_operand src s' = SOME (n2w srcpos) /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs)
        (w2n dw) mem)
Proof
  strip_tac >>
  `C = abi_decode_bytes_copy_size m` by simp[abi_decode_bytes_copy_size_def] >>
  `m + 32 <= C` by metis_tac[abi_decoder_bytes_copy_size] >>
  `val_wf (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs)` by
    (simp[val_wf_def, GSYM (cj 2 abi_decoder_bytes_copy_size)] >> decide_tac) >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >>
     asm_simp_tac bool_ss [abi_decode_source_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_bytes_copy_size m < dimword (:256)` by metis_tac[] >>
  drule_all (SRULE [wordsTheory.n2w_w2n, wordsTheory.w2n_lt]
    (Q.INST [`d` |-> `w2n (dw:bytes32)`] abi_decode_bytes_sentinel_sequence)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK ordinary` >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs)
    (w2n dw) ordinary.vs_memory` by
    (irule canonical_bytes_copied_layout >> simp[] >>
     qexistsl_tac [`C`, `srcpos`, `s.vs_call_ctx.cc_calldata`] >>
     gvs[abi_decode_source_def, GSYM (cj 2 abi_decoder_bytes_copy_size)]) >>
  irule calldata_bytestring_decoder_typed_robust_uniform >> simp[] >>
  conj_tac
  >- (simp[val_footprint_def] >> decide_tac) >>
  qexistsl_tac [`LENGTH bs`, `m`] >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  simp[] >> decide_tac
QED

Theorem calldata_bytestring_decoder_typed_robust:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  val_wf tv v /\ val_footprint tv v <= C /\
  (?ordinary. run_inst_seq (emitted_insts sa sb) s = OK ordinary /\
    val_in_memory tv v (w2n dw) ordinary.vs_memory) ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem)
Proof
  strip_tac >>
  drule_all (SRULE [PULL_EXISTS] calldata_bytestring_decoder_typed_robust_uniform) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> gvs[]
QED

Theorem calldata_canonical_bytestring_typed_robust:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\
  eval_operand src s = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  LENGTH bs <= m /\
  mem_bytes_at srcpos (LENGTH (enc (contractABI$Bytes NONE) (contractABI$BytesV bs)))
    s.vs_call_ctx.cc_calldata = enc (contractABI$Bytes NONE) (contractABI$BytesV bs) /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\
    eval_operand src s' = SOME (n2w srcpos) /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs)
        (w2n dw) mem)
Proof
  strip_tac >> drule_all calldata_canonical_bytestring_typed_robust_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[]
QED

Theorem calldata_typed_clamped_word_robust:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD sw s) /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    sa last src (Var p) CALLDATALOAD (Lit 0w) (Lit 0w) 0 sbpos d b cap s /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    abi_decoder_post tv v sb d 32 b cap s s' /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory tv v d mem)
Proof
  strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    abi_decoder_post tv v sb d 32 b cap s t` by
    (`sw = n2w sbpos` by
       (qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac (srw_ss()) [abi_decoder_recursive_pre_def, abi_decoder_pre_def,
          abi_decoder_ranges_def] >> metis_tac[optionTheory.SOME_11]) >>
     gvs[] >> irule (calldata_pos abi_decoder_typed_clamped_word_sequence) >> simp[] >>
     metis_tac[]) >>
  drule_all calldata_clamped_word_prefix_framed >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `s'` (qx_choose_then `G'`
      (qx_choose_then `tn'` strip_assume_tac)))) >>
  `abi_decoder_post tv v sb d 32 b cap s s'` by
    (gvs[] >> metis_tac[abi_decoder_post_inst_idx]) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[] >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def, cj 1 arithmeticTheory.ADD_CLAUSES, abi_decoder_pre_def, abi_decoder_metadata_def]) >>
  `type_to_abi_dec_info sf ce ty = DecPrimWord clamp` by metis_tac[] >>
  drule_all (cj 2 abi_decoder_primitive_cases) >> strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `val_footprint tv v <= 32` by metis_tac[val_footprint_le] >>
  `d = w2n dw` by
    (qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_decoder_ranges_def] >> strip_tac >>
     `d < dimword (:256)` by decide_tac >>
     `dw = n2w d` by
       (qpat_x_assum `eval_operand (Var p) s = SOME dw` mp_tac >>
        qpat_assum `eval_operand (Var p) s = SOME (n2w d)`
          (fn th => rewrite_tac[th]) >> simp[]) >>
     simp[]) >>
  rpt strip_tac >> irule clean_footprint_val_in_memory_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s'.vs_memory`, `tn'.t_mem`] >>
  fs[abi_decoder_post_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem calldata_typed_unclamped_word_robust:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord NoClamp) sa = ((),sb) /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord NoClamp) av v
    sa last src (Var p) CALLDATALOAD (Lit 0w) (Lit 0w) 0 sbpos d b cap s /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    abi_decoder_post tv v sb d 32 b cap s s' /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory tv v d mem)
Proof
  strip_tac >> irule calldata_typed_clamped_word_robust >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[abi_decoder_clamp_valid_def]
QED

(* Ordinary reentry and ghost execution share the original, unpruned state.
   The second endpoint differs only in its instruction index. *)
Theorem calldata_primitive_reentry_ptr_endpoint:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecPrimWord clamp) av v
    st last src (Var p) CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ptr_covers G tn p initial 32 /\ op_taint tn src = {} /\
  fn_has_code st st' fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual endpoint G' tn'.
    run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    endpoint = actual with vs_inst_idx := LENGTH st'.cs_current_insts /\
    ~endpoint.vs_halted /\ endpoint.vs_current_bb = st'.cs_current_bb /\
    endpoint.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ptr_covers G' tn' p endpoint 32 /\
    (!i. d <= i /\ i < d + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' endpoint) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn initial)
Proof
  strip_tac >> drule_all (calldata_pos abi_decoder_primitive_reentry_sequence) >> strip_tac >>
  drule (calldata_pos abi_decoder_pre_observations) >> strip_tac >>
  `eval_operand (Var p) initial = SOME (n2w d) /\
   eval_operand src initial = SOME (n2w sb) /\ d < dimword (:256)` by
    (fs[abi_decoder_ranges_def] >> decide_tac) >>
  `not_fresh_at st p /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  drule_all calldata_word_overwrite_prefix >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `run_inst_seq _ _ = OK (_ with vs_inst_idx := _)` kall_tac >>
  qexistsl_tac [`actual`, `s'`, `G'`, `tn'`] >> simp[]
QED

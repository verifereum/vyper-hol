(* Typed representations at clean decoder endpoints. *)
Theory calldataTypedRobustPtr
Ancestors calldataDecodePtr calldataWordPtr robustCopyTransportPtr exprSimMemoryTransport
  bodyPtrDefs venomMemProofs list valueEncoding valueEncodingProofs valueEncodingProps
  abiEncoder abiDecoderContract venomInst venomState venomExecSemantics words
  codegenRel contextCodegenRel compileEnv ptrDiscipline ptrSafeRun fragExec finite_map
  abiDecoderBytes abiDecoderBytesTyped abiCanonicalBytes abiDecoderGuards exprSim
  contractABI vyperValue vyperTyping arithmetic

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

Theorem calldata_bytestring_decoder_typed_robust:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
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
  strip_tac >> drule_all calldata_bytestring_decoder_prefix_framed >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `s'` (qx_choose_then `G'`
      (qx_choose_then `tn'` strip_assume_tac)))) >>
  `val_in_memory tv v (w2n dw) s'.vs_memory` by gvs[] >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> irule clean_footprint_val_in_memory_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s'.vs_memory`, `tn'.t_mem`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem calldata_canonical_bytestring_typed_robust:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
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
  drule_all abi_decode_bytes_sentinel_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK ordinary` >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs)
    (w2n dw) ordinary.vs_memory` by
    (irule canonical_bytes_copied_layout >> simp[] >>
     qexistsl_tac [`C`, `srcpos`, `s.vs_call_ctx.cc_calldata`] >>
     gvs[abi_decode_source_def, GSYM (cj 2 abi_decoder_bytes_copy_size)]) >>
  irule calldata_bytestring_decoder_typed_robust >> simp[] >>
  conj_tac
  >- (simp[val_footprint_def] >> decide_tac) >>
  qexistsl_tac [`LENGTH bs`, `m`] >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  simp[] >> decide_tac
QED

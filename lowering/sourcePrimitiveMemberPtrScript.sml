(* Physical observations of the same primitive execution used by the ghost port. *)
Theory sourcePrimitiveMemberPtr
Ancestors sourceWordDecoderPtr sourceBytesRepresentation sourceEncodingLayout
  decoderMemberPrefixPtr abiDecoderClampedWord ghostPcTransportPtr
  abiDecoderContract abiDecoderBytes compileEnv venomState words
  abiDecoderCoherence abiDecoderDynamicLoopSetup ptrDiscipline abiDecoderWordTyped
  abiDecoderMemberSetup exprLowering vyperABI vyperTyping abiDecoderClamp
  fragExec list finite_map pred_set arithmetic abiCanonicalBytes bodyPtrDefs
  decoderCalldataShell exprLoweringProps instIdxIndep sourceEncodingWindows
  vyperABIRoundtrip abiDecodeRanges

(* The calldata instance of the position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`] th);

Theorem clamped_word_endpoint_physical_frame:
  compile_abi_decode_to_buf dst src opc (Lit 0w) hi (DecPrimWord clamp) sa = ((),sb) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w srcpos) /\
  eval_operand dst s = SOME (n2w d) /\
  srcpos < dimword (:256) /\ d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w srcpos : bytes32) s) /\
  fresh_vars_wrt sa s /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := k) ==>
  abi_decode_frame d 32 s t /\ fresh_vars_wrt sb t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all (calldata_pos abi_decoder_clamped_word_copied_window) >>
  strip_tac >> gvs[] >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def] >> gvs[]
QED

Theorem bytestring_endpoint_physical_frame:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (Lit 0w) (DecBytestring n) sa = ((),sb) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME sw /\
  eval_operand dst s = SOME dw /\ abi_decode_load opc sw s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt sa s /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := k) ==>
  abi_decode_frame (w2n dw) (abi_decode_bytes_copy_size n) s t /\
  fresh_vars_wrt sb t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w (w2n sw)) /\
   eval_operand dst s = SOME (n2w (w2n dw)) /\
   abi_decode_load opc (n2w (w2n sw):bytes32) s = n2w cnt /\
   w2n sw < dimword (:256) /\ w2n dw < dimword (:256)` by
    simp[wordsTheory.w2n_lt] >>
  drule_all abi_decode_bytes_sentinel_sequence >> strip_tac >>
  gvs[] >> gvs[abi_decode_frame_def, fresh_vars_wrt_def] >> gvs[]
QED

(* One physical/ghost boundary for both nonrecursive decoder descriptors. *)
Theorem source_primitive_decoder_ptr:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w) ei sa = ((),sb) /\
  abi_decoder_coherent ce env sf ty tv /\ type_to_abi_dec_info sf ce ty = ei /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  ((?clamp. ei = DecPrimWord clamp /\ is_word_type ty /\ C = 32) \/
   (?m. ei = DecBytestring m /\ C = abi_decode_bytes_copy_size m /\ m < dimword (:256))) /\
  C < dimword (:256) /\
  eval_operand (Var p) s = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand src s = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\ op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ptr_covers H u p t C /\
    val_in_memory tv v d t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v d mem) /\
    abi_decode_frame d C s t /\ fresh_vars_wrt sb t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac
  >- suspend "word"
  >> suspend "bytes"
QED

Resume source_primitive_decoder_ptr[word]:
  gvs[] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) s)` by
    (irule coherent_source_word_clamp >> simp[abi_decode_source_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`sw` |-> `n2w srcpos : bytes32`]
    calldata_source_word_ptr_endpoint_uniform)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`] clamped_word_endpoint_physical_frame)) >>
  strip_tac >> qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[] >>
  gvs[w2n_n2w, LESS_MOD]
QED

Resume source_primitive_decoder_ptr[bytes]:
  gvs[] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  drule_all (SRULE [GSYM abi_decode_bytes_copy_size_def]
    (Q.INST [`C` |-> `abi_decode_bytes_copy_size m`]
      calldata_source_bytes_ptr_endpoint_uniform)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all coherent_source_bytes_representation >> strip_tac >>
  `mem_bytes_at srcpos (LENGTH (enc (contractABI$Bytes NONE) (contractABI$BytesV bs)))
    (abi_decode_source CALLDATALOAD s) = enc (contractABI$Bytes NONE) (contractABI$BytesV bs)` by
    gvs[abi_decode_source_def] >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >> simp[]) >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`] bytestring_endpoint_physical_frame)) >>
  strip_tac >> qexistsl_tac [`s'`, `G'`, `tn'`] >>
  gvs[w2n_n2w, LESS_MOD, abi_decode_bytes_copy_size_def, mem_agree_outside_def]
QED

Finalise source_primitive_decoder_ptr

(* The prepared-state certificate concerns only navigation, never the child.
   Both the source value and the ghosts below are produced by execution. *)
Theorem source_primitive_member_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    ei mid = ((),sb) /\
  lookup_var root s = SOME a /\ not_fresh_at sa root /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ w2n a + vo < dimword (:256) /\ C < dimword (:256) /\
  run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
  abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt mid r /\
  r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
  eval_operand (FST ops) r = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  abi_decoder_coherent ce env sf ty tv /\ type_to_abi_dec_info sf ce ty = ei /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  ((?clamp. ei = DecPrimWord clamp /\ is_word_type ty /\ C = 32) \/
   (?m. ei = DecBytestring m /\ C = abi_decode_bytes_copy_size m /\ m < dimword (:256))) /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  fn_has_code sa mid fn /\ fn_has_code mid sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u q.
    SND ops = Var q /\
    run_inst_seq (emitted_insts mid sb) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    run_inst_seq (emitted_insts sa mid ++ emitted_insts mid sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ptr_covers H u q t C /\
    val_in_memory tv v (w2n a + vo) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n a + vo) mem) /\
    abi_decode_frame (w2n a + vo) C s t /\ fresh_vars_wrt sb t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  gnvs[lookup_var_def] >>
  `eval_operand (Var q) r = SOME (n2w (w2n a + vo))` by
    simp[eval_operand_def, lookup_var_def] >>
  `allocas_from lo r /\ ~r.vs_halted` by
    (gvs[abi_decoder_address_frame_def, allocas_from_def] >> gvs[]) >>
  `mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av` by simp[] >>
  `w2n a + vo < dimword (:256)` by decide_tac >>
  drule_all (SRULE [] (Q.INST [`ei` |-> `type_to_abi_dec_info sf ce ty`]
    source_primitive_decoder_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at mid x` by
    (drule abi_decode_member_setup_counters >> strip_tac >>
     simp[not_fresh_at_def] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
     Cases_on `dyn` >> gvs[] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sb)` by
    (qpat_x_assum `(?clamp. _) \/ _` strip_assume_tac >> gvs[]
     >- (drule_all (SRULE [abi_decode_source_opcode_def]
           (Q.INST [`opc` |-> `CALLDATALOAD`] abi_decoder_clamped_word_shape)) >>
         simp[EVERY_MEM] >> metis_tac[]) >>
     drule calldata_bytes_allocation_shape >> simp[EVERY_MEM] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa mid ++ emitted_insts mid sb) s =
    OK (t with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `run_inst_seq (emitted_insts sa mid) _ = _`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts mid sb` (fn th => rewrite_tac[th])) >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  qexistsl_tac [`t`, `H'`, `u'`] >>
  gvs[abi_decoder_address_frame_def, abi_decode_frame_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `r.vs_inst_idx = _` (fn th => fs[GSYM th]) >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => fs[GSYM th]) >>
  metis_tac[]
QED

(* A real indexed tuple child: forward conversion supplies its window and
   exact value.  No ABI has_types premise is used. *)
Theorem canonical_source_tuple_primitive_member_ptr:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ vyper_to_abi_list env tys vs = SOME avs /\
  ats = MAP (vyper_to_abi_type env) tys /\ i < LENGTH tys /\
  mem_bytes_at cdsbase (LENGTH (enc (Tuple ats) (ListV avs))) r.vs_call_ctx.cc_calldata =
    enc (Tuple ats) (ListV avs) /\
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    ei mid = ((),sb) /\
  lookup_var root s = SOME a /\ not_fresh_at sa root /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + C <= cap /\ w2n a + vo < dimword (:256) /\ C < dimword (:256) /\
  run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
  abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt mid r /\
  r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
  eval_operand (FST ops) r = SOME (n2w (cdsbase + abi_tuple_child_offset ats avs i)) /\
  cdsbase + abi_tuple_child_offset ats avs i < dimword (:256) /\
  type_to_abi_dec_info sf ce (EL i tys) = ei /\
  ((?clamp. ei = DecPrimWord clamp /\ is_word_type (EL i tys) /\ C = 32) \/
   (?m. ei = DecBytestring m /\ C = abi_decode_bytes_copy_size m /\ m < dimword (:256))) /\
  fn_has_code sa mid fn /\ fn_has_code mid sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    run_inst_seq (emitted_insts sa mid ++ emitted_insts mid sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    val_in_memory (EL i tvs) (EL i vs) (w2n a + vo) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (EL i tvs) (EL i vs) (w2n a + vo) mem) /\
    abi_decode_frame (w2n a + vo) C s t /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all coherent_source_list_head_lengths >> strip_tac >>
  `i < LENGTH (MAP (vyper_to_abi_type env) tys)` by simp[] >>
  `mem_bytes_at cdsbase
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    r.vs_call_ctx.cc_calldata =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)` by metis_tac[] >>
  drule_all structural_tuple_indexed_source >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >>
  `abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
   value_has_type (EL i tvs) (EL i vs) /\
   vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  gnvs[EL_MAP] >>
  `vyper_to_abi env (EL i tys) (EL i vs) = SOME (EL i avs)` by simp[] >>
  `vo + C <= cap /\ w2n a + vo < dimword (:256)` by decide_tac >>
  `run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx)` by simp[] >>
  drule_all (SRULE [] (Q.INST [`ty` |-> `EL i tys`, `ei` |-> `type_to_abi_dec_info sf ce (EL i tys)`]
    source_primitive_member_ptr)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `u`] >> simp[] >>
  pure_once_rewrite_tac[ADD_COMM] >> asm_rewrite_tac[]
QED

(* Zero head and destination offsets still execute two fresh ADDs.  In
   particular navigation is not assumed to be an identity on registers. *)
Theorem zero_offset_member_setup_certificate[local]:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w) F 0 0 sa = (ops,mid) /\
  eval_operand src s = SOME (n2w srcpos) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var dst /\ fresh_vars_wrt mid s ==>
  ?r. run_inst_seq (emitted_insts sa mid) s = OK r /\
    eval_operand (FST ops) r = SOME (n2w srcpos) /\
    eval_operand (SND ops) r = SOME (n2w d) /\
    fresh_vars_wrt mid r /\ abi_decoder_address_frame sa.cs_next_var s r
Proof
  strip_tac >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`dyn` |-> `F`, `opc` |-> `CALLDATALOAD`, `limit_st` |-> `st'`]
      (calldata_pos abi_decode_member_setup_reentry))) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED

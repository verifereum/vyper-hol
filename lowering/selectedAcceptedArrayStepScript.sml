(* Source-exact transition of an installed nonbulk array loop. *)
Theory selectedAcceptedArrayStep
Ancestors
  selectedAcceptedInterfaces calldataArrayRawCallsite calldataMemberResourceFrame
  decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr robustCopyTransportPtr
  fragGasOriginPtrExec vyperCalldataProps vyperCalldata words arithmetic
  calldataSourceCorrespondence calldataDynStep decoderArraySetupPtr
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderExecution
  entryDecoderSetupEndpoint entryDecoderStateFrame calldataFiniteTransport
  compileEnv venomState venomExecSemantics abiDecoderFrame fragGasOriginPtr
  exprLoweringProps loweringStateRelDefs ptrDiscipline abiDecoderReentry
  codegenRel instIdxIndep emitHelperProps abiEncoder finite_map pred_set list
  bodyPtrDefs venomInst abiDecoderContract

(* The index computation is word arithmetic even when the ABI head wraps. *)
Theorem selected_array_source_word:
  (if tv_abi_dynamic tv then
    n2w (sb + 32 + w2n (abi_decode_load CALLDATALOAD
      (n2w (sb + 32 + ofs) : bytes32) s))
   else n2w (sb + 32 + ofs)) =
  (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
    (cd_at F (w2n (n2w sb:bytes32)) 32) ofs) : bytes32)
Proof
  Cases_on `tv_abi_dynamic tv` >>
  simp[cd_member_ptr_def, cd_at_def, w2n_n2w, MOD_PLUS, calldata_decode_load_word]
QED

Theorem selected_array_source_cons:
  cd_decode_elems F cd tv b i (SUC n) = SOME xs ==>
  ?x rest. xs = x::rest /\
    cd_decode F cd tv (cd_member_ptr F cd tv b (i*tv_abi_size tv)) = SOME x /\
    cd_decode_elems F cd tv b (SUC i) n = SOME rest
Proof
  simp[Once cd_decode_def, AllCaseEqs(), ADD1] >> metis_tac[]
QED

(* The body setup runs at the installed cursor; its source need not be a
   nonwrapping ABI header and the counter can be a replay allocation. *)
Theorem selected_array_setup[local]:
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  dec_info_needs_offset di = tv_abi_dynamic tv /\
  lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\ j < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ lookup_var root s = SOME (n2w d) /\
  ptr_covers G tn q s 32 /\ ptr_covers G tn root s span /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  not_fresh_at st q /\ not_fresh_at st root /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  32+j*type_memory_size tv+type_memory_size tv <= span /\
  d+32+j*type_memory_size tv < dimword (:256) /\ type_memory_size tv < dimword (:256) /\
  ready.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code st ready fn /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a H u child.
    ~a.vs_halted /\ a.vs_current_bb = ready.cs_current_bb /\
    a.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) a = SOME (n2w j) /\
    eval_operand (FST (SND ops)) a = SOME
      (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (cd_at F (w2n (n2w sb:bytes32)) 32) (j*tv_abi_size tv))) /\
    eval_operand (Var child) a = SOME (n2w (d+32+j*type_memory_size tv)) /\
    SND (SND ops) = Var child /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (Var child) /\
    ptr_covers H u child a (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    op_taint u (FST (SND ops)) = {} /\ op_prov H (FST (SND ops)) = NONE /\
    fresh_vars_wrt limit a /\ entry_decoder_obs s a /\
    a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
    a.vs_alloca_next = s.vs_alloca_next /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op a = eval_operand op s) /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,H,u))
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand (Var root) s = SOME (n2w d) /\
   mload (w2n (n2w slot : bytes32)) s = n2w j` by
    (simp[eval_operand_def, w2n_n2w] >> fs[]) >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule_all calldata_array_element_setup_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK raw` >>
  `LENGTH (emitted_insts st ready) + s.vs_inst_idx =
    LENGTH ready.cs_current_insts` by fs[inst_extends_def] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op raw = eval_operand op s` by
    (rpt strip_tac >> drule_all entry_element_setup_total_frame >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule entry_element_setup_reentry_code >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH ready.cs_current_insts`, `HG`, `u`, `child`] >>
  pure_once_rewrite_tac [GSYM selected_array_source_word] >>
  fs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def]
QED

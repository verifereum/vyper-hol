(* Canonical primitive decoder endpoints, with actual execution observations. *)
Theory entryReachBodyCanonicalWordEndpoint
Ancestors
  entryCanonicalWordExecution
  valueEncodingDefs loweringStateRelDefs entryReachBodyRecursiveInterface entryReachBodyOperationalPath
  entryReachBodySequenceObservations entryReachBodyExactArrayLoop abiDecoderPrimitiveMemory
  abiDecoderPrimitiveCaller
  abiDecoderClampedWord abiDecoderWordTyped abiEncoder ctorAbiActualAlloc abiDecoderContract
  abiEncoderRegisteredEffect entryReachBodyOwnedRegion entryReachBodyScratchSet
  abiAllocationHistory allocaFrontierBound allocaBudgetProps venomMemDefs
  venomExecSemantics venomInstProps venomState venomInst emitHelperProps exprLoweringProps
  compileEnv emitHelper words list rich_list arithmetic

(* The owned word endpoint, given only that the loaded word passes the clamp
   and that the copied word lays out the value. *)
Theorem entry_canonical_word_memory_endpoint:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s) /\
  (!mem. mem_bytes_at d 32 mem = mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) ==>
     val_in_memory tv v d mem) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce ty) s /\
  entry_scratch_ready sites b cap s ==>
  ?t. val_in_memory tv v d t.vs_memory /\ entry_decode_path ctx fn s t /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\ entry_scratch_ready sites b cap t /\
    alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_bytes ce ty) t /\
    abi_encoder_registered_effect child_sites [(d,type_memory_bytes ce ty)] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all entry_canonical_word_memory_execution >>
  metis_tac[]
QED

Theorem entry_canonical_word_owned_endpoint:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv (DecPrimWord clamp) av v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce ty) s /\
  entry_scratch_ready sites b cap s ==>
  ?t. val_in_memory tv v d t.vs_memory /\ entry_decode_path ctx fn s t /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\ entry_scratch_ready sites b cap t /\
    alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_bytes ce ty) t /\
    abi_encoder_registered_effect child_sites [(d,type_memory_bytes ce ty)] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_primitive_clamp >> strip_tac >>
  `!mem. mem_bytes_at d 32 mem = mem_bytes_at sb 32 (abi_decode_source CALLDATALOAD s) ==>
     val_in_memory tv v d mem` by
    metis_tac[abi_decoder_primitive_canonical_layout] >>
  drule_all entry_canonical_word_memory_endpoint >>
  disch_then (qspec_then `child_sites` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

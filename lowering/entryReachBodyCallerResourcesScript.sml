(* Actual registration compiler-shell projections; no execution hypotheses. *)
Theory entryReachBodyCallerResources
Ancestors
  entryReachBodyPackageAlignment calldataRegistration calldataRegistrationExec actualRegistrationCode
  abiDecoderContract
  abiDecoderCode abiDecoderAppend actualDecoderSites entryReachBodyInitialResources
  entryReachBodyRegistrationSingleton loweringHalt exprSimAccounts
  compileVyper compileEnv moduleLowering abiEncoderWindowContract fragExec
  finite_map words list arithmetic

Theorem caller_address_extends[local]:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
  (if dyn then ?offset after_load.
    emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
    emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) ==>
  cs_extends allocated first
Proof
  strip_tac >> Cases_on `dyn` >> gvs[] >>
  imp_res_tac emit_op_extends_next_var >> metis_tac[cs_extends_trans]
QED

Theorem caller_singleton_compiler_shell:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (cef,last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
  (prim ==> ?c. info = DecPrimWord c) /\ fn_has_code st last fn ==>
  ?buf allocated head after_head src first.
    compile_alloc_buffer n st = (buf,allocated) /\
    FLOOKUP cef.ce_vars name = SOME (PtrVar buf.buf_operand n) /\
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
    (if dyn /\ ~prim then ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
     else src = head /\ first = after_head) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) info first = ((),last) /\
    fn_has_code st allocated fn /\ fn_has_code allocated first fn /\ fn_has_code first last fn /\
    abi_decoder_code first last /\
    cs_extends st allocated /\ cs_extends allocated first /\ cs_extends first last
Proof
  strip_tac >> drule_all register_singleton_allocated_boundary >> strip_tac >>
  `FLOOKUP cef.ce_vars name = SOME (PtrVar buf.buf_operand n)` by simp[FLOOKUP_UPDATE] >>
  `var_location_decode_operand (PtrVar buf.buf_operand n) = SOME buf.buf_operand` by
    simp[var_location_decode_operand_def] >>
  drule_all registration_decoder_prelude >> strip_tac >>
  `cs_extends st allocated` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends allocated first` by (irule caller_address_extends >> metis_tac[]) >>
  `cs_extends first last` by
    metis_tac[cs_appends_def, cj 1 cs_appends_abi_decode_mutual] >>
  `abi_decoder_code first last` by
    (irule abi_decoder_to_buf_code >> goal_assum (drule_at Any) >>
     simp[abi_decode_source_opcode_def]) >>
  qexistsl_tac [`buf`, `allocated`, `head`, `after_head`, `src`, `first`] >> simp[] >>
  `cs_extends allocated last` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  metis_tac[fn_has_code_split]
QED

(* The strict numerical bound comes from the lowering acceptance gate,
   not from finiteness of the scratch-site set. *)
Theorem caller_runtime_allocation_budget:
  lower_vyper_runtime_unit tops policy = SOME unit ==>
  unit_alloca_budget unit.cu_context < dimword (:256)
Proof
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rw[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  drule vyperCompilerTheory.run_lowering_alloca_budget >> simp[]
QED


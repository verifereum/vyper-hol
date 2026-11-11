(* Compiler-only certificates for the actual selected registration slot. *)
Theory entryReachBodyRegistrationSlotCertificate
Ancestors
  entryReachBodyDecoderWindowCertificate
  entryReachBodyPackageAlignment abiDecoderCounters abiDecoderCode abiDecoderContract
  entryReachBodyDecoderIdCoverageCompile
  actualDecoderPackaging actualAllocExec loweringHalt calldataRegistrationExec
  abiDecoderPrimitiveCaller abiEncoderWindowContract loweringShapeDefs
  compileEnv compileVyper list pred_set words arithmetic entryReachBodyCallerResources

Theorem entry_selected_prefix_descriptor:
  set_external_package_target target
    (package_external_fn tops T keys
      (mut,F,raw,name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce (TAKE i pos) off st = (next,last) /\
  i < LENGTH args /\ EL i pos = (arg_name,prim,dyn,sz,info) /\
  abi_decoder_coherent next env next.ce_struct_fields (SND (EL i args)) tv ==>
  prim = is_word_type (SND (EL i args)) /\
  info = type_to_abi_dec_info next.ce_struct_fields next (SND (EL i args)) /\
  (prim ==> ?c. info = DecPrimWord c)
Proof
  strip_tac >> drule entry_runtime_package_layout >> strip_tac >>
  `build_positional_arg ce (EL i args) = (arg_name,prim,dyn,sz,info)` by
    gvs[build_positional_args_def, EL_MAP] >>
  Cases_on `EL i args` >> fs[] >>
  drule_all entry_prefix_descriptor >> strip_tac >> simp[] >>
  metis_tac[calldataRegistrationTheory.word_type_decoder_primitive]
QED

Theorem entry_packaged_slot_scratch:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info last0 = ((),last) /\
  cs_extends last entry_end /\
  fn = mk_raw_function "__entry" (all_blocks entry_end) /\
  fn_inst_ids_distinct fn ==>
  (!id. id IN window_alloca_sites fn (abi_decoder_ids last0.cs_next_id last.cs_next_id) ==>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) /\
  (!inst. MEM inst (fn_insts fn) /\
    inst.inst_id IN window_alloca_sites fn (abi_decoder_ids last0.cs_next_id last.cs_next_id) ==>
      alloca_size inst = 32)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all entry_decoder_to_buf_id_coverage >> strip_tac >>
  irule entry_decoder_window_scratch_sizes >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> irule external_phase_decoder_owned >>
  goal_assum (drule_at Any) >> simp[decoder_code_member_state_insts]
QED

Theorem entry_slot_compiler_counters:
  compile_alloc_buffer n st = (buf,allocated) /\
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
  (if dyn then ?offset after_load.
    emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
    emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w) info first = ((),last) /\
  last.cs_next_var <= limit.cs_next_var ==>
  st.cs_next_id < first.cs_next_id /\ first.cs_next_id <= last.cs_next_id /\
  st.cs_next_var <= first.cs_next_var /\ first.cs_next_var <= last.cs_next_var /\
  first.cs_next_var <= limit.cs_next_var /\
  abi_decoder_operand_live last.cs_next_var buf.buf_operand /\
  cs_extends first last /\
  st.cs_next_id NOTIN abi_decoder_ids first.cs_next_id last.cs_next_id /\
  st.cs_next_id NOTIN window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id) /\
  FINITE (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all registration_address_prelude_bounds >> strip_tac >>
  `ci_mono first last` by
    metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_compile_abi_decode, pairTheory.SND] >>
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  `abi_decoder_operand_live allocated.cs_next_var buf.buf_operand` by
    metis_tac[actual_alloc_buffer_live] >>
  `abi_decoder_operand_live last.cs_next_var buf.buf_operand` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `allocated.cs_next_var` >> simp[] >> decide_tac) >>
  `window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id) SUBSET
    abi_decoder_ids first.cs_next_id last.cs_next_id` by
    simp[window_alloca_sites_subset] >>
  `FINITE (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))` by
    metis_tac[pred_setTheory.SUBSET_FINITE, abiDecoderAllocationTheory.abi_decoder_ids_finite] >>
  gvs[abiDecoderAllocationTheory.abi_decoder_ids_def, window_alloca_sites_def] >> decide_tac
QED

Theorem entry_selected_slot_allocation:
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops T keys
      (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce (TAKE i pos) 4 start = (cei,st) /\
  compile_register_positional_args cei [EL i pos] off st = (cei1,last) /\
  fn_has_code st last fn /\ i < LENGTH args ==>
  ?tv name prim dyn sz info buf allocated head after_head src first.
    EL i pos = (name,prim,dyn,sz,info) /\ name = FST (EL i args) /\
    prim = is_word_type (SND (EL i args)) /\
    info = type_to_abi_dec_info cei.ce_struct_fields cei (SND (EL i args)) /\
    abi_decoder_coherent cei (type_env tops) cei.ce_struct_fields (SND (EL i args)) tv /\
    evaluate_type (type_env tops) (SND (EL i args)) = SOME tv /\
    compile_alloc_buffer (type_memory_size tv) st = (buf,allocated) /\
    FLOOKUP cei1.ce_vars name = SOME (PtrVar buf.buf_operand (type_memory_size tv)) /\
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
    (if dyn /\ ~prim then ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
     else src = head /\ first = after_head) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w) info first = ((),last) /\
    fn_has_code st allocated fn /\ fn_has_code allocated first fn /\ fn_has_code first last fn /\
    abi_decoder_code first last /\
    cs_extends st allocated /\ cs_extends allocated first /\ cs_extends first last
Proof
  strip_tac >> drule_all entry_selected_indexed_metadata >> strip_tac >>
  drule_all entry_selected_prefix_descriptor >> strip_tac >>
  drule_all entry_selected_indexed_location >> strip_tac >>
  gvs[] >>
  drule_all entryReachBodyCallerResourcesTheory.caller_singleton_compiler_shell >> simp[]
QED

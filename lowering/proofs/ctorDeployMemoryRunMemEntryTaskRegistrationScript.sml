Theory ctorDeployMemoryRunMemEntryTaskRegistration
Ancestors
  ctorDeployMemoryRunMemEntryPrefix ctorDeployMemoryRunMemEntryPhaseAdapters
  ctorDeployMemoryRunMemEntryShiftedRegistration ctorDeployMemoryRunMemEntrySupport
  ctorSourceInputs abiDecoderCoherence compileVyper supportedProgram vyperInterpreter
  contextProps context emitHelperProps emitHelper fragExec compileEnv
  venomInst venomState venomExecSemantics list rich_list fragExecMem codegenRel exprLoweringProps

Theorem ctor_task_payable_raw:
  emit_op CALLVALUE [] st0 = (cv,st1) /\
  emit_op ISZERO [cv] st1 = (nv,st2) /\
  emit_void ASSERT [nv] st2 = ((),st3) /\
  initial.vs_call_ctx.cc_callvalue = 0w ==>
  ?x y. run_inst_seq (emitted_insts st0 st3) initial =
    OK (update_var y 1w (update_var x 0w initial))
Proof
  strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, run_inst_seq_def, step_inst_base_def,
       mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
       exec_read0_def, exec_pure1_def, bool_to_word_def] >>
  qexistsl [`STRING #"%" (toString st0.cs_next_var)`,
    `STRING #"%" (toString (st0.cs_next_var + 1))`] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def]
QED

Theorem ctor_task_payable_exact:
  emit_op CALLVALUE [] st0 = (cv,st1) /\
  emit_op ISZERO [cv] st1 = (nv,st2) /\
  emit_void ASSERT [nv] st2 = ((),st3) /\
  initial.vs_call_ctx.cc_callvalue = 0w /\
  run_inst_seq (emitted_insts st0 st3) initial = OK raw /\
  actual = raw with vs_inst_idx := LENGTH st3.cs_current_insts ==>
  ?x y. actual = (update_var y 1w (update_var x 0w initial)
    with vs_inst_idx := LENGTH st3.cs_current_insts)
Proof
  strip_tac >> drule_all ctor_task_payable_raw >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem ctor_task_registration_metadata:
  package_constructor tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (ce_pack,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
  ce0 = (ce_pack with ce_imm_alloca := imm) /\
  contract_namespaces_ok T [((NONE:num option),tops)] /\
  EVERY (assignable_type (type_env tops)) (MAP SND fargs) /\
  ALL_DISTINCT (MAP FST fargs) /\
  bind_arguments (type_env tops) fargs vals = SOME scope /\
  vyper_to_abi_list (type_env tops) (MAP SND fargs) vals = SOME avs /\
  EVERY (supported_value_type tops) (MAP SND fargs) /\
  fn_allocs_ok tops (mut,nr,rr,fname,fargs,dflts,ret,fbody) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ==>
  pos_args = build_positional_args ce0 fargs /\
  LENGTH avs = LENGTH fargs /\
  EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
  (!i. i < LENGTH fargs ==>
    ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
      val_wf entry.type entry.value /\
      type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
      abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
        (SND (EL i fargs)) entry.type /\
      abi_decoder_metadata ce0 (type_env tops) (SND (EL i fargs)) entry.type
        (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
        (EL i avs) entry.value) /\
  (!func initial. local_ptrs_rel func ce0 [scope] initial)
Proof
  strip_tac >> drule_all constructor_bound_source_inputs >> strip_tac >>
  asm_rewrite_tac[] >> qx_gen_tac `i` >> strip_tac >>
  drule_all constructor_bound_abi_inputs >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH fargs ==> ?entry. _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> drule_all abi_decoder_coherent_root_metadata >> simp[]
QED

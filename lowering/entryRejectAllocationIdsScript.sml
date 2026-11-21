(* The entry assembler bounds the IDs of all ALLOCA instructions it emits. *)
Theory entryRejectAllocationIds
Ancestors
  groupedEntryCounters compileExprAllocaFresh compilerInstructionSuffix abiDecoderCode abiDecoderCounters
  moduleLowering loweringShapeDefs exprLoweringProps
  calldataRegistrationExec stmtLoweringMono emitHelper context venomInst
  compileEnv exprLowering abiEncoder actualDecoderPackaging pair list
Libs monadsyntax

Definition entry_alloca_ids_def:
  entry_alloca_ids sa sb <=>
    sa.cs_next_id <= sb.cs_next_id /\
    !i. MEM i (state_insts sb) /\ i.inst_opcode = ALLOCA ==>
      MEM i (state_insts sa) \/ i.inst_id < sb.cs_next_id
End

Theorem entry_ids_trans[local]:
  entry_alloca_ids sa sb /\ entry_alloca_ids sb sc ==> entry_alloca_ids sa sc
Proof
  rw[entry_alloca_ids_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem entry_ids_bind[local]:
  (!s. entry_alloca_ids s (SND (m s))) /\
  (!v s. entry_alloca_ids s (SND (k v s))) ==>
  entry_alloca_ids s (SND (comp_bind m k s))
Proof
  rw[comp_bind_def] >> pairarg_tac >> simp[] >>
  irule entry_ids_trans >> metis_tac[SND]
QED

Theorem entry_ids_ignore[local]:
  (!s. entry_alloca_ids s (SND (m s))) /\
  (!s. entry_alloca_ids s (SND (k s))) ==>
  entry_alloca_ids s (SND (comp_ignore_bind m k s))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >> irule entry_ids_bind >> simp[]
QED

Theorem entry_ids_suffix[local]:
  ci_mono sa sb /\
  EVERY (\i. i.inst_opcode = ALLOCA ==> i.inst_id < sb.cs_next_id)
    (added_insts sa sb) ==> entry_alloca_ids sa sb
Proof
  strip_tac >>
  `state_insts sb = state_insts sa ++ added_insts sa sb` by
    metis_tac[state_insts_cs_extends, ci_mono_def] >>
  fs[entry_alloca_ids_def, ci_mono_def, EVERY_MEM] >> metis_tac[]
QED

Theorem entry_ids_emit[local]:
  entry_alloca_ids s (SND (emit_op opc ops s)) /\
  entry_alloca_ids s (SND (emit_void opc ops s)) /\
  entry_alloca_ids s (SND (emit_inst opc ops outs s))
Proof
  rpt conj_tac
  >- (Cases_on `emit_op opc ops s` >>
      drule added_insts_emit_op >> strip_tac >>
      irule entry_ids_suffix >> simp[mk_inst_def])
  >- (Cases_on `emit_void opc ops s` >>
      drule added_insts_emit_void >> strip_tac >>
      irule entry_ids_suffix >> simp[mk_inst_def]) >>
  Cases_on `emit_inst opc ops outs s` >>
  drule added_insts_emit_inst >> strip_tac >>
  irule entry_ids_suffix >> simp[mk_inst_def]
QED

Theorem entry_ids_prims[local]:
  entry_alloca_ids s (SND (comp_return v s)) /\
  entry_alloca_ids s (SND (new_block lbl s)) /\
  entry_alloca_ids s (SND (fresh_label lbl s))
Proof
  simp[comp_return_def, entry_alloca_ids_def] >>
  simp[new_block_def, fresh_label_def, state_insts_def, all_blocks_def,
       REVERSE_DEF, MAP_APPEND, FLAT_APPEND, rich_listTheory.SNOC_APPEND]
QED

Theorem entry_ids_decoder[local]:
  entry_alloca_ids s
    (SND (compile_abi_decode_to_buf dst src CALLDATALOAD base_op hi info s))
Proof
  `abi_decoder_code s
    (SND (compile_abi_decode_to_buf dst src CALLDATALOAD base_op hi info s))` by
    simp[abi_decoder_code_mutual] >>
  fs[entry_alloca_ids_def, abi_decoder_code_def,
     decoder_code_member_state_insts] >> metis_tac[]
QED

val entry_ids_primitive = [entry_ids_emit, entry_ids_prims];
fun entry_ids_steps extras =
  rpt (FIRST [irule entry_ids_bind, irule entry_ids_ignore] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp (extras @ entry_ids_primitive);

Theorem entry_ids_ptr_guard[local]:
  entry_alloca_ids s (SND (compile_abi_arg_ptr_guard opc actual parent s))
Proof
  simp[compile_abi_arg_ptr_guard_def] >> IF_CASES_TAC >> entry_ids_steps []
QED

Theorem entry_ids_alloc_buffer[local]:
  entry_alloca_ids s (SND (compile_alloc_buffer n s))
Proof
  simp[compile_alloc_buffer_def] >> entry_ids_steps []
QED

Theorem entry_ids_create_kwargs[local]:
  !specs ce s. entry_alloca_ids s (SND (compile_create_kwarg_allocas ce specs s))
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, entry_ids_prims] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def] >>
  rpt gen_tac >> entry_ids_steps [entry_ids_alloc_buffer]
QED

Theorem entry_ids_lower_default[local]:
  entry_alloca_ids s (SND (lower_value compile_expr ce ty e s)) /\
  entry_alloca_ids s (SND (compile_store_bytestring src dst s))
Proof
  conj_tac >> irule entry_ids_suffix >>
  simp[lower_value_alloca_ids, store_bytestring_alloca_ids]
QED

Theorem entry_ids_init_kwargs[local]:
  !vars ce off k hi s. entry_alloca_ids s (SND (compile_init_kwargs ce vars off k hi s))
Proof
  Induct >> simp[compile_init_kwargs_def, entry_ids_prims] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_init_kwargs_def] >> rpt gen_tac >> IF_CASES_TAC >>
  rpt (FIRST [irule entry_ids_bind, irule entry_ids_ignore, IF_CASES_TAC] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_ids_emit, entry_ids_prims, entry_ids_lower_default,
       entry_ids_decoder, entry_ids_ptr_guard]
QED

Theorem entry_ids_entry_checks[local]:
  entry_alloca_ids s (SND (compile_entry_checks n payable s))
Proof
  simp[compile_entry_checks_def] >>
  rpt (FIRST [irule entry_ids_bind, irule entry_ids_ignore, IF_CASES_TAC] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_ids_emit, entry_ids_prims]
QED

Theorem entry_ids_group_entries[local]:
  !entries m common vars off s.
    entry_alloca_ids s (SND (compile_group_entries m entries common vars off s))
Proof
  Induct >> simp[compile_group_entries_def, entry_ids_prims] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_group_entries_def, compile_entry_point_kwargs_def] >>
  rpt gen_tac >> entry_ids_steps [entry_ids_init_kwargs, entry_ids_entry_checks]
QED

Theorem entry_ids_selector_checks[local]:
  !sels m s. entry_alloca_ids s (SND (compile_selector_checks m sels s))
Proof
  Induct >> simp[compile_selector_checks_def, entry_ids_prims] >>
  gen_tac >> PairCases_on `h` >> simp[compile_selector_checks_def] >>
  rpt gen_tac >> entry_ids_steps []
QED

Theorem entry_ids_external_groups[local]:
  !groups m s. entry_alloca_ids s (SND (compile_external_groups m groups s))
Proof
  Induct >> simp[compile_external_groups_def, entry_ids_prims] >>
  Cases
  >- (rename1 `ExternalSingle selector pkg` >> PairCases_on `selector` >>
      gen_tac >> PURE_ONCE_REWRITE_TAC[compile_external_groups_def] >>
      entry_ids_steps [entry_ids_selector_checks]) >>
  gen_tac >> PURE_ONCE_REWRITE_TAC[compile_external_groups_def] >>
  entry_ids_steps [entry_ids_create_kwargs, entry_ids_group_entries]
QED

Theorem entry_ids_group_dispatch:
  compile_group_dispatch_linear groups fallback sa = (jobs,sb) ==>
  entry_alloca_ids sa sb
Proof
  `entry_alloca_ids sa (SND (compile_group_dispatch_linear groups fallback sa))` by
    (simp[compile_group_dispatch_linear_def] >> entry_ids_steps [entry_ids_external_groups]) >>
  strip_tac >> fs[]
QED

val entry_mono_primitives = [ci_mono_comp_return, ci_mono_emit_op,
  ci_mono_emit_void, ci_mono_emit_inst, ci_mono_new_block];

fun entry_mono_steps extras =
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind, IF_CASES_TAC] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp (extras @ entry_mono_primitives);

Theorem entry_nonreentrant_ci_mono[local]:
  ci_mono s (SND (compile_nonreentrant_lock key trans view s)) /\
  ci_mono s (SND (compile_nonreentrant_unlock key trans view s))
Proof
  Cases_on `trans` >> Cases_on `view` >>
  simp[compile_nonreentrant_lock_def, compile_nonreentrant_unlock_def,
       ci_mono_emit_void, ci_mono_comp_return] >>
  entry_mono_steps []
QED

Theorem entry_guarded_ci_mono[local]:
  ci_mono s (SND (compile_guarded_body ce nr key trans view bstmts rt s))
Proof
  Cases_on `rt` >> simp[compile_guarded_body_def] >>
  entry_mono_steps [entry_nonreentrant_ci_mono, CONJUNCT2 compile_stmt_ci_mono,
    stmtLoweringMonoTheory.ci_mono_comp_get]
QED

Theorem entry_legacy_body_ci_mono[local]:
  ci_mono s (SND (compile_external_function_body ce args nr key trans view bstmts rt s))
Proof
  simp[compile_external_function_body_def] >>
  entry_mono_steps [registration_compile_ci_mono, entry_guarded_ci_mono]
QED

Theorem entry_legacy_jobs_ci_mono:
  !pkgs s. ci_mono s (SND (compile_external_fn_bodies pkgs s))
Proof
  Induct >> simp[compile_external_fn_bodies_def, ci_mono_comp_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def] >>
  rpt gen_tac >> entry_mono_steps [entry_legacy_body_ci_mono, compile_entry_checks_ci_mono]
QED

Theorem compile_external_jobs_ci_mono:
  !jobs s. ci_mono s (SND (compile_external_jobs jobs s))
Proof
  Induct >> simp[compile_external_jobs_def, ci_mono_comp_return] >>
  gen_tac >> Cases_on `h` >>
  simp[compile_external_jobs_def, compile_common_function_body_def] >>
  rpt gen_tac >>
  entry_mono_steps [entry_legacy_jobs_ci_mono, registration_compile_ci_mono,
    entry_guarded_ci_mono]
QED

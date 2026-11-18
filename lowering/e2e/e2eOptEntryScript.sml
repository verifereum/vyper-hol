(* The entry state of a frame running a finalized program: it relates to the
   compiled program's assembly entry, and the finalized program's assembly
   entry relates to the frame.

   TOP-LEVEL: opt_entry_codegen_asm_entry_rel, opt_entry_asm_frame_rel,
   opt_entry_fields.
 *)
Theory e2eOptEntry
Ancestors
  e2eProducers e2eEntry e2eDefs asmFrameRel codegenEntrySim codegenEntryRel
  contextCodegenRel codegenRel frameRel unitTransformDefs venomState

Theorem opt_entry_codegen_asm_entry_rel:
  !tops prog prog' am tx es cplan u.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u ==>
  codegen_asm_entry_rel cplan prog (opt_entry_state prog prog' cplan es)
    (entry_asm_state (opt_entry_state prog prog' cplan es) es)
Proof
  rpt strip_tac >>
  simp[codegenEntrySimTheory.codegen_asm_entry_rel_def,
       entry_asm_state_def, shared_state_rel_def,
       venom_asm_terminal_rel_def, opt_entry_state_def,
       entry_venom_state_frame_fields, entry_venom_state_fresh] >>
  gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
      entry_venom_state_def, venomStateTheory.init_venom_state_def,
      context_memory_rel_def]
QED

Theorem opt_entry_asm_frame_rel:
  !tops prog prog' am tx es cplan u.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u /\
  assemble prog' <> [] ==>
  asm_frame_rel prog' (opt_entry_state prog prog' cplan es).vs_data_section es
    (entry_asm_state (opt_entry_state prog prog' cplan es) es with
       as_code := assemble prog' ++
         (opt_entry_state prog prog' cplan es).vs_data_section) es
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`u`, `cplan`] assume_tac)
    entry_venom_state_initial_ctx_rel >>
  drule_then (qspec_then `cplan` strip_assume_tac)
    entry_venom_state_installed_section >>
  fs[entry_venom_state_frame_fields] >>
  `account_already_created
     (lookup_account (FST (HD es.contexts)).msgParams.callee
        es.rollback.accounts)` by
    (`(FST (HD es.contexts)).msgParams.code <> []` by
       (strip_tac >> fs[]) >>
     gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
         vfmExecutionTheory.account_already_created_def,
         listTheory.NULL_EQ]) >>
  `asm_frame_rel prog' (entry_venom_state prog' cplan es).vs_data_section es
     (entry_asm_state (entry_venom_state prog' cplan es) es) es` by
    metis_tac[asm_frame_rel_entry] >>
  `entry_asm_state (opt_entry_state prog prog' cplan es) es with
     as_code := assemble prog' ++
       (opt_entry_state prog prog' cplan es).vs_data_section =
   entry_asm_state (entry_venom_state prog' cplan es) es` by
    (qpat_assum `_ = assemble prog' ++ _` (fn th => REWRITE_TAC [GSYM th]) >>
     simp[opt_entry_state_def, entry_asm_state_def] >>
     simp[entry_venom_state_def] >>
     qpat_x_assum `_ = assemble prog' ++ _` (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `entry_asm_state _ _ with as_code := _ = _` SUBST1_TAC >>
  fs[opt_entry_state_def, entry_venom_state_frame_fields]
QED

Theorem opt_entry_fields:
  !tops prog prog' am tx es cplan vs.
    call_state_rel tops (assemble prog') am tx es /\
    vs = opt_entry_state prog prog' cplan es ==>
    vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
    vs.vs_call_ctx.cc_calldata =
      buffer_to_list (FST (HD es.contexts)).msgParams.data /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    vs.vs_call_ctx.cc_static = tx.is_static /\
    o1_initial_state_ok vs /\
    vs.vs_code = assemble prog ++ vs.vs_data_section
Proof
  rpt strip_tac >> gvs[] >>
  simp[opt_entry_state_def, entry_venom_state_frame_fields,
       entry_venom_state_fresh, o1_initial_state_ok_def] >>
  gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
      entry_venom_state_def, opt_entry_state_def]
QED

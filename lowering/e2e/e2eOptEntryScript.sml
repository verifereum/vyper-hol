(* The entry state of a frame running a finalized program: it relates to the
   compiled program's assembly entry, and the finalized program's assembly
   entry relates to the frame.

   TOP-LEVEL: opt_entry_codegen_asm_entry_rel, opt_entry_asm_frame_rel,
   opt_entry_fields.
 *)
Theory e2eOptEntry
Ancestors
  e2eProducers e2eEntry e2eDefs asmFrameRel codegenEntrySim codegenEntryRel
  codegenLabelDisciplined contextCodegenRel codegenRel frameRel
  unitTransformDefs venomState finite_map

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

(* Both entry relations use the bytes installed in the call frame. Venom's
   label map still uses the original program's offsets for control flow. *)
Theorem opt_entry_asm_rels_own:
  !tops prog prog' am tx es cplan.
    call_state_rel tops (assemble prog') am tx es /\
    assemble prog' <> [] ==>
    (opt_entry_state_own prog prog' cplan es).vs_code =
      assemble prog' ++ (opt_entry_state_own prog prog' cplan es).vs_data_section /\
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog
      (opt_entry_state_own prog prog' cplan es)
      (entry_asm_state (opt_entry_state_own prog prog' cplan es) es) /\
    asm_frame_rel prog' (opt_entry_state_own prog prog' cplan es).vs_data_section es
      (entry_asm_state (opt_entry_state_own prog prog' cplan es) es) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `cplan` strip_assume_tac)
    entry_venom_state_installed_section >>
  simp[opt_entry_state_own_def] >>
  conj_tac
  >- (simp[codegen_asm_entry_rel_reloc_def, entry_asm_state_def,
           shared_state_rel_def, venom_asm_terminal_rel_def,
           entry_venom_state_fresh, FLOOKUP_o_f] >>
      gvs[call_state_rel_def, frame_fresh_def, entry_venom_state_def,
          init_venom_state_def, context_memory_rel_def] >>
      gen_tac >> Cases_on `FLOOKUP (lo_reloc prog prog') l` >> simp[]) >>
  drule_then assume_tac call_state_rel_block_number_bound >>
  drule_then assume_tac call_state_rel_parsed >>
  gvs[call_state_rel_def, evm_state_ok_def, frame_fresh_def, frame_tx_rel_def] >>
  drule_all entry_venom_state_evm_environment >>
  disch_then (qspecl_then [`prog'`, `cplan`] strip_assume_tac) >>
  `tx.code = assemble prog' ++ DROP (LENGTH (assemble prog')) tx.code` by
    (qpat_assum `installed_code_rel _ _ _ _`
       (mp_tac o MATCH_MP immutableSectionRelTheory.installed_code_rel_section) >>
     simp[]) >>
  `tx.code <> []` by
    (strip_tac >> fs[]) >>
  simp[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def,
       asmDataSuffixPropsTheory.data_suffix_assemble,
       entry_venom_state_fresh, entry_venom_state_frame_fields,
       entry_venom_state_created_in_tx, asm_pc_to_offset_def,
       relationTheory.RTC_REFL] >>
  gvs[msg_ctx_rel_def, tx_ctx_rel_def, block_ctx_rel_def, blockhash_rel_def,
      vfmExecutionTheory.account_already_created_def, listTheory.NULL_EQ] >>
  qpat_assum `tx.code = assemble prog' ++ _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[CONJ_ASSOC]
QED

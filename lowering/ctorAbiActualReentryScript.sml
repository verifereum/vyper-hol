(* Pruning is a proof-state device, never a change to the real machine. *)
Theory ctorAbiActualReentry
Ancestors
  ctorAbiActualFrame ctorAbiActualMemory abiDecoderVarExtend fragExec
  abiDecoderVarSequence abiDecoderReentry abiDecoderReentryPointer
  abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
  venomMemDefs venomState compileEnv valueEncoding finite_map pred_set list

Theorem ctor_actual_extend_invariants:
  abi_decoder_vars_extend extras clean actual ==>
  (ctor_actual_scratch fn ids d n actual <=> ctor_actual_scratch fn ids d n clean) /\
  (alloca_inv actual <=> alloca_inv clean) /\
  (alloca_frontier_inv ctx fn site actual <=> alloca_frontier_inv ctx fn site clean) /\
  (val_in_memory tv v d actual.vs_memory <=> val_in_memory tv v d clean.vs_memory)
Proof
  strip_tac >> drule abi_decoder_vars_extend_observations >> strip_tac >>
  simp[ctor_actual_scratch_def, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def, alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

Theorem ctor_actual_extend_effect:
  abi_decoder_vars_extend extras clean actual ==>
  (abi_encoder_registered_effect ids outs initial actual <=>
   abi_encoder_registered_effect ids outs initial clean)
Proof
  strip_tac >> drule abi_decoder_vars_extend_restore >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_reentry_sequence:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code (abi_decoder_prune_vars next initial) = OK clean ==>
  ?actual. run_inst_seq code initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual
Proof
  strip_tac >> irule abi_decoder_sequence_vars_extend >> simp[] >>
  qexists `abi_decoder_prune_vars next initial` >>
  simp[abi_decoder_prune_extension]
QED

Theorem ctor_actual_reentry_live:
  abi_decoder_vars_extend extras clean actual /\
  (!op w. abi_decoder_operand_live next op /\
    eval_operand op (abi_decoder_prune_vars next initial) = SOME w ==>
    eval_operand op clean = SOME w) ==>
  !op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w
Proof
  rpt strip_tac >> irule abi_decoder_vars_extend_eval >>
  qexistsl [`extras`, `clean`] >> simp[] >> first_x_assum irule >>
  simp[abi_decoder_prune_eval]
QED

(* The postcondition observes the real endpoint, including retained SSA vars. *)
Theorem ctor_actual_reentry_fragment:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (emitted_insts st st') /\
  (!s. P s ==>
    ?clean. run_inst_seq (emitted_insts st st')
      (abi_decoder_prune_vars next s) = OK clean /\
      !actual. abi_decoder_vars_extend s.vs_vars clean actual ==>
        Q (actual with vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
  frag_exec ctx st st' P Q (K F)
Proof
  strip_tac >> irule frag_exec_run_inst_seq >> simp[] >>
  gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all ctor_actual_reentry_sequence >> strip_tac >>
  qexists `actual` >> simp[]
QED

(* Observations of successful allocation-free instruction sequences. *)
Theory entryReachBodySequenceObservations
Ancestors
  loweringStateRelDefs entryReachBodyExactArrayLoop ctorAbiActualAlloc exprLoweringProps emitHelperProps compileEnv
  venomExecSemantics venomState venomInst fragExec finite_map words list arithmetic

Theorem sequence_observer_step[local]:
  MEM i.inst_opcode [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
  step_inst_base i s = OK t ==> entry_loop_fields s t
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_pure2_def, exec_pure1_def, AllCaseEqs()] >> strip_tac >>
  gvs[entry_loop_fields_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem sequence_observer_fields[local]:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode
    [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY]) code ==>
  entry_loop_fields s t
Proof
  strip_tac >> simp[entry_loop_fields_def] >> rpt conj_tac >>
  irule run_inst_seq_preserves_field >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `MEM i.inst_opcode [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY]` by
    fs[EVERY_MEM] >>
  drule_all sequence_observer_step >> simp[entry_loop_fields_def]
QED

Theorem entry_sequence_observations:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode
    [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit_st.cs_next_var)
      i.inst_outputs) code /\
  fresh_vars_wrt limit_st s ==>
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >> conj_tac
  >- (irule sequence_observer_fields >> goal_assum (drule_at Any) >> fs[EVERY_CONJ]) >>
  simp_tac bool_ss [fresh_vars_wrt_def] >> rpt strip_tac >>
  `lookup_var (STRING #"%" (toString n)) t =
   lookup_var (STRING #"%" (toString n)) s` by
    (irule ctor_actual_sequence_var_frame >> goal_assum (drule_at Any) >>
     pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
     qpat_x_assum `EVERY _ code`
       (mp_tac o Q.SPEC `i` o REWRITE_RULE[EVERY_MEM]) >>
     asm_rewrite_tac[] >> disch_then (strip_assume_tac o BETA_RULE) >>
     BETA_TAC >>
     conj_tac >- (fs[MEM] >> simp[is_terminator_def]) >>
     strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >> decide_tac) >>
  gvs[lookup_var_def, fresh_vars_wrt_def, FLOOKUP_DEF] >> metis_tac[]
QED

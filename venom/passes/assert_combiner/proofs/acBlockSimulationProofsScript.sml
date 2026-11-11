(* Concrete assembly of the independently checked emission interfaces. *)
Theory acBlockSimulationProofs
Ancestors
  acMergeCursorProofs acMergeCursorDefs acMergeRuntimeDefs acMergeRuntimeProofs
  acLiveEmissionProofs acDeferredEmissionProofs acMergeSimulationProofs
  acBlockTransformProofs acSupplyProofs acChainProofs acAbortRelProofs
  acRuntimePhiProofs acRuntimeSuccessorProofs acRuntimeInvariantDefs
  runInstsExecBlockProps assertCombinerDefs venomExecSemantics venomExecProofs
  venomWf venomWfProps venomState venomInst dfgAnalysisProps
  stateEquiv stateEquivProps irSupply irSupplyFreshProps list rich_list pred_set

Theorem ac_query_fresh_operand:
  ir_supply_covers_fn su fn /\
  ac_get_iszero_operand (dfg_build_function fn) {} c = SOME (Var v) ==>
  v NOTIN ac_fresh_vars su fn
Proof
  rpt strip_tac >> drule ac_get_iszero_operand_src >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  metis_tac[ac_fresh_vars_original_operand]
QED

(* Source suffixes begin after the parallel PHI batch. The state in the
   certificate is normalized, but the two actual list states are not. *)
Theorem ac_merge_suffix_simulation:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn su fn /\ MEM bb fn.fn_blocks /\
  offset <= LENGTH bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> PHI) (DROP offset bb.bb_instructions) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (DROP offset bb.bb_instructions)) /\
  ir_supply_extends
    (SND (ac_merge_insts
      (ac_scan_block (dfg_build_function fn) (DROP offset bb.bb_instructions) NONE)
      [] su0 (DROP offset bb.bb_instructions))) su_end /\
  (set su_end.irs_used_vars DIFF set su0.irs_used_vars) SUBSET ac_fresh_vars su fn /\
  (!i v. MEM i (DROP offset bb.bb_instructions) /\
    (MEM (Var v) i.inst_operands \/ MEM v i.inst_outputs) ==>
    v NOTIN ac_fresh_vars su fn) /\
  ac_merge_runtime_cert fn bb offset 0 s /\
  state_equiv (ac_fresh_vars su fn) s t ==>
  (?e. run_insts fuel ctx (DROP offset bb.bb_instructions) s = Error e) \/
  lift_result (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV)
    ac_abort_equiv
    (run_insts fuel ctx (DROP offset bb.bb_instructions) s)
    (run_insts fuel ctx
      (FST (ac_merge_insts
        (ac_scan_block (dfg_build_function fn) (DROP offset bb.bb_instructions) NONE)
        [] su0 (DROP offset bb.bb_instructions))) t)
Proof
  rpt strip_tac >>
  qabbrev_tac `xs = DROP offset bb.bb_instructions` >>
  qabbrev_tac `cs = ac_scan_block (dfg_build_function fn) xs NONE` >>
  qabbrev_tac `shape = ac_merge_static xs cs su0 su_end` >>
  qabbrev_tac `pending = (ac_merge_pending xs cs : num -> (num # operand) list -> ir_supply -> (num # operand) option)` >>
  qabbrev_tac `cert = ac_merge_runtime_cert fn bb offset` >>
  `ac_merge_cursor_laws xs (dfg_build_function fn) cs (ac_fresh_vars su fn)
     su0 shape pending` by
    (metis_tac[Abbr `shape`, Abbr `pending`, Abbr `cs`, ac_merge_cursor_laws_scan]) >>
  `ac_merge_runtime_laws xs (dfg_build_function fn) fuel ctx cert` by
    (simp[Abbr `xs`, Abbr `cert`] >> irule ac_merge_runtime_cert_laws >> simp[]) >>
  `!c q v. ac_get_iszero_operand (dfg_build_function fn) {} c = SOME q /\
       q = Var v ==> v NOTIN ac_fresh_vars su fn` by
    (rpt strip_tac >> gvs[] >> metis_tac[ac_query_fresh_operand]) >>
  `ac_live_emission_contract xs cs fuel ctx
     (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV) ac_abort_equiv
     (ac_merge_live (ac_fresh_vars su fn) cert shape pending)
     (ac_merge_revert_deferred (ac_fresh_vars su fn) cert shape pending)` by
    (irule acLiveEmissionProofsTheory.ac_live_emission_contract >> metis_tac[]) >>
  `ac_deferred_emission_contract xs cs fuel ctx ac_abort_equiv
     (ac_merge_revert_deferred (ac_fresh_vars su fn) cert shape pending)` by
    (irule acDeferredEmissionProofsTheory.ac_deferred_emission_contract >> metis_tac[]) >>
  `ac_emission_end_contract xs (state_equiv (ac_fresh_vars su fn))
     (ac_merge_live (ac_fresh_vars su fn) cert shape pending)
     (ac_merge_revert_deferred (ac_fresh_vars su fn) cert shape pending)` by
    (simp[ac_emission_end_contract_def] >> conj_tac
     >- simp[ac_merge_live_def] >> metis_tac[ac_deferred_end]) >>
  drule ac_merge_insts_simulation_suffix >> simp[] >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum irule >>
  simp[ac_merge_live_def] >>
  fs[ac_merge_cursor_laws_def, Abbr `cert`]
QED

(* Initial witness diagnostics; no full-contract falsehood asserted. *)
Theory targetPureWalkWitnessProbe
Ancestors
  targetPureWalkConditionalSim targetPureWalkOracleProbe targetPureWalkCallerProbe
  targetPureWalkSimulationProbe exprLoweringProps venomInst venomExecSemantics
  venomState loweringStateRelDefs targetPureWalkModuleProbe

Theorem witness_context_forces_callee:
  !fn s. alloca_room simulation_probe_context fn s ==>
    fn = simulation_probe_callee
Proof
  simp[alloca_room_def, simulation_probe_context_def, mk_venom_context_def,
       lookup_function_def, listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
QED

Definition witness_cx_def:
  witness_cx = module_probe_cx with txn :=
    (module_probe_cx.txn with <| block_number := 1; block_hashes := [0w] |>)
End

Theorem witness_source_execution:
  !obs. eval_base_place witness_cx module_probe_target
      (oracle_probe_state with gas_obs := obs) =
    (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
     (oracle_probe_state with
       <| gas_obs := obs;
          immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 1)))])] |>))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Definition witness_machine_def:
  witness_machine = (init_venom_state "caller") with
    <| vs_vars := FEMPTY |+ ("a_ptr",0w);
       vs_alloca_next := 32;
       vs_memory := REPLICATE 32 0w;
       vs_block_ctx := (init_venom_state "caller").vs_block_ctx with
         <| bc_number := 1w; bc_blockhash := (\n. 0w) |> |>
End

Theorem witness_initial_relation:
  stmt_state_rel (simulation_probe_context_with_caller simulation_probe_caller)
    simulation_probe_caller simulation_probe_cenv witness_cx
    oracle_probe_state witness_machine
Proof
  `alloca_room (simulation_probe_context_with_caller simulation_probe_caller)
      simulation_probe_caller witness_machine` by
    (irule simulation_probe_caller_alloca_room >>
     simp_tac (srw_ss() ++ wordsLib.SIZES_ss)
       [witness_machine_def, wordsTheory.dimword_def]) >>
  rewrite_tac[stmt_state_rel_def] >>
  simp[simulation_probe_caller_alloca_room, simulation_probe_caller_fmp_room,
       simulation_probe_cenv_def, immutable_base_zero_def,
       immutable_alloca_sep_def, immutable_decl_sep_def,
       witness_machine_def, init_venom_state_def] >>
  reverse conj_tac >-
    simp[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
  rewrite_tac[state_rel_def] >>
  simp[immutables_rel_def, logs_rel_def, simulation_probe_cenv_def,
       oracle_probe_state_def, module_probe_state_def,
       vyperStateTheory.empty_state_def] >>
  conj_tac >-
    (simp[local_ptrs_rel_def, local_backed_def, local_region_def,
          vyperStateTheory.lookup_scopes_def, lookup_var_def] >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> EVAL_TAC >>
         rpt strip_tac >> `i = 0` by decide_tac >> gvs[] >> EVAL_TAC)
     >> rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]) >>
  EVAL_TAC >> simp[] >> gen_tac >>
  Cases_on `n = 0` >> simp[]
QED

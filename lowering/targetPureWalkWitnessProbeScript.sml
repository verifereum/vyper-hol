(* Initial witness diagnostics; no full-contract falsehood asserted. *)
Theory targetPureWalkWitnessProbe
Ancestors
  targetPureWalkConditionalSim targetPureWalkOracleProbe targetPureWalkCallerProbe
  targetPureWalkSimulationProbe exprLoweringProps venomInst venomExecSemantics
  venomState loweringStateRelDefs targetPureWalkModuleProbe
  vyperMachineFrame gasOutcome gasSummary gasExemptCert exprSimDefs vyperState

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

Definition witness_env_def:
  witness_env = (ARB : typing_env) with
    <| var_types := FEMPTY |+ ("a", ArrayT (BaseT (UintT 256)) (Fixed 1));
       var_assignable := FEMPTY |+ ("a",T);
       fn_sigs := FEMPTY |+ ((NONE,"index"),
         <| param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256) |>) |>
End

Theorem witness_target_sim:
  target_sim (simulation_probe_context_with_caller simulation_probe_caller)
    simulation_probe_caller simulation_probe_cenv witness_cx witness_env
    module_probe_target oracle_probe_state
Proof
  irule simulation_probe_target_sim_conditional_with_caller >>
  simp[simulation_probe_caller_name, witness_env_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  qexists_tac `oracle_probe_state with
    immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 1)))])]` >>
  simp[witness_source_execution] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem witness_antecedent:
  ~expr_can_mutate simulation_probe_cenv (target_to_expr module_probe_target) /\
  simulation_probe_cenv.ce_func_mutability = build_func_mutability (cx_tops witness_cx) /\
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops witness_cx) ==>
     function_mutability_ok [(NONE,cx_tops witness_cx)] vis mut nr dflts body) /\
  get_module_code witness_cx NONE = SOME (cx_tops witness_cx) /\
  EVERY (\c. FST c = NONE) (int_calls_target module_probe_target) /\
  target_sim (simulation_probe_context_with_caller simulation_probe_caller)
    simulation_probe_caller simulation_probe_cenv witness_cx witness_env
    module_probe_target oracle_probe_state /\
  type_place_target witness_env module_probe_target = SOME (Type (BaseT (UintT 256))) /\
  compile_get_target_ptr compile_expr simulation_probe_cenv module_probe_target
    simulation_probe_start = (simulation_probe_op,simulation_probe_finish) /\
  fn_has_code simulation_probe_start simulation_probe_finish simulation_probe_caller /\
  fn_inst_ids_distinct simulation_probe_caller /\
  local_ptrs_reserved simulation_probe_cenv simulation_probe_start /\
  gas_admissible (eval_base_place witness_cx module_probe_target) target_res_ok oracle_probe_state /\
  stmt_state_rel (simulation_probe_context_with_caller simulation_probe_caller)
    simulation_probe_caller simulation_probe_cenv witness_cx oracle_probe_state witness_machine /\
  ~witness_machine.vs_halted /\
  witness_machine.vs_current_bb = simulation_probe_start.cs_current_bb /\
  witness_machine.vs_inst_idx = LENGTH simulation_probe_start.cs_current_insts
Proof
  `gas_admissible (eval_base_place witness_cx module_probe_target)
     target_res_ok oracle_probe_state` by
    simp[gasContextTheory.gas_admissible_def, witness_source_execution,
         targetPlaceSimDefsTheory.target_res_ok_def] >>
  simp[witness_target_sim, simulation_probe_compilation,
       simulation_probe_caller_has_code, simulation_probe_caller_distinct,
       witness_initial_relation, witness_machine_def, init_venom_state_def,
       simulation_probe_start_def] >>
  conj_tac >- (EVAL_TAC >> simp[] >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[witness_env_def] >> EVAL_TAC >> simp[]) >>
  simp[local_ptrs_reserved_def, simulation_probe_cenv_def,
       finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> simp[not_fresh_at_def]
QED

Theorem witness_source_not_frame:
  !obs res ee.
    eval_base_place witness_cx module_probe_target
      (oracle_probe_state with gas_obs := obs) = (res,ee) ==>
    ~machine_frame (oracle_probe_state with logs := ee.logs) ee
Proof
  simp[witness_source_execution] >> rpt strip_tac >> gvs[] >>
  gvs[machine_frame_def, oracle_probe_state_def, module_probe_state_def,
      vyperStateTheory.empty_state_def, finite_mapTheory.FLOOKUP_EXT] >>
  fs[FUN_EQ_THM] >> first_x_assum (qspec_then `"x"` mp_tac) >> EVAL_TAC >> simp[]
QED

Theorem witness_exact_conclusion_false:
  ~gas_outcome F (cx_tops witness_cx)
    (simulation_probe_context_with_caller simulation_probe_caller, simulation_probe_caller)
    (eval_base_place witness_cx module_probe_target) (oracle_probe_state,witness_machine)
    (\res ee t. ?pv. res = INL pv /\
      target_post (simulation_probe_context_with_caller simulation_probe_caller)
        simulation_probe_caller simulation_probe_cenv witness_cx oracle_probe_state
        simulation_probe_start simulation_probe_finish witness_machine ee pv
        (Type (BaseT (UintT 256))) simulation_probe_op t /\
      machine_frame (oracle_probe_state with logs := ee.logs) ee /\
      ee.scopes = oracle_probe_state.scopes /\
      t.vs_current_bb = simulation_probe_finish.cs_current_bb /\
      t.vs_inst_idx = LENGTH simulation_probe_finish.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> fs[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def]
  >- (gvs[gasSummaryTheory.gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      strip_tac >> drule witness_source_not_frame >> simp[])
  >- (gvs[gasSummaryTheory.gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      simp[witness_source_execution] >> strip_tac >>
      gvs[exprSimDefsTheory.expr_exit_def])
  >> drule gasExemptCertTheory.gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       witness_source_execution, vyperStateTheory.return_def]
QED

(* All frozen premises hold together, but the exact frozen conclusion fails. *)
Theorem target_walk_frame_counterexample:
  ~(!ctx func cenv cx env bt es vt sa sb op s0.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
    (!vis mut nr rr fn args dflts ret body.
       MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
       function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
    get_module_code cx NONE = SOME (cx_tops cx) /\
    EVERY (\c. FST c = NONE) (int_calls_target bt) /\
    target_sim ctx func cenv cx env bt es /\
    type_place_target env bt = SOME vt /\
    compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es, s0)
      (\res ee t. ?pv. res = INL pv /\
         target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
         machine_frame (es with logs := ee.logs) ee /\ ee.scopes = es.scopes /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r))
Proof
  metis_tac[witness_antecedent, witness_exact_conclusion_false]
QED

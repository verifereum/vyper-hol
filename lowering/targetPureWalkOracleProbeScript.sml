(* Source diagnostics only, not a full-antecedent counterexample. *)
Theory targetPureWalkOracleProbe
Ancestors
  targetPureWalkModuleProbe gasOutcome gasSummary gasExemptCert exprSimDefs
  vyperState vyperMachineFrame targetPlaceSimDefs exprLoweringProps
  loweringStateRelDefs

Definition oracle_probe_state_def:
  oracle_probe_state = module_probe_state with outcomes := SOME []
End

Theorem oracle_probe_source_execution:
  !obs. eval_base_place module_probe_cx module_probe_target
      (oracle_probe_state with gas_obs := obs) =
    (INL (PlaceR (MemoryPlace "a" [ValueSubscript (IntV 0)])),
     (oracle_probe_state with
       <| gas_obs := obs;
          immutables := [(0w,[(NONE,FEMPTY |+ ("x",(BaseTV (UintT 256),IntV 1)))])] |>))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem oracle_probe_admissible:
  gas_admissible (eval_base_place module_probe_cx module_probe_target)
    target_res_ok oracle_probe_state
Proof
  simp[gasContextTheory.gas_admissible_def, oracle_probe_source_execution,
       targetPlaceSimDefsTheory.target_res_ok_def]
QED

Theorem oracle_probe_source_not_frame:
  !obs res ee.
    eval_base_place module_probe_cx module_probe_target
      (oracle_probe_state with gas_obs := obs) = (res,ee) ==>
    ~machine_frame (oracle_probe_state with logs := ee.logs) ee /\
    ee.scopes = oracle_probe_state.scopes
Proof
  simp[oracle_probe_source_execution] >> rpt strip_tac >> gvs[] >>
  gvs[machine_frame_def, oracle_probe_state_def, module_probe_state_def,
      vyperStateTheory.empty_state_def, finite_mapTheory.FLOOKUP_EXT] >>
  fs[FUN_EQ_THM] >> first_x_assum (qspec_then `"x"` mp_tac) >> EVAL_TAC >> simp[]
QED

Theorem oracle_probe_no_framed_outcome:
  !ctx func s0 P.
    ~gas_outcome F (cx_tops module_probe_cx) (ctx,func)
      (eval_base_place module_probe_cx module_probe_target)
      (oracle_probe_state,s0)
      (\res ee t. P res ee t /\
        machine_frame (oracle_probe_state with logs := ee.logs) ee)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  fs[gas_outcome_def, gas_summary_at_def]
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      strip_tac >> drule oracle_probe_source_not_frame >> simp[])
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      simp[oracle_probe_source_execution] >> strip_tac >>
      gvs[expr_exit_def])
  >> drule gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, oracle_probe_source_execution,
       vyperStateTheory.return_def]
QED

Theorem oracle_probe_invisible_immutables:
  !ctx func cenv cx es s imms.
    cenv.ce_module_vars = FEMPTY ==>
    (stmt_state_rel ctx func cenv cx (es with immutables := imms) s <=>
     stmt_state_rel ctx func cenv cx es s)
Proof
  rpt strip_tac >>
  simp[stmt_state_rel_def, state_rel_def, immutables_rel_def,
       immutable_alloca_sep_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, logs_rel_def]
QED

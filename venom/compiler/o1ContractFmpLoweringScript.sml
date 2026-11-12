(*
 * FmpLowering's O1 pass contract (o1_contract_fmp_lowering).  The step
 * half is fmpStepContract's.  The stage half is assembled here from the
 * stage simulation (fmpStageRunner) and the lowered memory phase
 * (fmpStageCoverage), at the raw input state: the real state with its
 * free-memory pointer fields set to the raw run's fmp.
 *
 * TOP-LEVEL:
 *   fmp_lowering_run_contract_gas - the stage half, row 3 to row 4
 *   o1_contract_fmp_lowering      - the pass contract
 *)
Theory o1ContractFmpLowering
Ancestors
  o1PassContract o1ScheduleDecomp fmpLowerDefs fmpAnalysisDefs
  venomPassDispatcher venomFnScheduleRunner venomPassSchedule
  venomCompilerTypes venomState venomInst o1ComposeSupport fmpStepContract
  fmpStageRunner fmpStageCoverage list

(* Why: the raw state is the real one with fmp in both free-memory pointer
   fields, a raw variant of it; the stage simulation and the lowered
   memory phase hold there, the static layout's end is the input's, which
   FmpLowering keeps, and row 4's function rows carry make_ssa_input_ok. *)
Theorem fmp_lowering_run_contract_gas:
  o1_run_contract_gas rpolicy D fmp 3
Proof
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  simp[o1_run_contract_gas_def, o1_stage_contract_gas_def,
       fmp_variant_def, pass_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  qexists_tac `vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>` >>
  conj_tac
  >- simp[raw_variant_def, gas_variant_def,
          venom_state_component_equality] >>
  strip_tac >>
  conj_tac >- metis_tac[fmp_lowering_stage_sim] >>
  `?eom. max_live_eom C = SOME eom` by
    (qpat_x_assum `o1_inv D 3 C _` mp_tac >>
     simp[o1_inv_def, o1_static_inv_def] >> metis_tac[]) >>
  `mem_inv (lowered_mem_fact eom) C' vs'` by
    metis_tac[fmp_lowering_stage_lowered_mem] >>
  `max_live_eom C' = max_live_eom C` by
    (irule ctx_pass_stage_max_live_eom >>
     qexistsl [`CFP_Simple VP_FmpLowering`, `rpolicy`, `o1_walk_view rpolicy 3`] >>
     simp[fn_pass_tag_def, fn_pass_static_layout_effect_def]) >>
  simp[o1_inv_def, o1_lowered_inv_def] >>
  fs[o1_pre_def, EVERY_MEM, o1_fn_row_def]
QED

Theorem o1_contract_fmp_lowering:
  o1_step_contract_at 3 rpolicy (CFP_Simple VP_FmpLowering) /\
  o1_run_contract_gas rpolicy D fmp 3
Proof
  simp[fmp_step_contract_at, fmp_lowering_run_contract_gas]
QED

(* Retained caller rows: closed child packets are consumed only at their
   immutable recorded call, with historical operand/setup agreement. *)
Theory gasFocusRetainedRowReplay
Ancestors
  dftGasPrefixProvider dftGasFromListReadings dftGasToListReplay
  dftGasFromListRestore dftRunRel removeUnusedGasProofs
  gasEvents gasOracleReplay dftIndexedExec venomExecSemantics
  venomInst venomState stateEquiv list rich_list arithmetic finite_map

Theorem focus_retained_invoke_contribution[local]:
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME csf /\
  eval_operands ops b0 = SOME args /\
  setup_callee csf args b0 = SOME child_entry /\
  (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
  (!callee argv. setup_callee callee argv
      (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0) /\
  u.vs_gas_readings = g ++ tail /\
  (?extra. es = gas_events_blocks f C csf
      (child_entry with vs_gas_readings := g ++ tail) ++ extra) /\
  ((?fr. terminates (run_blocks fr C csf
      (child_entry with vs_gas_readings := g ++ tail))) ==>
    gas_events_blocks f C csf
      (child_entry with vs_gas_readings := g ++ tail) = es /\
    residual_result tail (IntRet ir child_out)
      (run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail))) /\
  (!v. (run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail) = OK v \/
        ?r. run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail) = IntRet r v) ==>
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_blocks ((d,c.inst_id)::p) d f C csf
        (child_entry with vs_gas_readings := g ++ tail)) = ZIP (keys,g)) ==>
  (?extra. es = gas_events_step f C owner c u ++ extra) /\
  (!v. step_inst f C c u = OK v ==>
    gas_events_step f C owner c u = es /\ v.vs_gas_readings = tail /\
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_step p d f C sf c u) = ZIP (keys,g))
Proof
  strip_tac >>
  `!op. MEM op ops ==> eval_operand op u = eval_operand op b0` by
    (gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops u = SOME args` by metis_tac[eval_operands_agree] >>
  `setup_callee csf args u =
      SOME (child_entry with vs_gas_readings := g ++ tail)` by
    (qpat_x_assum `!callee argv. _` (qspecl_then [`csf`, `args`] mp_tac) >>
     simp[gas_setup_callee] >> Cases_on `setup_callee csf args u` >>
     simp[] >> strip_tac >> drule gas_setup_callee_readings >>
     simp[venom_state_component_equality]) >>
  simp[gas_events_step_def, dftGasFromListTraceDefsTheory.trace_step_invoke] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `run_blocks f C csf (child_entry with vs_gas_readings := g ++ tail)` >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  `?fr. terminates (run_blocks fr C csf
      (child_entry with vs_gas_readings := g ++ tail))` by
    (qexists_tac `f` >> simp[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `(?fr. _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> gvs[residual_result_def, lift_result_def] >>
  drule gas_bind_outputs_readings >>
  simp[Once (cj 1 dftGasFromListTraceDefsTheory.trace_defs)]
QED

(* Readings and backward cut guards for concrete LowerDload expansions. *)
Theory gasFocusLowerDloadCutGuards
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyRelation lowerDloadPublicTrace
  lowerDloadDefs o1LowerDloadRunner concretizeLayoutCutSafe o1SafeUpto
  gasOracleReplay oracleExecProps venomState venomInst list rich_list

Theorem ld_step_ok_cut_back:
  step_inst fuel C inst s = OK t /\ gas_cut n vs t ==> gas_cut n vs s
Proof
  strip_tac >> drule ld_step_ok_readings >>
  disch_then (qspec_then `ARB` assume_tac) >>
  gvs[gas_cut_def, LENGTH_DROP] >> decide_tac
QED

Theorem ld_block_entry_cut_back:
  step_inst fuel C inst s = OK u /\ enters_block fn u t /\
  gas_cut n vs t ==> gas_cut n vs s
Proof
  strip_tac >> drule enters_block_readings >> strip_tac >>
  drule ld_step_ok_cut_back >> disch_then irule >> gvs[gas_cut_def]
QED

Theorem ld_callee_entry_cut_back:
  setup_callee fn args s = SOME cs /\ enters_block fn cs t /\
  gas_cut n vs t ==> gas_cut n vs s
Proof
  strip_tac >> drule enters_block_readings >> strip_tac >>
  drule gas_setup_callee_readings >> strip_tac >> gvs[gas_cut_def]
QED

Theorem ld_prefix_nongas_readings[local]:
  !h t. ld_prefix C fn X p h t0 t /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) X ==>
    t.vs_gas_readings = t0.vs_gas_readings
Proof
  Induct
  >- simp[ld_prefix_zero] >>
  rpt strip_tac >> dxrule ld_prefix_predecessor >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac)) >>
  first_x_assum drule_all >> strip_tac >>
  `(EL h X).inst_opcode <> GAS /\ (EL h X).inst_opcode <> INVOKE` by
    (drule ld_prefix_bound >> strip_tac >> gvs[EVERY_EL]) >>
  drule_all step_inst_noninvoke_gas_readings >> strip_tac >> gvs[]
QED

Theorem ld_generated_nongas[local]:
  lower_dload_inst_supply u inst = (X,r) /\ 1 < LENGTH X ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) X
Proof
  Cases_on `inst.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[]) >>
  rw[lower_dload_inst_supply_def] >> gvs[]
QED

Theorem ld_expansion_prefix_readings:
  active_inst fn inst s /\ ld_envelope u fn s s.vs_inst_idx X p /\
  ld_prefix Ct fn' X p h t0 t ==>
  t.vs_gas_readings = t0.vs_gas_readings
Proof
  strip_tac >> Cases_on `h = 0`
  >- gvs[ld_prefix_zero] >>
  `1 < LENGTH X` by (drule ld_prefix_bound >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) X` by
    (drule ld_envelope_supply_reserved >> strip_tac >>
     drule_all ld_generated_nongas >> simp[]) >>
  drule_all ld_prefix_nongas_readings >> simp[]
QED

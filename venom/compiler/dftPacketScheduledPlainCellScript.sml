Theory dftPacketScheduledPlainCell
Ancestors
  dftStructural dftShape dftBlockSim dftDefs passSharedDefs oracleExecProps alist sorting
  venomExecSemantics venomState venomInst venomEffects list

Theorem dft_packet_scheduled_plain_cell:
  from_block [x] y /\ x.inst_opcode <> INVOKE /\
  ALL_DISTINCT (MAP FST obs) /\
  (x.inst_opcode = GAS ==> cell = [ALOOKUP obs key]) /\
  (x.inst_opcode <> GAS ==> cell = []) /\
  (y.inst_opcode = GAS ==>
     u.vs_gas_readings <> [] /\ MEM (key,HD u.vs_gas_readings) obs) /\
  step_inst n C y u = OK v ==>
  PERM (MAP THE (FILTER IS_SOME cell) ++ v.vs_gas_readings) u.vs_gas_readings
Proof
  strip_tac >> fs[from_block_def]
  >- (Cases_on `x.inst_opcode = GAS`
      >- (gvs[] >> Cases_on `u.vs_gas_readings` >> gvs[] >>
          drule_all ALOOKUP_ALL_DISTINCT_MEM >> strip_tac >>
          drule_all step_inst_ok_gas >> strip_tac >> simp[update_var_def]) >>
      `v.vs_gas_readings = u.vs_gas_readings` by
        (irule step_inst_noninvoke_gas_readings >> metis_tac[]) >>
      simp[]) >>
  `x.inst_opcode <> GAS` by
    (strip_tac >> gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  drule flip_operands_special_opcode >> simp[] >> strip_tac >>
  `v.vs_gas_readings = u.vs_gas_readings` by
    (irule step_inst_noninvoke_gas_readings >> metis_tac[]) >>
  simp[]
QED

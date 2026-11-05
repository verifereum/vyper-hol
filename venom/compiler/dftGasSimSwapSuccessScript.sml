Theory dftGasSimSwapSuccess
Ancestors
  dftGasSimLocalBoundary dftGasSimInvokeFrame dftGasSimBoundary
  dftRunRel dftBlockSim dftCommutation dftGasOracleDefs
  venomExecSemantics venomState venomInst venomWf list

Theorem ev_step_independent_update_ok_iff:
  inst_wf i /\
  (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
  ~MEM out i.inst_outputs ==>
  (ev_step orc p d fuel C i (update_var out value s) = OK u <=>
   ?t. ev_step orc p d fuel C i s = OK t /\
       u = update_var out value t)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (drule_all ev_step_invoke_update_var >>
      Cases_on `ev_step orc p d fuel C i s` >> simp[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = GAS`
  >- (`?gout. i.inst_outputs = [gout]` by metis_tac[ev_step_gas_shape] >>
      `!st. ev_step orc p d fuel C i st =
        OK (update_var gout (orc (p,d,i.inst_id)) st)` by
        (gen_tac >> drule_all ev_step_gas_shape >> simp[] >> metis_tac[]) >>
      gvs[] >> simp[update_var_commutes, EQ_SYM_EQ]) >>
  simp[ev_step_ordinary] >>
  drule_all step_inst_frame >>
  disch_then (qspecl_then [`fuel`, `C`, `s`, `value`] mp_tac) >>
  Cases_on `step_inst fuel C i s` >> simp[map_result_state_def] >> metis_tac[]
QED

Theorem ev_gas_pair_success_iff:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\
  inst_wf g /\ inst_wf i ==>
  ((?sg. ev_step orc p d fuel C g s = OK sg /\
         ev_step orc p d fuel C i sg = OK t) <=>
   (?si. ev_step orc p d fuel C i s = OK si /\
         ev_step orc p d fuel C g si = OK t))
Proof
  strip_tac >>
  `?gout. g.inst_outputs = [gout]` by metis_tac[ev_step_gas_shape] >>
  `!st. ev_step orc p d fuel C g st =
    OK (update_var gout (orc (p,d,g.inst_id)) st)` by
    (gen_tac >> drule_all ev_step_gas_shape >> simp[] >> metis_tac[]) >>
  drule_all dft_independent_gas_output >> strip_tac >>
  simp[] >> drule_all ev_step_independent_update_ok_iff >>
  simp[] >> metis_tac[]
QED


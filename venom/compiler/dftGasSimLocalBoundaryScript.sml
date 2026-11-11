Theory dftGasSimLocalBoundary
Ancestors
  dftGasSimInvokeFrame dftGasSimBoundary dftGasOracleDefs dftRunRel
  dftCommutation venomExecSemantics venomExecProps venomInst venomState
  instIdxIndep analysisSimProofsBase venomWf list pair

Theorem ev_step_ordinary:
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE ==>
  ev_step orc p d fuel C i s = step_inst fuel C i s
Proof
  simp[ev_step_def, step_inst_def]
QED

Theorem ev_step_gas_shape:
  i.inst_opcode = GAS /\ inst_wf i ==>
  ?out. i.inst_outputs = [out] /\
    ev_step orc p d fuel C i s = OK (update_var out (orc (p,d,i.inst_id)) s)
Proof
  strip_tac >>
  `LENGTH i.inst_outputs = 1` by gvs[inst_wf_def] >>
  Cases_on `i.inst_outputs` >> gvs[] >> simp[ev_step_def, ev_gas_def]
QED

Theorem ev_step_invoke_update_fold:
  !us s.
  i.inst_opcode = INVOKE /\
  EVERY (\uv. ~MEM (Var (FST uv)) i.inst_operands /\
               ~MEM (FST uv) i.inst_outputs) us ==>
  ev_step orc p d fuel C i
    (FOLDL (\u uv. update_var (FST uv) (SND uv) u) s us) =
  (case ev_step orc p d fuel C i s of
     OK t => OK (FOLDL (\u uv. update_var (FST uv) (SND uv) u) t us)
   | r => r)
Proof
  Induct >- (simp[] >> Cases_on `ev_step orc p d fuel C i s` >> simp[]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  `!y. MEM (Var y) i.inst_operands ==> FST h <> y` by metis_tac[] >>
  drule_all ev_step_invoke_update_var >>
  strip_tac >> simp[] >>
  Cases_on `ev_step orc p d fuel C i s` >> simp[]
QED

Theorem ev_step_nonterminator_no_intret:
  ~is_terminator i.inst_opcode ==> ev_step orc p d fuel C i s <> IntRet vals t
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (simp[ev_step_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  Cases_on `i.inst_opcode = GAS`
  >- simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  simp[ev_step_ordinary, dft_swap_nonterminator_no_intret]
QED

Theorem ev_step_nonterminator_halt_invoke:
  ~is_terminator i.inst_opcode /\ ev_step orc p d fuel C i s = Halt t ==>
  i.inst_opcode = INVOKE
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE` >- simp[] >>
  Cases_on `i.inst_opcode = GAS`
  >- (gvs[ev_step_def, ev_gas_def, AllCaseEqs()]) >>
  gvs[ev_step_ordinary] >> drule_all dft_swap_nonterminator_halt_invoke >> simp[]
QED

Theorem ev_step_nonterminator_ok_idx:
  ~is_terminator i.inst_opcode /\ ev_step orc p d fuel C i s = OK t ==>
  ev_step orc p d fuel C i (s with vs_inst_idx := n) =
    OK (t with vs_inst_idx := n)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- simp[ev_step_invoke_inst_idx] >>
  Cases_on `i.inst_opcode = GAS`
  >- (gvs[ev_step_def, ev_gas_def, AllCaseEqs()] >>
      simp[update_var_def]) >>
  gvs[ev_step_ordinary] >>
  simp[analysisSimProofsBaseTheory.step_inst_idx_indep,
       exec_result_map_def]
QED

Theorem ev_step_nonterminator_abort_idx_iff:
  ~is_terminator i.inst_opcode ==>
  ((?t. ev_step orc p d fuel C i (s with vs_inst_idx := n) = Abort a t) <=>
   (?t. ev_step orc p d fuel C i s = Abort a t))
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (simp[ev_step_invoke_inst_idx] >>
      Cases_on `ev_step orc p d fuel C i s` >> simp[]) >>
  Cases_on `i.inst_opcode = GAS`
  >- simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  simp[ev_step_ordinary, dft_swap_abort_idx_iff]
QED

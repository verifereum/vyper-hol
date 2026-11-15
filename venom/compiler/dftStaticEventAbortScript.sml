(* Static abort replay keeps the existing asymmetric DFT abort class. *)
Theory dftStaticEventAbort
Ancestors
  dftStaticAbort dftGasSimSwapStop dftGasSimLocalBoundary dftGasSimBoundary
  dftRunRel dftBlockSim dftIndexedExec dftPermSim dftGasOracleDefs
  venomExecSemantics venomState venomInst venomWf venomEffects opcodeClass
  list pair pred_set

Theorem ev_suffix_first_abort_static:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
    write_effects x.inst_opcode = empty_effects) /\
  (y.inst_opcode <> INVOKE ==>
   !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  ev_step orc p d fuel C x s = Abort a t ==>
  ev_suffix orc p d fuel C (x::y::tail) s = Abort a t /\
  ?b u. ev_suffix orc p d fuel C (y::x::tail) s = Abort b u /\
        (a = Revert_abort ==> b = Revert_abort)
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  simp[ev_suffix_def] >>
  Cases_on `x.inst_opcode = GAS`
  >- gvs[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  Cases_on `y.inst_opcode = GAS`
  >- (`?sy. ev_step orc p d fuel C y s = OK sy` by
        (drule_all ev_step_gas_shape >> metis_tac[]) >>
      `?u. ev_step orc p d fuel C x sy = Abort a u` by
        metis_tac[ev_pair_abort_iff] >>
      `?u. ev_step orc p d fuel C x
             (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[ev_step_nonterminator_abort_idx_iff] >>
      simp[ev_suffix_def] >> metis_tac[]) >>
  Cases_on `y.inst_opcode = INVOKE`
  >- metis_tac[ev_invoke_partner_no_abort] >>
  Cases_on `x.inst_opcode = INVOKE`
  >- (drule_all dft_swap_invoke_partner_class >> strip_tac >>
      `y.inst_opcode <> CODECOPY` by
        (strip_tac >> gvs[write_effects_def, empty_effects_def]) >>
      `~is_pseudo y.inst_opcode /\ y.inst_opcode <> ALLOCA` by
        (gvs[dft_gas_swap_pair_def] >> metis_tac[is_alloca_op_def]) >>
      `?sy. step_inst fuel C y s = OK sy` by
        metis_tac[dft_swap_guarded_nofail_total] >>
      `ev_step orc p d fuel C y s = OK sy` by simp[ev_step_ordinary] >>
      `?u. ev_step orc p d fuel C x sy = Abort a u` by
        metis_tac[ev_pair_abort_iff] >>
      `?u. ev_step orc p d fuel C x
             (sy with vs_inst_idx := SUC s.vs_inst_idx) = Abort a u` by
        metis_tac[ev_step_nonterminator_abort_idx_iff] >>
      simp[ev_suffix_def] >> metis_tac[]) >>
  `~gas_pair x.inst_opcode y.inst_opcode` by simp[gas_pair_def] >>
  gvs[ev_step_ordinary] >>
  drule_at (Pat `step_inst _ _ _ _ = Abort _ _`) dft_nongas_suffix_first_abort_static >>
  simp[] >>
  disch_then (qspecl_then [`y`, `[]`] mp_tac) >> simp[] >>
  Cases_on `step_inst fuel C y s` >>
  simp[dft_exec_suffix_cons, dft_exec_cons_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `step_inst fuel C x (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
      gvs[dft_exec_suffix_def] >> simp[ev_suffix_def] >> metis_tac[]) >>
  simp[ev_suffix_def] >> metis_tac[]
QED

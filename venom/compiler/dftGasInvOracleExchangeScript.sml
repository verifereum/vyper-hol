Theory dftGasInvOracleExchange
Ancestors
  dftGasOracleDefs dftRunRel dftBlockSim dftIndexedExec dftCommutation
  venomExecSemantics venomInst venomState

Theorem inv_ev_indexed_nongas_pair_ok:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  x.inst_opcode <> GAS /\ y.inst_opcode <> GAS /\
  x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE /\
  ev_step orc p d fuel ctx y s = OK sy /\
  ev_step orc p d fuel ctx x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ?sx sxy. ev_step orc p d fuel ctx x s = OK sx /\
    ev_step orc p d fuel ctx y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >> gvs[ev_step_def] >>
  qspecl_then [`x`, `y`] mp_tac (Q.GENL [`x`, `y`] dft_indexed_nongas_pair_ok) >>
  simp[step_inst_non_invoke, gas_pair_def] >> metis_tac[]
QED

Theorem inv_ev_noninvoke_ok_idx:
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ev_step orc p d fuel ctx i s = OK t ==>
  ev_step orc p d fuel ctx i (s with vs_inst_idx := n) =
    OK (t with vs_inst_idx := n)
Proof
  strip_tac >> Cases_on `i.inst_opcode = GAS`
  >- (gvs[ev_step_def, ev_gas_def, AllCaseEqs()] >>
      simp[update_var_def]) >>
  gvs[ev_step_def] >>
  `step_inst fuel ctx i s = OK t` by simp[step_inst_non_invoke] >>
  drule_all dft_step_ok_idx >> simp[step_inst_non_invoke]
QED

Theorem inv_ev_noninvoke_preserves_idx:
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ev_step orc p d fuel ctx i s = OK t ==>
  t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> Cases_on `i.inst_opcode = GAS`
  >- gvs[ev_step_def, ev_gas_def, AllCaseEqs(), update_var_def] >>
  gvs[ev_step_def] >>
  `step_inst fuel ctx i s = OK t` by simp[step_inst_non_invoke] >>
  metis_tac[step_inst_preserves_inst_idx]
QED

Theorem inv_ev_gas_shape:
  g.inst_opcode = GAS /\ inst_wf g ==>
  ?out. g.inst_outputs = [out] /\
    !orc p d fuel ctx s. ev_step orc p d fuel ctx g s =
      OK (update_var out (orc (p,d,g.inst_id)) s)
Proof
  strip_tac >> drule_all dft_gas_ok_shape >> strip_tac >>
  qexists_tac `out` >> simp[ev_step_def, ev_gas_def]
QED

Theorem inv_ev_ordinary_var_frame:
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  ~MEM (Var out) i.inst_operands /\ ~MEM out i.inst_outputs ==>
  ev_step orc p d fuel ctx i (update_var out w s) =
    map_result_state (update_var out w) (ev_step orc p d fuel ctx i s)
Proof
  strip_tac >> simp[ev_step_def] >>
  irule step_inst_base_frame >> metis_tac[]
QED

Theorem inv_ev_gas_ordinary_success:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\ inst_wf g /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  ev_step orc p d fuel ctx g s = OK sg /\
  ev_step orc p d fuel ctx i sg = OK st ==>
  ?t. ev_step orc p d fuel ctx i s = OK t /\
      ev_step orc p d fuel ctx g t = OK st
Proof
  strip_tac >> drule_all inv_ev_gas_shape >> strip_tac >>
  drule_all dft_independent_gas_output >> strip_tac >>
  gvs[] >> drule_all inv_ev_ordinary_var_frame >>
  disch_then (fn th => fs[th]) >>
  Cases_on `ev_step orc p d fuel ctx i s` >>
  gvs[map_result_state_def]
QED

Theorem inv_ev_ordinary_gas_success:
  dft_gas_swap_pair g i /\ g.inst_opcode = GAS /\ inst_wf g /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  ev_step orc p d fuel ctx i s = OK t /\
  ev_step orc p d fuel ctx g t = OK st ==>
  ?sg. ev_step orc p d fuel ctx g s = OK sg /\
       ev_step orc p d fuel ctx i sg = OK st
Proof
  strip_tac >> drule_all inv_ev_gas_shape >> strip_tac >>
  drule_all dft_independent_gas_output >> strip_tac >>
  gvs[] >> irule EQ_TRANS >>
  qexists_tac `map_result_state (update_var out (orc (p,d,g.inst_id)))
    (ev_step orc p d fuel ctx i s)` >>
  conj_tac >- (irule inv_ev_ordinary_var_frame >> simp[]) >>
  simp[map_result_state_def]
QED

Theorem inv_ev_two_gas_success:
  dft_gas_swap_pair x y /\ x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  inst_wf x /\ inst_wf y /\
  ev_step orc p d fuel ctx y s = OK sy /\
  ev_step orc p d fuel ctx x sy = OK st ==>
  ?sx. ev_step orc p d fuel ctx x s = OK sx /\
       ev_step orc p d fuel ctx y sx = OK st
Proof
  strip_tac >>
  `?outx. x.inst_outputs = [outx] /\
    !orc p d fuel ctx s. ev_step orc p d fuel ctx x s =
      OK (update_var outx (orc (p,d,x.inst_id)) s)` by
    (irule inv_ev_gas_shape >> simp[]) >>
  `?outy. y.inst_outputs = [outy] /\
    !orc p d fuel ctx s. ev_step orc p d fuel ctx y s =
      OK (update_var outy (orc (p,d,y.inst_id)) s)` by
    (irule inv_ev_gas_shape >> simp[]) >>
  `outx <> outy` by
    (drule_all dft_independent_gas_output >> simp[]) >>
  gvs[] >> simp[update_var_def, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem inv_ev_gas_pair_success:
  dft_gas_swap_pair x y /\ ~(x.inst_opcode <> GAS /\ y.inst_opcode <> GAS) /\
  inst_wf x /\ inst_wf y /\
  x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE /\
  ev_step orc p d fuel ctx y s = OK sy /\
  ev_step orc p d fuel ctx x sy = OK st ==>
  ?sx. ev_step orc p d fuel ctx x s = OK sx /\
       ev_step orc p d fuel ctx y sx = OK st
Proof
  strip_tac >> Cases_on `x.inst_opcode = GAS`
  >- (Cases_on `y.inst_opcode = GAS`
      >- (irule inv_ev_two_gas_success >> metis_tac[]) >>
      irule inv_ev_ordinary_gas_success >> metis_tac[]) >>
  `y.inst_opcode = GAS` by gvs[gas_pair_def] >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  irule inv_ev_gas_ordinary_success >> metis_tac[]
QED

Theorem inv_ev_indexed_noninvoke_pair_ok:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE /\
  ev_step orc p d fuel ctx y s = OK sy /\
  ev_step orc p d fuel ctx x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ?sx sxy. ev_step orc p d fuel ctx x s = OK sx /\
    ev_step orc p d fuel ctx y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >> Cases_on `~(x.inst_opcode <> GAS /\ y.inst_opcode <> GAS)`
  >- (`~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
        gvs[dft_gas_swap_pair_def] >>
      `ev_step orc p d fuel ctx x sy = OK (syx with vs_inst_idx := sy.vs_inst_idx)` by
        (qpat_x_assum `ev_step _ _ _ _ _ y s = _` kall_tac >>
         drule_all inv_ev_noninvoke_ok_idx >>
         disch_then (qspec_then `sy.vs_inst_idx` mp_tac) >> simp[]) >>
      drule_all inv_ev_gas_pair_success >> strip_tac >>
      qexistsl_tac [`sx`, `syx with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[] >> drule_all inv_ev_noninvoke_ok_idx >>
      disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[]) >>
  irule inv_ev_indexed_nongas_pair_ok >> gvs[gas_pair_def] >> metis_tac[]
QED

Theory dftGasInvCallExchange
Ancestors
  dftGasInvCallPartner dftGasInvCallFrame dftGasInvOracleExchange
  dftGasOracleDefs dftRunRel dftBlockSim venomInstProofs1
  venomExecSemantics venomInst venomState list pred_set

Theorem inv_partner_updates_support[local]:
  dft_gas_swap_pair c i /\ MAP FST pairs = i.inst_outputs ==>
  EVERY (\uw. ~MEM (Var (FST uw)) c.inst_operands /\
               ~MEM (FST uw) c.inst_outputs) pairs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST uw) i.inst_outputs` by metis_tac[MEM_MAP] >>
  gvs[dft_gas_swap_pair_def, inst_defs_def, inst_uses_def,
      DISJOINT_DEF, EXTENSION] >>
  metis_tac[mem_var_operand_vars]
QED

Theorem inv_ev_call_partner_success:
  dft_gas_swap_pair c i /\ c.inst_opcode = INVOKE /\ inst_wf i /\
  ev_step orc p d fuel ctx c s = OK sc /\
  ev_step orc p d fuel ctx i sc = OK st ==>
  ?si. ev_step orc p d fuel ctx i s = OK si /\
       ev_step orc p d fuel ctx c si = OK st
Proof
  strip_tac >> drule_all inv_call_partner_inputs >>
  strip_tac >>
  `inv_partner_inputs i sc s` by metis_tac[inv_partner_inputs_sym] >>
  drule_all inv_partner_portable_updates >> strip_tac >>
  drule_all inv_partner_updates_support >> strip_tac >>
  qexists_tac `FOLDL (\st (out,w). update_var out w st) s pairs` >>
  simp[] >>
  drule_all inv_ev_invoke_updates_frame >>
  strip_tac >> fs[pairTheory.LAMBDA_PROD]
QED

Theorem inv_ev_partner_call_success:
  dft_gas_swap_pair c i /\ c.inst_opcode = INVOKE /\ inst_wf i /\
  ev_step orc p d fuel ctx i s = OK si /\
  ev_step orc p d fuel ctx c si = OK st ==>
  ?sc. ev_step orc p d fuel ctx c s = OK sc /\
       ev_step orc p d fuel ctx i sc = OK st
Proof
  strip_tac >>
  `inv_partner_inputs i s s` by simp[inv_partner_inputs_def] >>
  drule_all inv_partner_portable_updates >> strip_tac >>
  drule_all inv_partner_updates_support >> strip_tac >>
  drule_all inv_ev_invoke_updates_frame >>
  strip_tac >> fs[pairTheory.LAMBDA_PROD] >>
  Cases_on `ev_step orc p d fuel ctx c s` >> gvs[] >>
  rename1 `ev_step orc p d fuel ctx c s = OK sc` >>
  drule_all inv_call_partner_inputs >> strip_tac >>
  drule_all inv_partner_portable_updates >> strip_tac >> gvs[] >>
  rename1 `ev_step orc p d fuel ctx i sc = OK (FOLDL _ sc transported)` >>
  `EVERY (\uw. ~MEM (Var (FST uw)) c.inst_operands /\
                 ~MEM (FST uw) c.inst_outputs) transported` by
    (irule inv_partner_updates_support >> metis_tac[]) >>
  qspec_then `transported` mp_tac
    (Q.INST [`inst` |-> `c`] inv_ev_invoke_updates_frame) >>
  simp[pairTheory.LAMBDA_PROD] >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  qpat_x_assum `FOLDL _ s pairs = _`
    (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem inv_ev_swap_ok_idx[local]:
  ~is_terminator i.inst_opcode /\ ev_step orc p d fuel ctx i s = OK t ==>
  ev_step orc p d fuel ctx i (s with vs_inst_idx := n) =
    OK (t with vs_inst_idx := n)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (irule inv_ev_invoke_ok_idx >> simp[]) >>
  irule inv_ev_noninvoke_ok_idx >> simp[]
QED

Theorem inv_ev_invoke_pair_success[local]:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  (x.inst_opcode = INVOKE \/ y.inst_opcode = INVOKE) /\
  ev_step orc p d fuel ctx y s = OK sy /\
  ev_step orc p d fuel ctx x sy = OK st ==>
  ?sx. ev_step orc p d fuel ctx x s = OK sx /\
       ev_step orc p d fuel ctx y sx = OK st
Proof
  strip_tac
  >- (irule inv_ev_partner_call_success >> metis_tac[]) >>
  irule inv_ev_call_partner_success >> metis_tac[dft_gas_swap_pair_sym]
QED

Theorem inv_ev_indexed_pair_ok:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ev_step orc p d fuel ctx y s = OK sy /\
  ev_step orc p d fuel ctx x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ?sx sxy. ev_step orc p d fuel ctx x s = OK sx /\
    ev_step orc p d fuel ctx y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >> Cases_on `x.inst_opcode <> INVOKE /\ y.inst_opcode <> INVOKE`
  >- (irule inv_ev_indexed_noninvoke_pair_ok >> metis_tac[]) >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    gvs[dft_gas_swap_pair_def] >>
  `ev_step orc p d fuel ctx x sy = OK (syx with vs_inst_idx := sy.vs_inst_idx)` by
    (qpat_x_assum `ev_step _ _ _ _ _ y s = _` kall_tac >>
     drule_all inv_ev_swap_ok_idx >>
     disch_then (qspec_then `sy.vs_inst_idx` mp_tac) >> simp[]) >>
  `?sx. ev_step orc p d fuel ctx x s = OK sx /\
     ev_step orc p d fuel ctx y sx = OK (syx with vs_inst_idx := sy.vs_inst_idx)` by
    (irule inv_ev_invoke_pair_success >> metis_tac[]) >>
  qexistsl_tac [`sx`, `syx with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >> drule_all inv_ev_swap_ok_idx >>
  disch_then (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[]
QED

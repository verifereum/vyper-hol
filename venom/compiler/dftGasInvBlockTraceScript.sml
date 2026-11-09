Theory dftGasInvBlockTrace
Ancestors
  dftGasInvFixedTrace dftGasInvResidualTrace dftGasInvBoundaryState
  dftGasOracleDefs dftRunRel opcodeClass venomExecSemantics venomInst
  venomState list rich_list sorting

Theorem inv_ev_nonterminator_no_intret:
  ~is_terminator i.inst_opcode ==>
  ev_step orc p d fuel ctx i s <> IntRet vals t
Proof
  strip_tac >> Cases_on `i.inst_opcode = GAS`
  >- simp[ev_step_def, ev_gas_def, AllCaseEqs()] >>
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[ev_step_def, AllCaseEqs()] >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[ev_step_def] >> strip_tac >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem inv_block_trace_OK:
  !body pre s.
  bb.bb_instructions = pre ++ body ++ [term] /\
  s.vs_inst_idx = LENGTH pre /\
  EVERY (\i. ~is_terminator i.inst_opcode) body /\
  is_terminator term.inst_opcode ==>
  (ev_block orc p d fuel ctx bb s = OK t <=>
   ?u. inv_ev_trace orc p d fuel ctx body s u /\
       ev_step orc p d fuel ctx term u = OK t /\ ~t.vs_halted)
Proof
  Induct >> rpt strip_tac
  >- (once_rewrite_tac[ev_block_def] >>
      simp[get_instruction_def, EL_APPEND_EQN, inv_ev_trace_def] >>
      Cases_on `ev_step orc p d fuel ctx term s` >> simp[] >>
      rename1 `OK mid` >> Cases_on `mid.vs_halted` >> simp[] >> metis_tac[]) >>
  rename1 `bb.bb_instructions = pre ++ h::tail ++ [term]` >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `!mid. (ev_block orc p d fuel ctx bb
      (mid with vs_inst_idx := SUC s.vs_inst_idx) = OK t <=>
      ?u. inv_ev_trace orc p d fuel ctx tail
        (mid with vs_inst_idx := SUC s.vs_inst_idx) u /\
        ev_step orc p d fuel ctx term u = OK t /\ ~t.vs_halted)` by
    (gen_tac >> first_x_assum irule >>
     gvs[] >> qexists_tac `pre ++ [h]` >> simp[APPEND_ASSOC]) >>
  gvs[EVERY_DEF] >>
  once_rewrite_tac[ev_block_def] >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx h s` >>
  simp[inv_ev_trace_def] >> metis_tac[]
QED

Theorem inv_block_trace_IntRet:
  !body pre s.
  bb.bb_instructions = pre ++ body ++ [term] /\
  s.vs_inst_idx = LENGTH pre /\
  EVERY (\i. ~is_terminator i.inst_opcode) body /\
  is_terminator term.inst_opcode ==>
  (ev_block orc p d fuel ctx bb s = IntRet vals t <=>
   ?u. inv_ev_trace orc p d fuel ctx body s u /\
       ev_step orc p d fuel ctx term u = IntRet vals t)
Proof
  Induct >> rpt strip_tac
  >- (once_rewrite_tac[ev_block_def] >>
      simp[get_instruction_def, EL_APPEND_EQN, inv_ev_trace_def] >>
      Cases_on `ev_step orc p d fuel ctx term s` >> simp[] >>
      rename1 `OK mid` >> Cases_on `mid.vs_halted` >> simp[]) >>
  rename1 `bb.bb_instructions = pre ++ h::tail ++ [term]` >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `!mid. (ev_block orc p d fuel ctx bb
      (mid with vs_inst_idx := SUC s.vs_inst_idx) = IntRet vals t <=>
      ?u. inv_ev_trace orc p d fuel ctx tail
        (mid with vs_inst_idx := SUC s.vs_inst_idx) u /\
        ev_step orc p d fuel ctx term u = IntRet vals t)` by
    (gen_tac >> first_x_assum irule >>
     gvs[] >> qexists_tac `pre ++ [h]` >> simp[APPEND_ASSOC]) >>
  gvs[EVERY_DEF] >>
  `ev_step orc p d fuel ctx h s <> IntRet vals t` by
    metis_tac[inv_ev_nonterminator_no_intret] >>
  once_rewrite_tac[ev_block_def] >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx h s` >>
  gvs[inv_ev_trace_def] >> metis_tac[]
QED

Theorem inv_block_source_sort:
  bb.bb_instructions = pre ++ ordered ++ [term] /\
  bb'.bb_instructions = pre' ++ executed ++ [term] /\
  s.vs_inst_idx = LENGTH pre /\ LENGTH pre' = LENGTH pre /\
  EVERY (\i. ~is_terminator i.inst_opcode) ordered /\
  EVERY (\i. ~is_terminator i.inst_opcode) executed /\
  is_terminator term.inst_opcode /\
  ALL_DISTINCT ordered /\ PERM executed ordered /\
  (!x z. id_before ordered x z /\ id_before executed z x ==>
     dft_gas_swap_pair x z /\ inst_wf x /\ inst_wf z) /\
  (r = OK t \/ r = IntRet vals t) /\
  ev_block orc p d fuel ctx bb' s = r ==>
  ev_block orc p d fuel ctx bb s = r
Proof
  rpt strip_tac >> gvs[]
  >- (`?u. inv_ev_trace orc p d fuel ctx executed s u /\
           ev_step orc p d fuel ctx term u = OK t /\ ~t.vs_halted` by
        metis_tac[inv_block_trace_OK] >>
      `inv_ev_trace orc p d fuel ctx ordered s u` by
        (irule inv_trace_source_sort >> simp[] >>
         qexists_tac `executed` >> simp[] >> metis_tac[]) >>
      metis_tac[inv_block_trace_OK]) >>
  `?u. inv_ev_trace orc p d fuel ctx executed s u /\
       ev_step orc p d fuel ctx term u = IntRet vals t` by
    metis_tac[inv_block_trace_IntRet] >>
  `inv_ev_trace orc p d fuel ctx ordered s u` by
    (irule inv_trace_source_sort >> simp[] >>
         qexists_tac `executed` >> simp[] >> metis_tac[]) >>
  metis_tac[inv_block_trace_IntRet]
QED

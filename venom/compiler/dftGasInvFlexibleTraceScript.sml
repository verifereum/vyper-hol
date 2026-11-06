Theory dftGasInvFlexibleTrace
Ancestors
  dftGasInvCallExchange dftGasInvCallPartner dftGasInvResidualTrace dftGasInvPrefixRun
  dftGasOracleDefs dftRunRel dftPermSim dftShape dftStructural dftDefs venomExecSemantics venomInst venomState venomEffects passSharedDefs list

Definition inv_ev_ftrace_def:
  (inv_ev_ftrace orc p d ctx [] s t <=> s = t) /\
  (inv_ev_ftrace orc p d ctx (i::xs) s t <=>
    ?fuel u. ~is_terminator i.inst_opcode /\
      ev_step orc p d fuel ctx i s = OK u /\
      inv_ev_ftrace orc p d ctx xs
        (u with vs_inst_idx := SUC s.vs_inst_idx) t)
End

Theorem inv_ev_trace_ftrace:
  !xs s t. inv_ev_trace orc p d fuel ctx xs s t ==>
    inv_ev_ftrace orc p d ctx xs s t
Proof
  Induct >> simp[inv_ev_trace_def, inv_ev_ftrace_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem inv_ev_ftrace_append:
  !xs ys s t. inv_ev_ftrace orc p d ctx (xs ++ ys) s t <=>
    ?u. inv_ev_ftrace orc p d ctx xs s u /\
        inv_ev_ftrace orc p d ctx ys u t
Proof
  Induct >> simp[inv_ev_ftrace_def] >> metis_tac[]
QED

Theorem inv_ev_ftrace_idx:
  !xs s t. inv_ev_ftrace orc p d ctx xs s t ==>
    t.vs_inst_idx = s.vs_inst_idx + LENGTH xs
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem inv_ev_noninvoke_fuel:
  i.inst_opcode <> INVOKE ==>
  ev_step orc p d fuel1 ctx i s = ev_step orc p d fuel2 ctx i s
Proof
  simp[ev_step_def]
QED

Theorem inv_ev_indexed_mixed_pair_ok:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ev_step orc p d fy ctx y s = OK sy /\
  ev_step orc p d fx ctx x (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
  ?sx sxy. ev_step orc p d fx ctx x s = OK sx /\
    ev_step orc p d fy ctx y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
    (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
    (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  strip_tac >> Cases_on `x.inst_opcode = INVOKE`
  >- (`y.inst_opcode <> INVOKE` by metis_tac[inv_call_partner_class] >>
      `!st. ev_step orc p d fy ctx y st = ev_step orc p d fx ctx y st` by
        metis_tac[inv_ev_noninvoke_fuel] >>
      metis_tac[inv_ev_indexed_pair_ok]) >>
  `!st. ev_step orc p d fx ctx x st = ev_step orc p d fy ctx x st` by
    metis_tac[inv_ev_noninvoke_fuel] >>
  metis_tac[inv_ev_indexed_pair_ok]
QED

Theorem inv_ev_ftrace_exchange:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  inv_ev_ftrace orc p d ctx (y::x::xs) s t ==>
  inv_ev_ftrace orc p d ctx (x::y::xs) s t
Proof
  simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  drule_all inv_ev_indexed_mixed_pair_ok >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem inv_ev_ftrace_slice:
  !xs a s t.
  bb.bb_instructions = a ++ xs ++ b /\ s.vs_inst_idx = LENGTH a ==>
  (inv_ev_ftrace orc p d ctx xs s t <=>
   inv_ev_prefix orc p d ctx bb (LENGTH xs) s t)
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  simp[inv_ev_ftrace_def, inv_ev_prefix_suc] >>
  `!u. inv_ev_ftrace orc p d ctx xs
          (u with vs_inst_idx := SUC s.vs_inst_idx) t <=>
        inv_ev_prefix orc p d ctx bb (LENGTH xs)
          (u with vs_inst_idx := SUC s.vs_inst_idx) t` by
    (gen_tac >> first_x_assum irule >>
     qexists_tac `a ++ [h]` >> simp[APPEND_ASSOC]) >>
  metis_tac[]
QED

Theorem inv_ev_flip_step:
  is_flippable i.inst_opcode ==>
  ev_step orc p d fuel ctx (flip_operands i) s =
  ev_step orc p d fuel ctx i s
Proof
  strip_tac >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  `~MEM (flip_operands i).inst_opcode [GAS; INVOKE]` by
    metis_tac[flip_operands_special_opcode, MEM] >>
  gvs[MEM] >> simp[ev_step_def] >> irule flip_operands_step_inst_base >> simp[]
QED

Theorem inv_ev_flip_nonterminator:
  is_flippable i.inst_opcode ==>
  ~is_terminator i.inst_opcode /\
  ~is_terminator (flip_operands i).inst_opcode
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def,
       is_terminator_def] >>
  Cases_on `i.inst_operands` >> simp[flip_operands_def, is_terminator_def] >>
  rename1 `i.inst_operands = op1::ops1` >>
  Cases_on `ops1` >> simp[flip_operands_def, is_terminator_def] >>
  rename1 `i.inst_operands = op1::op2::ops2` >>
  Cases_on `ops2` >>
  simp[flip_operands_def, is_comparator_def, flip_comparison_opcode_def,
       is_terminator_def]
QED

Theorem inv_ev_ftrace_flip:
  is_flippable i.inst_opcode ==>
  (inv_ev_ftrace orc p d ctx (flip_operands i::xs) s t <=>
   inv_ev_ftrace orc p d ctx (i::xs) s t)
Proof
  strip_tac >> drule inv_ev_flip_nonterminator >> strip_tac >>
  simp[inv_ev_ftrace_def, inv_ev_flip_step]
QED

Theorem inv_ev_ftrace_adjacent_exchange:
  dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  inv_ev_ftrace orc p d ctx (pre ++ y::x::post) s t ==>
  inv_ev_ftrace orc p d ctx (pre ++ x::y::post) s t
Proof
  simp[inv_ev_ftrace_append] >> metis_tac[inv_ev_ftrace_exchange]
QED

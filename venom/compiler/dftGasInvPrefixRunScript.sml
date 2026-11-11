Theory dftGasInvPrefixRun
Ancestors
  dftGasInvFuel dftGasOracleDefs

Definition inv_ev_prefix_def:
  (inv_ev_prefix orc p d ctx bb 0 s t <=> s = t) /\
  (inv_ev_prefix orc p d ctx bb (SUC n) s t <=>
    ?inst u fuel.
      get_instruction bb s.vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\
      ev_step orc p d fuel ctx inst s = OK u /\
      inv_ev_prefix orc p d ctx bb n
        (u with vs_inst_idx := SUC s.vs_inst_idx) t)
End

Theorem inv_ev_prefix_zero[simp]:
  inv_ev_prefix orc p d ctx bb 0 s t <=> s = t
Proof
  simp[inv_ev_prefix_def]
QED

Theorem inv_ev_prefix_suc:
  inv_ev_prefix orc p d ctx bb (SUC n) s t <=>
  ?inst u fuel.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    ev_step orc p d fuel ctx inst s = OK u /\
    inv_ev_prefix orc p d ctx bb n
      (u with vs_inst_idx := SUC s.vs_inst_idx) t
Proof
  simp[Once inv_ev_prefix_def]
QED

Theorem inv_ev_prefix_compose:
  !n s u m t.
    inv_ev_prefix orc p d ctx bb n s u /\
    inv_ev_prefix orc p d ctx bb m u t ==>
    inv_ev_prefix orc p d ctx bb (n + m) s t
Proof
  Induct >> simp[inv_ev_prefix_suc, arithmeticTheory.ADD_CLAUSES] >>
  rpt strip_tac >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem inv_ev_prefix_suffix:
  !n s t fuel r.
    inv_ev_prefix orc p d ctx bb n s t /\
    ev_block orc p d fuel ctx bb t = r /\
    (!msg. r <> Error msg) ==>
    ?joined_fuel. ev_block orc p d joined_fuel ctx bb s = r
Proof
  Induct >> simp[inv_ev_prefix_suc] >- metis_tac[] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
  rename1 `ev_step orc p d head_fuel ctx inst s = OK u` >>
  rename1 `ev_block orc p d tail_fuel ctx bb
    (u with vs_inst_idx := SUC s.vs_inst_idx) = r` >>
  qexists_tac `head_fuel + tail_fuel` >>
  `ev_step orc p d (head_fuel + tail_fuel) ctx inst s = OK u` by
    (irule ev_step_fuel_extend >> simp[]) >>
  once_rewrite_tac[ev_block_def] >> simp[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ev_block_fuel_extend >> simp[]
QED

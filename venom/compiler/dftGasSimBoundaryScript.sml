Theory dftGasSimBoundary
Ancestors
  dftGasOracleDefs dftPermSim dftStructural dftLifting dftShape dftDefs list venomState venomInst venomEffects passSharedDefs

Theorem ev_step_gas:
  inst.inst_opcode = GAS ==>
  ev_step orc p d fuel ctx inst s = ev_gas (orc (p,d,inst.inst_id)) inst s
Proof
  simp[Once ev_step_def]
QED

Theorem ev_gas_readings:
  ev_gas w inst s = OK t ==> t.vs_gas_readings = s.vs_gas_readings
Proof
  simp[ev_gas_def] >> Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
  simp[update_var_def] >> strip_tac >> gvs[]
QED

Definition ev_suffix_def:
  (ev_suffix orc p d fuel ctx [] s = Error "block not terminated") /\
  (ev_suffix orc p d fuel ctx (inst::rest) s =
    case ev_step orc p d fuel ctx inst s of
      OK t => if is_terminator inst.inst_opcode then
                if t.vs_halted then Halt t else OK t
              else ev_suffix orc p d fuel ctx rest
                     (t with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet vals t => IntRet vals t
    | Halt t => Halt t
    | Abort a t => Abort a t
    | Error e => Error e)
End

Theorem ev_suffix_block:
  !xs s bb. xs = DROP s.vs_inst_idx bb.bb_instructions ==>
    ev_suffix orc p d fuel ctx xs s = ev_block orc p d fuel ctx bb s
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bb.bb_instructions <= s.vs_inst_idx` by
        (qpat_x_assum `_ = DROP _ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
      simp[Once ev_block_def, get_instruction_def, ev_suffix_def]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `_ = DROP _ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[] >> decide_tac) >>
  `EL s.vs_inst_idx bb.bb_instructions = h` by
    (qpat_x_assum `_ = DROP _ _` (mp_tac o AP_TERM ``HD : instruction list -> instruction``) >> simp[HD_DROP]) >>
  once_rewrite_tac[ev_block_def] >>
  simp[ev_suffix_def, get_instruction_def] >>
  Cases_on `ev_step orc p d fuel ctx h s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum irule >> simp[] >>
  `!n (bi:instruction list). TL (DROP n bi) = DROP (SUC n) bi` by
    (Induct >> Cases_on `bi` >> simp[]) >>
  qpat_x_assum `_ = DROP _ _` (mp_tac o AP_TERM ``TL : instruction list -> instruction list``) >>
  simp[]
QED

Theorem flip_operands_ev_step:
  is_flippable i.inst_opcode ==>
  ev_step orc p d fuel ctx (flip_operands i) s = ev_step orc p d fuel ctx i s
Proof
  strip_tac >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  drule flip_operands_special_opcode >> simp[] >> strip_tac >>
  simp[Once ev_step_def] >>
  simp[Once ev_step_def] >>
  irule flip_operands_step_inst_base >> simp[]
QED

Theorem ev_step_gas_index:
  inst.inst_opcode = GAS ==>
  ev_step orc p d fuel ctx inst (s with vs_inst_idx := n) =
    case ev_step orc p d fuel ctx inst s of
      OK t => OK (t with vs_inst_idx := n)
    | other => other
Proof
  simp[ev_step_gas, ev_gas_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
  simp[update_var_def]
QED

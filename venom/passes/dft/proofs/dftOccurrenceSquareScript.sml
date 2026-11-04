Theory dftOccurrenceSquare
Ancestors
  dftOccurrenceReplay dftScheduleOrder arithmetic dftOccurrenceMachine
  dftOpenErase dftOpenMachine venomExecSemantics venomInst venomState
  venomEffects list finite_map

(* Bounded certificates, not a global schedule simulation relation. *)
Datatype:
  dft_square_pos = SqBefore | SqMiddle | SqAfter
End

Datatype:
  dft_occ_square = <| sq_l0 : dft_occ_config;
                      sq_l1 : dft_occ_config;
                      sq_l2 : dft_occ_config;
                      sq_r0 : dft_occ_config;
                      sq_r1 : dft_occ_config;
                      sq_r2 : dft_occ_config |>
End

Definition dft_square_pick_def:
  (dft_square_pick SqBefore a b c = a) /\
  (dft_square_pick SqMiddle a b c = b) /\
  (dft_square_pick SqAfter a b c = c)
End

Definition dft_square_depth_def:
  (dft_square_depth SqBefore = (0:num)) /\
  (dft_square_depth SqMiddle = 1) /\
  (dft_square_depth SqAfter = 2)
End

Definition dft_occ_at_join_def:
  dft_occ_at_join l r <=>
    l.dft_occ_path = r.dft_occ_path /\
    l.dft_occ_visit = r.dft_occ_visit /\
    l.dft_occ_saved = r.dft_occ_saved /\
    ?fn fn' bb bb' s stack n.
      l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
      r.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack n
End

Definition dft_occ_square_ok_def:
  dft_occ_square_ok w C C' q <=>
    dft_occ_oracle_next w C q.sq_l0 = q.sq_l1 /\
    dft_occ_oracle_next w C q.sq_l1 = q.sq_l2 /\
    dft_occ_oracle_next w C' q.sq_r0 = q.sq_r1 /\
    dft_occ_oracle_next w C' q.sq_r1 = q.sq_r2 /\
    dft_occ_at_join q.sq_l2 q.sq_r2
End

Definition dft_occ_square_phase_def:
  dft_occ_square_phase q p p' l r <=>
    l = dft_square_pick p q.sq_l0 q.sq_l1 q.sq_l2 /\
    r = dft_square_pick p' q.sq_r0 q.sq_r1 q.sq_r2
End

Theorem dft_occ_square_left_prefix:
  dft_occ_square_ok w C C' q ==>
  FUNPOW (dft_occ_oracle_next w C) (dft_square_depth p) q.sq_l0 =
  dft_square_pick p q.sq_l0 q.sq_l1 q.sq_l2
Proof
  Cases_on `p` >> simp[dft_occ_square_ok_def, dft_square_depth_def,
                          dft_square_pick_def, FUNPOW_2, FUNPOW]
QED

Theorem dft_occ_square_right_prefix:
  dft_occ_square_ok w C C' q ==>
  FUNPOW (dft_occ_oracle_next w C') (dft_square_depth p) q.sq_r0 =
  dft_square_pick p q.sq_r0 q.sq_r1 q.sq_r2
Proof
  Cases_on `p` >> simp[dft_occ_square_ok_def, dft_square_depth_def,
                          dft_square_pick_def, FUNPOW_2, FUNPOW]
QED

Theorem dft_occ_square_after_join:
  dft_occ_square_ok w C C' q /\
  dft_occ_square_phase q SqAfter SqAfter l r ==> dft_occ_at_join l r
Proof
  simp[dft_occ_square_ok_def, dft_occ_square_phase_def,
       dft_square_pick_def]
QED

Theorem dft_occ_square_phase_pick:
  dft_occ_square_phase q p p'
    (dft_square_pick p q.sq_l0 q.sq_l1 q.sq_l2)
    (dft_square_pick p' q.sq_r0 q.sq_r1 q.sq_r2)
Proof
  simp[dft_occ_square_phase_def]
QED

Definition dft_square_start_def:
  dft_square_start fn bb s path visit n =
    <|dft_occ_core := DftOpen (DftAt fn 0 bb (s with vs_inst_idx := 0)) [] n;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := []|>
End

Definition dft_gas_square_def:
  dft_gas_square w C C' fn bb s path visit n x y =
    let l0 = dft_square_start fn (bb with bb_instructions := [x;y]) s path visit n;
        r0 = dft_square_start fn (bb with bb_instructions := [y;x]) s path visit n;
        l1 = dft_occ_oracle_next w C l0;
        r1 = dft_occ_oracle_next w C' r0 in
    <|sq_l0 := l0; sq_l1 := l1; sq_l2 := dft_occ_oracle_next w C l1;
      sq_r0 := r0; sq_r1 := r1; sq_r2 := dft_occ_oracle_next w C' r1|>
End

Theorem dft_gas_square_ok:
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id ==>
  dft_occ_square_ok w C C'
    (dft_gas_square w C C' fn bb s path visit n x y)
Proof
  strip_tac >>
  simp[dft_occ_square_ok_def, dft_gas_square_def, dft_square_start_def] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_occ_address_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_erase_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       get_instruction_def, is_terminator_def, dft_occ_update_def,
       update_var_def] >>
  simp[dft_occ_at_join_def, FUPDATE_COMMUTES]
QED

Theorem dft_gas_square_no_forward_edge:
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] ==>
  ~dft_must_order x y
Proof
  simp[dft_must_order_def, inst_defs_def, inst_uses_def, operand_vars_def,
       read_effects_def, write_effects_def, empty_effects_def,
       is_terminator_def]
QED

Theorem dft_gas_square_no_reverse_edge:
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] ==>
  ~dft_must_order y x
Proof
  metis_tac[dft_gas_square_no_forward_edge]
QED

Theorem dft_gas_square_inhabited:
  u <> v ==>
  dft_occ_square_ok w C C'
    (dft_gas_square w C C' fn bb s path visit n
      (i with <|inst_opcode := GAS; inst_outputs := [u];
                inst_operands := []; inst_id := 0|>)
      (i with <|inst_opcode := GAS; inst_outputs := [v];
                inst_operands := []; inst_id := 1|>))
Proof
  strip_tac >> irule dft_gas_square_ok >> simp[]
QED

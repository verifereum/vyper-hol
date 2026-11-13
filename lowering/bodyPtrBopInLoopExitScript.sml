(* A fragment may stop at raw jump_to, before any continuation PHIs.
   In's open exit uses this endpoint; NotIn has an actual ISZERO prefix. *)
Theory bodyPtrBopInLoopExit
Ancestors fragGasPathPtr venomState

(* Unlike emit_jump_zero_path_ptr this boundary also applies to a selected
   JNZ successor, at an arbitrary source instruction and gas count. *)
Theorem raw_jump_edge_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK (jump_to lbl s) /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s
    (gas_count_step fuel ctx inst s) G tn (OK (jump_to lbl s))
Proof
  strip_tac >> rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `fuel` >> simp[] >>
  disj2_tac >> disj1_tac >>
  qexists_tac `lbl` >> simp[]
QED

Theorem raw_jump_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK (jump_to lbl s) /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
  gas_path_ptr D lo ctx fn PG G tn s
    (gas_count_step fuel ctx inst s) G tn (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all raw_jump_edge_ptr >> strip_tac >>
  `gas_path_ptr D lo ctx fn PG G tn (jump_to lbl s) 0 G tn
     (OK (jump_to lbl s))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[jump_to_def]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED

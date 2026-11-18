Theory bodyFullStoreSlotsStaticSeparation
Ancestors
  venomExecSemantics venomState venomInst list arithmetic words
  emitHelperProps transientLockProps

Theorem slots_bank_operand[local,simp]:
  eval_operand op (s with <|vs_transient := ts; vs_accounts := ac|>) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem slots_bank_update_var[local,simp]:
  update_var x v (s with <|vs_transient := ts; vs_accounts := ac|>) =
  (update_var x v s) with <|vs_transient := ts; vs_accounts := ac|>
Proof
  simp[update_var_def]
QED

Theorem slots_bank_jump[local,simp]:
  jump_to lbl (s with <|vs_transient := ts; vs_accounts := ac|>) =
  (jump_to lbl s) with <|vs_transient := ts; vs_accounts := ac|>
Proof
  simp[jump_to_def]
QED

Theorem slots_bank_step[local]:
  MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx i s = OK u ==>
  step_inst fuel ctx i (s with <|vs_transient := ts; vs_accounts := ac|>) =
    OK (u with <|vs_transient := ts; vs_accounts := ac|>)
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure1_def, exec_pure2_def, exec_read1_def, AllCaseEqs()] >>
  simp[mload_def]
QED

(* A trace records states after advancing the instruction index, or after
   a jump into a block with no leading PHIs. The same fetched instruction
   and the same operand and memory observations are retained on replay. *)
Theorem slots_readonly_bank_replay:
  !L fuel ctx func ac ts.
  (!n. SUC n < LENGTH L ==>
    ?bb i u.
      lookup_block (EL n L).vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (EL n L).vs_inst_idx = SOME i /\
      MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
      step_inst fuel ctx i (EL n L) = OK u /\
      EL (SUC n) L =
        (if is_terminator i.inst_opcode then u
         else u with vs_inst_idx := SUC (EL n L).vs_inst_idx)) ==>
  !replay. replay = MAP (\s. s with <|vs_transient := ts; vs_accounts := ac|>) L ==>
    LENGTH replay = LENGTH L /\
    (!n. n < LENGTH L ==>
      (EL n replay).vs_current_bb = (EL n L).vs_current_bb /\
      (EL n replay).vs_inst_idx = (EL n L).vs_inst_idx /\
      (!op. eval_operand op (EL n replay) = eval_operand op (EL n L)) /\
      (!a. mload a (EL n replay) = mload a (EL n L))) /\
    (!n. SUC n < LENGTH L ==>
      ?bb i u.
        lookup_block (EL n replay).vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (EL n replay).vs_inst_idx = SOME i /\
        get_instruction bb (EL n L).vs_inst_idx = SOME i /\
        MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
        step_inst fuel ctx i (EL n replay) = OK u /\
        EL (SUC n) replay =
          (if is_terminator i.inst_opcode then u
           else u with vs_inst_idx := SUC (EL n replay).vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> disch_then SUBST1_TAC >>
  simp[] >>
  conj_tac >- simp[EL_MAP, mload_def] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all slots_bank_step >> strip_tac >>
  qexistsl_tac [`bb`, `i`, `u with <|vs_transient := ts; vs_accounts := ac|>`] >>
  simp[EL_MAP] >>
  Cases_on `is_terminator i.inst_opcode` >>
  gvs[venom_state_component_equality]
QED

(* R is the supplied readonly execution to the cut; S is the supplied
   successful completion relation. Only endpoint uniqueness connects them.
   In particular this does not assume that a fold changes every input. *)
Theorem slots_readonly_positive_separation:
  (!w. R ((if tr then tstore else sstore) key w s)
          ((if tr then tstore else sstore) key w t)) /\
  (!a b c. R a b /\ success a c ==> b = c) /\
  (!w. ?u.
    success ((if tr then tstore else sstore) key w s) u /\
    (if tr then tload else sload) key u =
      (if tr then tload else sload) key
        (FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
           (mload (w2n sw+32*j) s) q)
          ((if tr then tstore else sstore) key w s) ks)) /\
  (!w. (if tr then tload else sload) key
      (FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
         (mload (w2n sw+32*j) s) q)
        ((if tr then tstore else sstore) key w s) ks) = value) ==>
  F
Proof
  strip_tac >>
  qpat_x_assum `!w. ?u. _` (qspec_then `value + 1w` strip_assume_tac) >>
  `u = (if tr then tstore else sstore) key (value + 1w) t` by
    metis_tac[] >>
  `value + 1w = value` by
    (Cases_on `tr` >> gvs[sload_sstore_same, tload_tstore_same] >>
     metis_tac[]) >>
  gvs[WORD_ADD_INV_0_EQ]
QED

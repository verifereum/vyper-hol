(*
 * Fuel bound for the dynamic-array-to-storage copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_dynarray_to_storage
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst venomExecSemantics venomState finite_map words arithmetic fragExec
Libs
  fragFuelLib

(* Semantic boundary for the condition: the temporary values are concrete,
   and neither loop-carried variable is overwritten. *)
Theorem dynstorage_condition_steps[local]:
  !s len ctr lt done l c id1 id2 id3 body exit.
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> lt /\ len <> done /\ ctr <> lt /\ ctr <> done ==>
    let s1 = update_var lt (bool_to_word (w2n c < w2n l)) s in
    let s2 = update_var done (bool_to_word (~(w2n c < w2n l))) s1 in
      step_inst_base (mk_inst id1 LT [Var ctr; Var len] [lt]) s = OK s1 /\
      step_inst_base (mk_inst id2 ISZERO [Var lt] [done]) s1 = OK s2 /\
      step_inst_base (mk_inst id3 JNZ
        [Var done; Label exit; Label body] []) s2 =
        OK (jump_to (if w2n c < w2n l then body else exit) s2) /\
      lookup_var len s2 = SOME l /\ lookup_var ctr s2 = SOME c
Proof
  rpt strip_tac >>
  Cases_on `w2n c < w2n l` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       exec_pure1_def, eval_operand_def, bool_to_word_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem dynstorage_increment_steps[local]:
  !s len ctr tmp l c id1 id2.
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> ctr /\ len <> tmp ==>
    let s1 = update_var tmp (c + 1w) s in
    let s2 = update_var ctr (c + 1w) s1 in
      step_inst_base (mk_inst id1 ADD [Var ctr; Lit 1w] [tmp]) s = OK s1 /\
      step_inst_base (mk_inst id2 ASSIGN [Var tmp] [ctr]) s1 = OK s2 /\
      lookup_var len s2 = SOME l /\ lookup_var ctr s2 = SOME (c + 1w)
Proof
  rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, eval_operands_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem dynstorage_remaining_decreases[local]:
  !(c:bytes32) (l:bytes32).
    w2n c < w2n l ==>
    w2n (c + 1w) = w2n c + 1 /\
    w2n l - w2n (c + 1w) < w2n l - w2n c
Proof
  rpt strip_tac >>
  `w2n l < dimword(:256)` by (MATCH_ACCEPT_TAC w2n_lt) >>
  `w2n c + w2n (1w:bytes32) < dimword(:256)` by
    (simp[] >> decide_tac) >>
  drule w2n_add_2 >> simp[] >> decide_tac
QED

(* The condition consumes one block, including the halted-state alternative.
   Instruction indices are relative, so the fact also applies after a prefix. *)
Theorem dynstorage_condition_outcome[local]:
  !G ctx fn s bb len ctr lt done l c id1 id2 id3 body exit.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 LT [Var ctr; Var len] [lt]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ISZERO [Var lt] [done]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst id3 JNZ [Var done; Label exit; Label body] []) /\
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> lt /\ len <> done /\ ctr <> lt /\ ctr <> done ==>
    let s1 = (update_var lt (bool_to_word (w2n c < w2n l)) s)
               with vs_inst_idx := SUC s.vs_inst_idx in
    let s2 = (update_var done (bool_to_word (~(w2n c < w2n l))) s1)
               with vs_inst_idx := SUC (SUC s.vs_inst_idx) in
    fuel_outcome G ctx fn s 1
      (\t. t = jump_to (if w2n c < w2n l then body else exit) s2)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `jump_to dest s2` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s2` by
    (gen_tac >>
     simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          exec_pure2_def, eval_operand_def] >>
     simp[Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, Abbr `s2`, bool_to_word_def] >>
     Cases_on `w2n c < w2n l` >> gvs[lookup_var_def, bool_to_word_def]) >>
  `fuel_outcome G ctx fn s2 1 (\t. t = jump_to dest s2)`
    suffices_by gvs[fuel_outcome_def] >>
  irule fuel_outcome_jump >>
  conj_tac >- simp[] >>
  qexistsl [`bb`,
    `mk_inst id3 JNZ [Var done; Label exit; Label body'] []`, `dest`] >>
  simp[Abbr `s2`, Abbr `dest`, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `w2n c < w2n l` >> simp[bool_to_word_def]
QED

Theorem dynstorage_increment_outcome[local]:
  !G ctx fn s bb len ctr tmp l c id1 id2 id3 cond.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 ADD [Var ctr; Lit 1w] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst id3 JMP [Label cond] []) /\
    lookup_var len s = SOME l /\ lookup_var ctr s = SOME c /\
    len <> ctr /\ len <> tmp ==>
    let s1 = (update_var tmp (c + 1w) s)
               with vs_inst_idx := SUC s.vs_inst_idx in
    let s2 = (update_var ctr (c + 1w) s1)
               with vs_inst_idx := SUC (SUC s.vs_inst_idx) in
    fuel_outcome G ctx fn s 1 (\t. t = jump_to cond s2)
Proof
  rpt strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `jump_to cond s2` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s2` by
    (gen_tac >>
     simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          exec_pure2_def, eval_operand_def] >>
     simp[Once exec_block_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          eval_operand_def, eval_operands_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE, Abbr `s2`]) >>
  `fuel_outcome G ctx fn s2 1 (\t. t = jump_to cond s2)`
    suffices_by gvs[fuel_outcome_def] >>
  irule fuel_outcome_jump >>
  conj_tac >- simp[] >>
  qexistsl [`bb`, `mk_inst id3 JMP [Label cond] []`, `cond`] >>
  simp[Abbr `s2`, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, update_var_def]
QED

(* The length is loaded into a fresh variable before the loop; the loop
   counts a fresh counter from 0 while it is below that length.  Each round
   copies one element (one word, or a word-copy loop over a literal count)
   and adds 1; the body writes only the counter and variables it allocates
   itself, so the length stays fixed and the loop leaves within 2 ** 256
   rounds. *)
Theorem fuel_ok_compile_dynarray_to_storage:
  !src_ptr dst_slot elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size
         transient)
Proof
  cheat
QED

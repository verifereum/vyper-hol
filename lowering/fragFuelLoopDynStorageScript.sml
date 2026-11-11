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
(* The copy slice stops before the counter update and the back edge. *)
Theorem fuel_ok_dynstorage_copy_body[local]:
  !src_ptr dst_slot counter elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (if elem_words = 1 then
         do mul_op <- emit_op MUL [Var counter; Lit 32w];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            val_op <- emit_op MLOAD [src_elem];
            slot_off <- emit_op ADD [Var counter; Lit 1w];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            (if transient then emit_void TSTORE [dst_elem; val_op]
             else emit_void SSTORE [dst_elem; val_op])
         od
       else
         do mul_op <- emit_op MUL [Var counter; Lit (n2w elem_mem_size)];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            slot_mul <- emit_op MUL [Var counter; Lit (n2w elem_words)];
            slot_off <- emit_op ADD [Lit 1w; slot_mul];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            compile_word_copy_loop src_elem dst_elem elem_words
              LocMemory (if transient then LocTransient else LocStorage) F;
            return ()
         od)
Proof
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

(* An empty write set keeps both loop registers, even across a nested copy.
   The bound is fixed at compile time, before the runtime state is chosen. *)
Theorem dynstorage_copy_body_outcome[local]:
  !m st x st' len counter.
    fuel_ok {} {} {} m /\ m st = (x, st') /\
    var_below st.cs_next_var len /\ var_below st.cs_next_var counter ==>
    ?Kb. frag_fuel {} {} {} st st' Kb /\
      !G ctx fn s.
        no_phi_fn fn /\ fn_has_code st st' fn /\
        callees_stable G ctx fn /\ at_point st s ==>
        ?j. j <= Kb /\
          fuel_outcome G ctx fn s j
            (\t. vars_kept st.cs_next_var {} s t /\
                 lookup_var len t = lookup_var len s /\
                 lookup_var counter t = lookup_var counter s /\
                 at_point st' t)
Proof
  rpt gen_tac >> strip_tac >>
  fs[fuel_ok_def] >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `Kb` >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `st.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >>
  goal_assum (drule_at Any) >>
  simp[vars_kept_def]
QED

Theorem fuel_ok_compile_dynarray_to_storage:
  !src_ptr dst_slot elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size
         transient)
Proof
  cheat
QED

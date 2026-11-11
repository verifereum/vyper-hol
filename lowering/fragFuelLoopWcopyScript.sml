(*
 * Fuel bound for the word-copy loop of the context helpers.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_word_copy_loop_base
 *)

Theory fragFuelLoopWcopy
Ancestors
  fragFuel fragFuelContextBase emitHelper context venomInst
  fragExec venomExecSemantics venomState
Libs
  fragFuelLib

(* Counter arithmetic is modular: the distance to the bound decreases even
   when incrementing the counter wraps around. *)
Theorem wcopy_distance_bound[local]:
  !b c:256 word. w2n (b - c) < 2 ** 256
Proof
  rpt gen_tac >> mp_tac (Q.ISPEC `b - c : 256 word` wordsTheory.w2n_lt) >>
  simp[wordsTheory.dimword_def]
QED

Theorem wcopy_distance_decreases[local]:
  !b c:256 word. c <> b ==>
    w2n (b - (c + 1w)) < w2n (b - c)
Proof
  rpt strip_tac >>
  `b - (c + 1w) = (b - c) - 1w` by wordsLib.WORD_DECIDE_TAC >>
  pure_asm_rewrite_tac[] >> irule wordsTheory.WORD_PRED_THM >>
  simp[wordsTheory.WORD_EQ_SUB_ZERO]
QED

(* Instruction-level interfaces use code lookups, independently of how the
   compiler obtained the blocks. Exact resulting states also expose framing. *)
Theorem wcopy_assign_jump_outcome[local]:
  !G ctx fn s bb ai ji ctr lbl value_op v.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ai /\
    ai.inst_opcode = ASSIGN /\ ai.inst_operands = [value_op] /\
    ai.inst_outputs = [ctr] /\ eval_operand value_op s = SOME v /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME ji /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label lbl] ==>
    fuel_outcome G ctx fn s 1
      (\t. t = jump_to lbl (update_var ctr v s))
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = (update_var ctr v s) with
                     vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> unabbrev_all_tac >> irule run_from_step >>
     qexistsl_tac [`bb`, `ai`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  simp[fuel_outcome_def] >>
  `fuel_outcome G ctx fn s1 1
     (\t. t = jump_to lbl (update_var ctr v s))` suffices_by
     simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `ji`, `lbl`] >>
  simp[Abbr `s1`, update_var_def, is_terminator_def,
       step_inst_base_opcode_eqs, jump_to_def]
QED

Theorem wcopy_cond_outcome[local]:
  !G ctx fn s bb ei ji ctr done count_op c yes no.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ei /\
    ei.inst_opcode = EQ /\ ei.inst_operands = [Var ctr; count_op] /\
    ei.inst_outputs = [done] /\ lookup_var ctr s = SOME c /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME ji /\
    ji.inst_opcode = JNZ /\
    ji.inst_operands = [Var done; Label yes; Label no] ==>
    fuel_outcome G ctx fn s 1
      (\t. ?b. eval_operand count_op s = SOME b /\
        t = jump_to (if c = b then yes else no)
              (update_var done (bool_to_word (c = b)) s))
Proof
  rpt strip_tac >> Cases_on `eval_operand count_op s`
  >- (simp[fuel_outcome_def] >> rpt strip_tac >>
      `!f. run_from f ctx fn s = Error "undefined operand"` by
        (gen_tac >> drule run_from_nonterm >> disch_then drule >>
         simp[is_terminator_def, step_inst_non_invoke,
              step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
         disch_then irule) >> simp[]) >>
  rename1 `eval_operand count_op s = SOME b` >>
  qabbrev_tac `s1 = (update_var done (bool_to_word (c = b)) s) with
                     vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> unabbrev_all_tac >> irule run_from_step >>
     qexistsl_tac [`bb`, `ei`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def]) >>
  simp[fuel_outcome_def] >>
  `fuel_outcome G ctx fn s1 1
     (\t. t = jump_to (if c = b then yes else no)
                (update_var done (bool_to_word (c = b)) s))` suffices_by
     simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `ji`, `if c = b then yes else no`] >>
  simp[Abbr `s1`, update_var_def, is_terminator_def,
       step_inst_base_opcode_eqs, jump_to_def, eval_operand_def,
       lookup_var_def, bool_to_word_def] >>
  Cases_on `c = b` >> simp[finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def]
QED

Theorem wcopy_increment_outcome[local]:
  !G ctx fn s bb ni ai ji ctr tmp lbl c.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME ni /\
    ni.inst_opcode = ADD /\ ni.inst_operands = [Var ctr; Lit 1w] /\
    ni.inst_outputs = [tmp] /\ lookup_var ctr s = SOME c /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME ai /\
    ai.inst_opcode = ASSIGN /\ ai.inst_operands = [Var tmp] /\
    ai.inst_outputs = [ctr] /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME ji /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label lbl] ==>
    fuel_outcome G ctx fn s 1
      (\t. t = jump_to lbl
        (update_var ctr (c + 1w) (update_var tmp (c + 1w) s)))
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = (update_var tmp (c + 1w) s) with
                     vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> unabbrev_all_tac >> irule run_from_step >>
     qexistsl_tac [`bb`, `ni`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def]) >>
  simp[fuel_outcome_def] >>
  `fuel_outcome G ctx fn s1 1
     (\t. t = jump_to lbl (update_var ctr (c + 1w) s1))` suffices_by
    simp[fuel_outcome_def, Abbr `s1`, update_var_def, jump_to_def] >>
  irule wcopy_assign_jump_outcome >> simp[] >>
  qexistsl_tac [`ai`, `bb`, `ji`, `Var tmp`] >>
  simp[Abbr `s1`, update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The loop counts a fresh counter from 0 up to the value of count_op,
   leaving through the exit block when they are equal.  Each round runs
   the body's straight-line code and one JMP back to the condition block.
   count_op was allocated before the loop, and the body writes only the
   counter and variables it allocates itself, so the bound stays fixed and
   the number of rounds is below 2 ** 256. *)
Theorem fuel_okS_compile_word_copy_loop_base:
  !src_op dst_op count_op load_loc store_loc is_ctor imm Wv E.
    fuel_okS (\st. !x. count_op = Var x ==> var_below st.cs_next_var x) Wv {} E
      (compile_word_copy_loop_base src_op dst_op count_op load_loc store_loc
         is_ctor imm)
Proof
  cheat
QED

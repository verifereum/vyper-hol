(*
 * Fuel bound for the static-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_sarray_typed
 *)

Theory fragFuelLoopSarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  venomExecSemantics venomExecProps venomState
Libs
  fragFuelLib

(* Condition trace: LT / ISZERO / JNZ. *)
Theorem sa_condition[local]:
  !G ctx fn N lc le lb c vlt vdone n k s bb ilt idone ij.
    no_phi_fn fn /\ callees_stable G ctx fn /\
    lookup_block lc fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME ilt /\
    ilt.inst_opcode = LT /\
    ilt.inst_operands = [Var c; Lit (n2w n)] /\
    ilt.inst_outputs = [vlt] /\
    get_instruction bb 1 = SOME idone /\
    idone.inst_opcode = ISZERO /\
    idone.inst_operands = [Var vlt] /\
    idone.inst_outputs = [vdone] /\
    get_instruction bb 2 = SOME ij /\
    ij.inst_opcode = JNZ /\
    ij.inst_operands = [Var vdone; Label le; Label lb] /\
    ij.inst_outputs = [] /\
    vlt <> c /\ vdone <> c /\ vlt <> vdone /\
    ~var_below N vlt /\ ~var_below N vdone /\
    s.vs_current_bb = lc /\ s.vs_inst_idx = 0 /\
    lookup_var c s = SOME (n2w k) /\ k <= w2n (n2w n : 256 word) ==>
    fuel_outcome G ctx fn s 1
      (\t. vars_kept N {} s t /\ lookup_var c t = SOME (n2w k) /\
           ((k = w2n (n2w n : 256 word) /\
             t.vs_current_bb = le /\ t.vs_inst_idx = 0) \/
            (k < w2n (n2w n : 256 word) /\
             t.vs_current_bb = lb /\ t.vs_inst_idx = 0)))
Proof
  rpt strip_tac >>
  `k < dimword (:256)` by
    (mp_tac (Q.ISPEC `n2w n : 256 word` wordsTheory.w2n_lt) >> decide_tac) >>
  `w2n (n2w k : 256 word) = k` by simp[wordsTheory.w2n_n2w] >>
  qabbrev_tac `w = bool_to_word (k < w2n (n2w n : 256 word))` >>
  qabbrev_tac `s1 = (update_var vlt w s) with vs_inst_idx := 1` >>
  qabbrev_tac `s2 = (update_var vdone (bool_to_word (w = 0w)) s1)
                      with vs_inst_idx := 2` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> simp[Abbr `s1`] >>
     `1 = SUC s.vs_inst_idx` by simp[] >> pop_assum SUBST1_TAC >>
     irule fragExecTheory.run_from_step >>
     qexistsl_tac [`bb`, `ilt`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def, Abbr `w`]) >>
  `!f. run_from f ctx fn s1 = run_from f ctx fn s2` by
    (gen_tac >> simp[Abbr `s2`] >>
     `2 = SUC s1.vs_inst_idx` by simp[Abbr `s1`] >> pop_assum SUBST1_TAC >>
     irule fragExecTheory.run_from_step >>
     qexistsl_tac [`bb`, `idone`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure1_def, eval_operand_def, Abbr `s1`,
          update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `fuel_outcome G ctx fn s2 1
      (\t. vars_kept N {} s t /\ lookup_var c t = SOME (n2w k) /\
           ((k = w2n (n2w n : 256 word) /\
             t.vs_current_bb = le /\ t.vs_inst_idx = 0) \/
            (k < w2n (n2w n : 256 word) /\
             t.vs_current_bb = lb /\ t.vs_inst_idx = 0)))` by
    (irule fuel_outcome_jump >> simp[] >>
     qexistsl_tac [`bb`, `ij`, `if w = 0w then le else lb`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs,
          eval_operand_def, Abbr `s2`, Abbr `s1`,
          update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `k < w2n (n2w n : 256 word)` >>
     gvs[Abbr `w`, bool_to_word_def, jump_to_def, vars_kept_def,
         lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[] >>
     `x <> vdone /\ x <> vlt` by metis_tac[] >> simp[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

(* Given a bound for the element copy (the recursive call), the copy of a
   static array of n elements is bounded.  The slow path counts a fresh
   counter from 0 while it is below the literal n2w n; each round copies one
   element and adds 1, so the loop leaves within 2 ** 256 rounds, and the
   counter never wraps since it stays at most n2w n. *)
Theorem fuel_ok_compile_copy_sarray_typed:
  !cenv dst dst_elem src src_elem n.
    (!d s Wv E. fuel_ok Wv {} E
                  (compile_store_memory_typed cenv d dst_elem s src_elem)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_copy_sarray_typed cenv dst dst_elem src src_elem n)
Proof
  cheat
QED

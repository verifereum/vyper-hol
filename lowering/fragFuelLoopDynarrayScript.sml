(*
 * Fuel bound for the dynamic-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_dynarray_typed
 *)

Theory fragFuelLoopDynarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  fragExec venomExecSemantics venomState venomInstProps words arithmetic
Libs
  fragFuelLib

(* The body may allocate temporaries and change memory freely.  Its empty
   write-set instance keeps every earlier variable, and frames the entry
   variables through the fragment. *)
Theorem dynarray_body_outcome[local]:
  !G N ctx fn st st' Kbody s entry Wv.
    frag_fuel {} {} {} st st' Kbody /\
    no_phi_fn fn /\ fn_has_code st st' fn /\ callees_stable G ctx fn /\
    at_point st s /\ N <= st.cs_next_var /\ vars_kept N Wv entry s ==>
    ?j. j <= Kbody /\ fuel_outcome G ctx fn s j
      (\t. at_point st' t /\ vars_kept st.cs_next_var {} s t /\
           vars_kept N Wv entry t)
Proof
  rpt strip_tac >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _`
    (mp_tac o SIMP_RULE (srw_ss()) [frag_fuel_def]) >>
  disch_then (qspecl_then [`G`, `st.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> simp[vars_kept_def] >>
  rpt strip_tac >>
  `var_below st.cs_next_var x` by
    (gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[vars_kept_def]
QED

(* Runtime interface for the condition block.  The two result variables
   may contain stale values on reentry; each is overwritten before use. *)
Theorem dynarray_condition_outcome[local]:
  !G ctx fn s bb ctr len lt done v n id1 id2 id3 body_lbl exit P.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id1 LT [Var ctr; Var len] [lt];
       mk_inst id2 ISZERO [Var lt] [done];
       mk_inst id3 JNZ [Var done; Label exit; Label body_lbl] []] /\
    s.vs_inst_idx = 0 /\
    lookup_var ctr s = SOME v /\ lookup_var len s = SOME n /\
    (!t. t = jump_to (if w2n v < w2n n then body_lbl else exit)
                ((update_var done (bool_to_word (~(w2n v < w2n n)))
                   (update_var lt (bool_to_word (w2n v < w2n n)) s))
                 with vs_inst_idx := 2) ==> P t) ==>
    fuel_outcome G ctx fn s 1 P
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = (update_var lt (bool_to_word (w2n v < w2n n)) s)
                       with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var done (bool_to_word (~(w2n v < w2n n))) s1)
                       with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> qunabbrev_tac `s1` >> irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst id1 LT [Var ctr; Var len] [lt]`] >>
     simp[get_instruction_def, mk_inst_def, is_terminator_def] >>
     simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
          eval_operand_def]) >>
  `!f. run_from f ctx fn s1 = run_from f ctx fn s2` by
    (gen_tac >> qunabbrev_tac `s2` >> irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst id2 ISZERO [Var lt] [done]`] >>
     simp[get_instruction_def, mk_inst_def, is_terminator_def,
          Abbr `s1`, update_var_def] >>
     simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_pure1_def,
          eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          bool_to_word_def] >> Cases_on `w2n v < w2n n` >>
     simp[bool_to_word_def, update_var_def]) >>
  `fuel_outcome G ctx fn s2 1 P` suffices_by
    simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`,
    `mk_inst id3 JNZ [Var done; Label exit; Label body_lbl] []`,
    `if w2n v < w2n n then body_lbl else exit`] >>
  simp[get_instruction_def, mk_inst_def, is_terminator_def,
       Abbr `s2`, Abbr `s1`, update_var_def] >>
  simp[GSYM mk_inst_def, step_inst_base_opcode_eqs,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       bool_to_word_def] >>
  Cases_on `w2n v < w2n n` >> gvs[update_var_def, bool_to_word_def]
QED

(* The tail can lie after an arbitrary fragment, possibly in a different
   block from the body entry.  Its instruction index is therefore explicit. *)
Theorem dynarray_increment_outcome[local]:
  !G ctx fn s bb ctr tmp v id1 id2 id3 cond P.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 ADD [Var ctr; Lit 1w] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) =
      SOME (mk_inst id3 JMP [Label cond] []) /\
    lookup_var ctr s = SOME v /\
    (!t. t = jump_to cond
           ((update_var ctr (v + 1w) (update_var tmp (v + 1w) s))
            with vs_inst_idx := SUC (SUC s.vs_inst_idx)) ==> P t) ==>
    fuel_outcome G ctx fn s 1 P
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = (update_var tmp (v + 1w) s)
                       with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var ctr (v + 1w) s1)
                       with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> qunabbrev_tac `s1` >> irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst id1 ADD [Var ctr; Lit 1w] [tmp]`] >>
     simp[mk_inst_def, is_terminator_def] >>
     simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
          eval_operand_def]) >>
  `!f. run_from f ctx fn s1 = run_from f ctx fn s2` by
    (gen_tac >> qunabbrev_tac `s2` >> irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst id2 ASSIGN [Var tmp] [ctr]`] >>
     simp[mk_inst_def, is_terminator_def, Abbr `s1`, update_var_def] >>
     simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, update_var_def]) >>
  `fuel_outcome G ctx fn s2 1 P` suffices_by simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `mk_inst id3 JMP [Label cond] []`, `cond`] >>
  simp[mk_inst_def, is_terminator_def, Abbr `s2`, Abbr `s1`, update_var_def] >>
  simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, update_var_def]
QED

(* A complete round.  H is indexed by the natural counter, so the consumer
   can choose its measure without exposing execution details again. *)
Theorem dynarray_round_outcome[local]:
  !G ctx fn N Wv entry ctr len lt done tmp n cond body_lbl exit
   id1 id2 id3 id4 id5 id6 cb st st' Kbody H Q.
    H = (\i s. s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
                lookup_var ctr s = SOME (n2w i) /\
                lookup_var len s = SOME (n2w n) /\ vars_kept N Wv entry s) /\
    Q = (\s. s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\
              vars_kept N Wv entry s) /\
    no_phi_fn fn /\ callees_stable G ctx fn /\ n < dimword(:256) /\
    lookup_block cond fn.fn_blocks = SOME cb /\
    cb.bb_instructions =
      [mk_inst id1 LT [Var ctr; Var len] [lt];
       mk_inst id2 ISZERO [Var lt] [done];
       mk_inst id3 JNZ [Var done; Label exit; Label body_lbl] []] /\
    st.cs_current_bb = body_lbl /\ st.cs_current_insts = [] /\
    frag_fuel {} {} {} st st' Kbody /\ fn_has_code st st' fn /\
    N <= st.cs_next_var /\
    var_below st.cs_next_var ctr /\ var_below st.cs_next_var len /\
    (!s. at_point st' s ==>
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx =
          SOME (mk_inst id4 ADD [Var ctr; Lit 1w] [tmp]) /\
        get_instruction bb (SUC s.vs_inst_idx) =
          SOME (mk_inst id5 ASSIGN [Var tmp] [ctr]) /\
        get_instruction bb (SUC (SUC s.vs_inst_idx)) =
          SOME (mk_inst id6 JMP [Label cond] [])) /\
    ctr <> lt /\ ctr <> done /\ len <> lt /\ len <> done /\
    len <> ctr /\ len <> tmp /\
    ~var_below N lt /\ ~var_below N done /\
    ~var_below N ctr /\ ~var_below N tmp ==>
    !i s. i <= n /\ H i s ==>
      ?j. j <= Kbody + 2 /\
        fuel_outcome G ctx fn s j (\t. Q t \/ (i < n /\ H (i + 1) t))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `i < dimword(:256)` by decide_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME cb /\ s.vs_inst_idx = 0 /\
   lookup_var ctr s = SOME (n2w i) /\ lookup_var len s = SOME (n2w n)` by
    gvs[] >>
  qabbrev_tac `B = \t. t.vs_current_bb = body_lbl /\ t.vs_inst_idx = 0 /\
     lookup_var ctr t = SOME (n2w i) /\ lookup_var len t = SOME (n2w n) /\
     vars_kept N Wv entry t` >>
  `fuel_outcome G ctx fn s 1 (\t. Q t \/ (i < n /\ B t))` by
    (drule_at (Pos (el 3)) dynarray_condition_outcome >>
     disch_then irule >> simp[] >>
     rpt strip_tac >> gvs[Abbr `B`, jump_to_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE, w2n_n2w, LESS_MOD] >>
     Cases_on `i < n` >> gvs[vars_kept_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`\t. Q t \/ (i < n /\ H (i + 1) t)`, `Kbody + 1`] mp_tac) >>
  impl_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac
      >- (qexists_tac `0` >> simp[fuel_outcome_refl]) >>
      `at_point st t /\ lookup_var ctr t = SOME (n2w i) /\
       lookup_var len t = SOME (n2w n) /\ vars_kept N Wv entry t` by
        gvs[Abbr `B`, at_point_def] >>
      drule_all dynarray_body_outcome >> strip_tac >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then [`\u. Q u \/ (i < n /\ H (i + 1) u)`, `1`] mp_tac) >>
      impl_tac
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          qpat_x_assum `!s. at_point st' s ==> _` drule >> strip_tac >>
          `lookup_var ctr t' = SOME (n2w i) /\
           lookup_var len t' = SOME (n2w n)` by gvs[vars_kept_def] >>
          qexists_tac `1` >> simp[] >>
          drule_at (Pos (el 3)) dynarray_increment_outcome >>
          disch_then irule >> simp[mk_inst_def] >>
          rpt strip_tac >>
          gvs[jump_to_def, lookup_var_def, update_var_def,
              finite_mapTheory.FLOOKUP_UPDATE, vars_kept_def] >>
          simp[GSYM word_add_n2w] >> metis_tac[]) >>
      disch_then (qx_choose_then `jtail` strip_assume_tac) >>
      qexists_tac `jtail` >> simp[] >> decide_tac) >>
  disch_then (qx_choose_then `jround` strip_assume_tac) >>
  qexists_tac `jround` >> simp[] >> decide_tac
QED

(* Convert the indexed round interface to the state measure expected by
   fuel_outcome_iterate.  Values never wrap: the next index is at most n. *)
Theorem dynarray_counted_iteration[local]:
  !G ctx fn ctr H Q n Kround.
    n < dimword(:256) /\
    (!i s. H i s ==> lookup_var ctr s = SOME (n2w i)) /\
    (!i s. i <= n /\ H i s ==>
      ?j. j <= Kround /\
        fuel_outcome G ctx fn s j (\t. Q t \/ (i < n /\ H (i + 1) t))) ==>
    !s. (?i. i <= n /\ H i s) ==>
      ?j. j <= dimword(:256) * Kround /\ fuel_outcome G ctx fn s j Q
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac fuel_outcome_iterate >>
  qexists_tac `\s. n - w2n (THE (lookup_var ctr s))` >>
  conj_tac
  >- (rpt strip_tac >> `i < dimword(:256)` by decide_tac >>
      `lookup_var ctr s = SOME (n2w i)` by metis_tac[] >>
      simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `?j. j <= Kround /\
    fuel_outcome G ctx fn s j (\t. Q t \/ (i < n /\ H (i + 1) t))` by
    metis_tac[] >>
  qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >- simp[] >>
  disj2_tac >> reverse conj_tac
  >- (`i < dimword(:256) /\ i + 1 < dimword(:256)` by decide_tac >>
      `lookup_var ctr s = SOME (n2w i) /\
       lookup_var ctr t = SOME (n2w (i + 1))` by metis_tac[] >>
      simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  qexists_tac `i + 1` >> simp[] >> decide_tac
QED

(* Given a bound for the element copy (the recursive call), the copy of a
   dynamic array is bounded.  The length is loaded into a fresh variable
   before the loop; the loop counts a fresh counter from 0 while it is
   below that length.  The body writes only the counter and variables it
   allocates itself, so the length stays fixed and the loop leaves within
   2 ** 256 rounds. *)
Theorem fuel_ok_compile_copy_dynarray_typed:
  !cenv dst dst_elem cap src src_elem.
    (!d s Wv E. fuel_ok Wv {} E
                  (compile_store_memory_typed cenv d dst_elem s src_elem)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)
Proof
  cheat
QED

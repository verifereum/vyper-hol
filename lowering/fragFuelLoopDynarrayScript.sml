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
   id1 id2 id3 id4 id5 id6 cb st st' Kbody.
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
    !i s. i <= n /\
      (s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
       lookup_var ctr s = SOME (n2w i) /\
       lookup_var len s = SOME (n2w n) /\ vars_kept N Wv entry s) ==>
      ?j. j <= Kbody + 2 /\
        fuel_outcome G ctx fn s j
          (\t. (t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ vars_kept N Wv entry t) \/
               (i < n /\ t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
                lookup_var ctr t = SOME (n2w (i + 1)) /\
                lookup_var len t = SOME (n2w n) /\ vars_kept N Wv entry t))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `H = \i s. s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
     lookup_var ctr s = SOME (n2w i) /\
     lookup_var len s = SOME (n2w n) /\ vars_kept N Wv entry s` >>
  qabbrev_tac `Q = \s. s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\
     vars_kept N Wv entry s` >>
  rpt gen_tac >> strip_tac >>
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
     rpt strip_tac >> gvs[Abbr `B`, Abbr `Q`, jump_to_def, lookup_var_def,
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
          gvs[Abbr `H`, jump_to_def, lookup_var_def, update_var_def,
              finite_mapTheory.FLOOKUP_UPDATE, vars_kept_def] >>
          simp[GSYM word_add_n2w] >> metis_tac[]) >>
      disch_then (qx_choose_then `jtail` strip_assume_tac) >>
      qexists_tac `jtail` >> simp[] >> decide_tac) >>
  disch_then (qx_choose_then `jround` strip_assume_tac) >>
  qexists_tac `jround` >> gvs[Abbr `Q`, Abbr `H`] >> decide_tac
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

(* Structural projection: admitting all jumps as exits bounds a single
   pass through the emitted code.  This is used only for compile-state
   properties, not as the fuel bound for the counted loop. *)
Theorem dynarray_compile_structure[local]:
  !cenv dst dst_elem cap src src_elem st x st'.
    (!d s Wv E. fuel_ok Wv {} E
       (compile_store_memory_typed cenv d dst_elem s src_elem)) /\
    compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem st = (x, st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    (cs_no_phi st ==> cs_no_phi st')
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} UNIV
     (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)`
    suffices_by metis_tac[fuel_ok_def] >>
  simp[Once (cj 6 compile_store_memory_typed_def), compile_copy_memory_dynamic_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
             fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst] >>
  simp[is_terminator_def]
QED

(* Keep each monadic cut as a run equation.  In particular, no unfolding
   of the recursive element copy is needed to recover the loop layout. *)
Theorem dynarray_counted_run[local]:
  !ce dst dt cap src styp sa result sz.
    ~(type_memory_bytes ce dt = type_memory_bytes ce styp /\ dt = styp) /\
    compile_copy_dynarray_typed ce dst dt cap src styp sa = (result,sz) ==>
    ?len long ok sd dd hdr body exit ctr lt done so doff sp dp next
     a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
     a17 a18 a19 a20 a21 a22 a23 a24 a25 a26.
      emit_op MLOAD [src] sa = (len,a1) /\
      emit_op GT [len; Lit (n2w cap)] a1 = (long,a2) /\
      emit_op ISZERO [long] a2 = (ok,a3) /\
      emit_void ASSERT [ok] a3 = ((),a4) /\
      emit_void MSTORE [dst;len] a4 = ((),a5) /\
      emit_op ADD [src;Lit 32w] a5 = (sd,a6) /\
      emit_op ADD [dst;Lit 32w] a6 = (dd,a7) /\
      fresh_label "typed_dyn_cond" a7 = (hdr,a8) /\
      fresh_label "typed_dyn_body" a8 = (body,a9) /\
      fresh_label "typed_dyn_exit" a9 = (exit,a10) /\
      fresh_var a10 = (ctr,a11) /\
      emit_inst ASSIGN [Lit 0w] [ctr] a11 = ((),a12) /\
      emit_inst JMP [Label hdr] [] a12 = ((),a13) /\
      new_block hdr a13 = (a13.cs_current_bb,a14) /\
      emit_op LT [Var ctr;len] a14 = (lt,a15) /\
      emit_op ISZERO [lt] a15 = (done,a16) /\
      emit_inst JNZ [done;Label exit;Label body] [] a16 = ((),a17) /\
      new_block body a17 = (a17.cs_current_bb,a18) /\
      emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce styp))] a18 = (so,a19) /\
      emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dt))] a19 = (doff,a20) /\
      emit_op ADD [sd;so] a20 = (sp,a21) /\
      emit_op ADD [dd;doff] a21 = (dp,a22) /\
      compile_store_memory_typed ce dp dt sp styp a22 = ((),a23) /\
      emit_op ADD [Var ctr;Lit 1w] a23 = (next,a24) /\
      emit_inst ASSIGN [next] [ctr] a24 = ((),a25) /\
      emit_inst JMP [Label hdr] [] a25 = ((),a26) /\
      new_block exit a26 = (a26.cs_current_bb,sz) /\ result = () /\
      len = Var (STRING #"%" (toString sa.cs_next_var)) /\
      ctr = STRING #"%" (toString (sa.cs_next_var + 5)) /\
      a22.cs_next_var = sa.cs_next_var + 12 /\
      var_below a22.cs_next_var (STRING #"%" (toString sa.cs_next_var)) /\
      var_below a22.cs_next_var ctr /\
      ctr <> STRING #"%" (toString sa.cs_next_var) /\
      (!N. N <= sa.cs_next_var ==>
        ~var_below N (STRING #"%" (toString sa.cs_next_var)) /\
        ~var_below N ctr)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once (cj 6 compile_store_memory_typed_def), comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[new_block_def, emit_op_def, emit_inst_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, fresh_label_def, emit_def,
      var_below_def, ASCIInumbersTheory.toString_inj]
QED

(* The straight-line body cut ends just before its back jump.  Its
   temporary registers are fresh; only the loop counter may be overwritten. *)
Theorem dynarray_body_fuel[local]:
  !ce dt styp ctr sd dd Wv E.
    (!d s Wv E. fuel_ok Wv {} E
       (compile_store_memory_typed ce d dt s styp)) ==>
    fuel_ok (ctr INSERT Wv) {} E
      (do so <- emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce styp))];
          doff <- emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dt))];
          sp <- emit_op ADD [sd;so];
          dp <- emit_op ADD [dd;doff];
          compile_store_memory_typed ce dp dt sp styp;
          next <- emit_op ADD [Var ctr;Lit 1w];
          emit_inst ASSIGN [next] [ctr]
       od)
Proof
  rpt strip_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst] >>
  simp[is_terminator_def]
QED

(* The iteration interface cuts before the increment, preserving ctr. *)
Theorem dynarray_body_cut_bound[local]:
  !ce dt styp ctr sd dd so doff sp dp a18 a19 a20 a21 a22 a23.
    (!d s Wv E. fuel_ok Wv {} E
       (compile_store_memory_typed ce d dt s styp)) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce styp))] a18 = (so,a19) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dt))] a19 = (doff,a20) /\
    emit_op ADD [sd;so] a20 = (sp,a21) /\
    emit_op ADD [dd;doff] a21 = (dp,a22) /\
    compile_store_memory_typed ce dp dt sp styp a22 = ((),a23) ==>
    cs_extends a18 a23 /\ a18.cs_next_var <= a23.cs_next_var /\
    ?Kbody. frag_fuel {} {} {} a18 a23 Kbody
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} {}
    (do so <- emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce styp))];
        doff <- emit_op MUL [Var ctr;Lit (n2w (type_memory_bytes ce dt))];
        sp <- emit_op ADD [sd;so];
        dp <- emit_op ADD [dd;doff];
        compile_store_memory_typed ce dp dt sp styp
     od)` by
    (fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  pop_assum mp_tac >>
  rewrite_tac[fuel_ok_def] >>
  disch_then (qspec_then `a18` mp_tac) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* Exact condition block, including its terminator. *)
Theorem dynarray_condition_code[local]:
  !a13 a14 a15 a16 a17 a18 hdr body exit ctr len lt done fn.
    new_block hdr a13 = (a13.cs_current_bb,a14) /\
    emit_op LT [Var ctr;len] a14 = (lt,a15) /\
    emit_op ISZERO [lt] a15 = (done,a16) /\
    emit_inst JNZ [done;Label exit;Label body] [] a16 = ((),a17) /\
    new_block body a17 = (a17.cs_current_bb,a18) /\
    fn_has_code a17 a18 fn ==>
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions :=
        [mk_inst a14.cs_next_id LT [Var ctr;len]
           [STRING #"%" (toString a14.cs_next_var)];
         mk_inst a15.cs_next_id ISZERO [lt]
           [STRING #"%" (toString a15.cs_next_var)];
         mk_inst a16.cs_next_id JNZ [done;Label exit;Label body] []]|>
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fn_has_code_new_block >>
  gvs[new_block_def, emit_op_def, emit_inst_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def]
QED

(* Exact increment cut: the recursive body may have emitted many blocks. *)
Theorem dynarray_increment_code[local]:
  !a23 a24 a25 a26 ctr next hdr fn.
    emit_op ADD [Var ctr;Lit 1w] a23 = (next,a24) /\
    emit_inst ASSIGN [next] [ctr] a24 = ((),a25) /\
    emit_inst JMP [Label hdr] [] a25 = ((),a26) /\
    fn_has_code a23 a26 fn ==>
    !s. at_point a23 s ==>
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME
          (mk_inst a23.cs_next_id ADD [Var ctr;Lit 1w]
            [STRING #"%" (toString a23.cs_next_var)]) /\
        get_instruction bb (SUC s.vs_inst_idx) = SOME
          (mk_inst a24.cs_next_id ASSIGN [next] [ctr]) /\
        get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME
          (mk_inst a25.cs_next_id JMP [Label hdr] [])
Proof
  rpt gen_tac >> strip_tac >>
  drule fn_has_code_same_block >>
  disch_then (qspec_then
    `[mk_inst a23.cs_next_id ADD [Var ctr;Lit 1w]
       [STRING #"%" (toString a23.cs_next_var)];
      mk_inst a24.cs_next_id ASSIGN [next] [ctr];
      mk_inst a25.cs_next_id JMP [Label hdr] []]` mp_tac) >>
  impl_tac
  >- gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> rpt strip_tac >> gvs[at_point_def] >>
  qpat_x_assum `!i. i < 3 ==> _`
    (fn th => map_every (fn i => mp_tac (Q.SPEC i th)) [`0`,`1`,`2`]) >>
  simp[ADD1]
QED

(* Embed the three runtime cuts in any function containing the loop. *)
Theorem dynarray_loop_intervals[local]:
  !sa a12 a13 a14 a15 a16 a17 a18 a23 a24 a25 a26 sz
   hdr body exit ctr len lt done next fn.
    cs_extends sa a12 /\ cs_extends a18 a23 /\
    emit_inst JMP [Label hdr] [] a12 = ((),a13) /\
    new_block hdr a13 = (a13.cs_current_bb,a14) /\
    emit_op LT [Var ctr;len] a14 = (lt,a15) /\
    emit_op ISZERO [lt] a15 = (done,a16) /\
    emit_inst JNZ [done;Label exit;Label body] [] a16 = ((),a17) /\
    new_block body a17 = (a17.cs_current_bb,a18) /\
    emit_op ADD [Var ctr;Lit 1w] a23 = (next,a24) /\
    emit_inst ASSIGN [next] [ctr] a24 = ((),a25) /\
    emit_inst JMP [Label hdr] [] a25 = ((),a26) /\
    new_block exit a26 = (a26.cs_current_bb,sz) /\
    fn_has_code sa sz fn ==>
    fn_has_code sa a12 fn /\ fn_has_code sa a13 fn /\ fn_has_code a17 a18 fn /\
    fn_has_code a18 a23 fn /\ fn_has_code a23 a26 fn /\
    a18.cs_current_bb = body /\ a18.cs_current_insts = [] /\
    (!t. at_point sz t <=> t.vs_current_bb = exit /\ t.vs_inst_idx = 0)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends a14 a15 /\ cs_extends a15 a16 /\ cs_extends a23 a24` by
    metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_extends a12 a13 /\ cs_extends a16 a17 /\
   cs_extends a24 a25 /\ cs_extends a25 a26` by
    metis_tac[cs_extends_emit_inst] >>
  `cs_extends a13 a14 /\ cs_extends a17 a18 /\ cs_extends a26 sz` by
    metis_tac[cs_extends_new_block] >>
  `cs_extends a14 a16 /\ cs_extends a23 a25` by
    metis_tac[cs_extends_trans] >>
  `cs_extends a18 a25 /\ cs_extends a25 sz` by
    metis_tac[cs_extends_trans] >>
  `cs_extends a18 sz /\ cs_extends a23 a26 /\ cs_extends a17 sz` by
    metis_tac[cs_extends_trans] >>
  `cs_extends a14 a17 /\ cs_extends a12 a14` by
    metis_tac[cs_extends_trans] >>
  `cs_extends a12 a17 /\ cs_extends sa a17 /\ cs_extends a12 sz` by
    metis_tac[cs_extends_trans] >>
  `cs_extends a13 a17` by metis_tac[cs_extends_trans] >>
  `cs_extends a13 sz /\ cs_extends sa a13` by metis_tac[cs_extends_trans] >>
  `cs_extends a12 a18` by metis_tac[cs_extends_trans] >>
  `cs_extends a12 a23` by metis_tac[cs_extends_trans] >>
  `fn_has_code a12 sz fn` by metis_tac[fn_has_code_split] >>
  drule_all frag_exec_loop_layout >> strip_tac >>
  rpt conj_tac
  >- metis_tac[fn_has_code_split]
  >- metis_tac[fn_has_code_split]
  >- metis_tac[fn_has_code_mid, cs_extends_refl]
  >- metis_tac[fn_has_code_split]
  >- metis_tac[fn_has_code_mid, cs_extends_refl]
  >- simp[]
  >- simp[] >>
  simp[at_point_def]
QED

(* All live loop registers are allocated in the prefix.  The increment's
   output is fresh even if the recursive body allocated further variables. *)
Theorem dynarray_register_layout[local]:
  !sa a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a23
   src dst cap len long ok sd dd hdr body exit ctr lt done.
    emit_op MLOAD [src] sa = (len,a1) /\
    emit_op GT [len; Lit (n2w cap)] a1 = (long,a2) /\
    emit_op ISZERO [long] a2 = (ok,a3) /\
    emit_void ASSERT [ok] a3 = ((),a4) /\
    emit_void MSTORE [dst;len] a4 = ((),a5) /\
    emit_op ADD [src;Lit 32w] a5 = (sd,a6) /\
    emit_op ADD [dst;Lit 32w] a6 = (dd,a7) /\
    fresh_label "typed_dyn_cond" a7 = (hdr,a8) /\
    fresh_label "typed_dyn_body" a8 = (body,a9) /\
    fresh_label "typed_dyn_exit" a9 = (exit,a10) /\
    fresh_var a10 = (ctr,a11) /\
    emit_inst ASSIGN [Lit 0w] [ctr] a11 = ((),a12) /\
    emit_inst JMP [Label hdr] [] a12 = ((),a13) /\
    new_block hdr a13 = (a13.cs_current_bb,a14) /\
    emit_op LT [Var ctr;len] a14 = (lt,a15) /\
    emit_op ISZERO [lt] a15 = (done,a16) /\
    emit_inst JNZ [done;Label exit;Label body] [] a16 = ((),a17) /\
    new_block body a17 = (a17.cs_current_bb,a18) /\
    a18.cs_next_var <= a23.cs_next_var ==>
    ?lv ltv donev tmp.
      len = Var lv /\ lt = Var ltv /\ done = Var donev /\
      lv = STRING #"%" (toString sa.cs_next_var) /\
      ltv = STRING #"%" (toString a14.cs_next_var) /\
      donev = STRING #"%" (toString a15.cs_next_var) /\
      tmp = STRING #"%" (toString a23.cs_next_var) /\
      sa.cs_next_var <= a18.cs_next_var /\
      var_below a18.cs_next_var ctr /\ var_below a18.cs_next_var lv /\
      ctr <> ltv /\ ctr <> donev /\ lv <> ltv /\ lv <> donev /\
      lv <> ctr /\ lv <> tmp /\
      ~var_below sa.cs_next_var ltv /\ ~var_below sa.cs_next_var donev /\
      ~var_below sa.cs_next_var ctr /\ ~var_below sa.cs_next_var tmp /\
      ~var_below sa.cs_next_var lv /\
      a1.cs_current_bb = sa.cs_current_bb /\
      LENGTH a1.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
      sa.cs_next_var <= a1.cs_next_var /\ var_below a1.cs_next_var lv
Proof
  rpt gen_tac >> strip_tac >>
  gvs[new_block_def, emit_op_def, emit_inst_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, fresh_label_def, emit_def] >>
  simp[var_below_def, ASCIInumbersTheory.toString_inj] >> decide_tac
QED

(* Successful loading defines the length; undefined addresses instead have
   a fixed result.  No validity premise about the source is needed. *)
Theorem dynarray_load_outcome[local]:
  !G ctx fn s bb id src len N Wv.
    callees_stable G ctx fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [src] [len]) /\
    ~var_below N len ==>
    fuel_outcome G ctx fn s 0
      (\t. (?n. n < dimword(:256) /\ lookup_var len t = SOME (n2w n)) /\
           t.vs_current_bb = s.vs_current_bb /\
           t.vs_inst_idx = SUC s.vs_inst_idx /\ vars_kept N Wv s t)
Proof
  rpt strip_tac >>
  drule_at (Pos (el 3)) run_from_nonterm_stable >>
  disch_then (qspecl_then [`G`, `ctx`, `fn`] mp_tac) >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac
  >- (gvs[GSYM mk_inst_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
      simp[fuel_outcome_def] >> disj1_tac >>
      qexists_tac `update_var len (mload (w2n addr) s) s with
                    vs_inst_idx := SUC s.vs_inst_idx` >>
      simp[update_var_def, lookup_var_def, vars_kept_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      conj_tac
      >- (qexists_tac `w2n (mload (w2n addr) s)` >> simp[w2n_lt]) >>
      metis_tac[]) >>
  simp[fuel_outcome_def]
QED

(* The prefix tail writes the fresh counter and enters the header. *)
Theorem dynarray_initialize_outcome[local]:
  !G ctx fn s bb ctr len n N Wv entry id1 id2 hdr.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 ASSIGN [Lit 0w] [ctr]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst id2 JMP [Label hdr] []) /\
    lookup_var len s = SOME (n2w n) /\ vars_kept N Wv entry s /\
    len <> ctr /\ ~var_below N ctr ==>
    fuel_outcome G ctx fn s 1
      (\t. t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
           lookup_var ctr t = SOME 0w /\
           lookup_var len t = SOME (n2w n) /\ vars_kept N Wv entry t)
Proof
  rpt strip_tac >>
  qabbrev_tac `s1 = update_var ctr 0w s with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn s1` by
    (gen_tac >> qunabbrev_tac `s1` >> irule run_from_step >>
     qexistsl_tac [`bb`, `mk_inst id1 ASSIGN [Lit 0w] [ctr]`] >>
     simp[mk_inst_def, is_terminator_def] >>
     simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
  `fuel_outcome G ctx fn s1 1
      (\t. t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
           lookup_var ctr t = SOME 0w /\
           lookup_var len t = SOME (n2w n) /\ vars_kept N Wv entry t)`
    suffices_by simp[fuel_outcome_def] >>
  irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `mk_inst id2 JMP [Label hdr] []`, `hdr`] >>
  simp[Abbr `s1`, update_var_def, mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, jump_to_def,
       vars_kept_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[vars_kept_def, lookup_var_def] >> metis_tac[]
QED

(* The intervening arithmetic, checks and stores preserve the loaded length:
   it was allocated before this action starts. *)
Theorem dynarray_prefix_middle_fuel[local]:
  !len cap dst src Wv E.
    fuel_ok Wv {} E
      (do long <- emit_op GT [len; Lit (n2w cap)];
          ok <- emit_op ISZERO [long];
          emit_void ASSERT [ok];
          emit_void MSTORE [dst;len];
          sd <- emit_op ADD [src;Lit 32w];
          dd <- emit_op ADD [dst;Lit 32w];
          hdr <- fresh_label "typed_dyn_cond";
          body <- fresh_label "typed_dyn_body";
          exit <- fresh_label "typed_dyn_exit";
          ctr <- fresh_var;
          return (sd,dd,hdr,body,exit,ctr)
       od)
Proof
  rpt gen_tac >> fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >>
  simp[is_terminator_def]
QED

Theorem dynarray_prefix_middle_bound[local]:
  !len cap dst src long ok sd dd hdr body exit ctr
   a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11.
    emit_op GT [len; Lit (n2w cap)] a1 = (long,a2) /\
    emit_op ISZERO [long] a2 = (ok,a3) /\
    emit_void ASSERT [ok] a3 = ((),a4) /\
    emit_void MSTORE [dst;len] a4 = ((),a5) /\
    emit_op ADD [src;Lit 32w] a5 = (sd,a6) /\
    emit_op ADD [dst;Lit 32w] a6 = (dd,a7) /\
    fresh_label "typed_dyn_cond" a7 = (hdr,a8) /\
    fresh_label "typed_dyn_body" a8 = (body,a9) /\
    fresh_label "typed_dyn_exit" a9 = (exit,a10) /\
    fresh_var a10 = (ctr,a11) ==>
    cs_extends a1 a11 /\ a1.cs_next_var <= a11.cs_next_var /\
    ?Kmid. frag_fuel {} {} {} a1 a11 Kmid
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`len`, `cap`, `dst`, `src`] mp_tac dynarray_prefix_middle_fuel >>
  disch_then (qspecl_then [`{}`, `{}`] mp_tac) >>
  rewrite_tac[fuel_ok_def] >>
  disch_then (qspec_then `a1` mp_tac) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* Prefix code cuts used by the value-establishing execution interface. *)
Theorem dynarray_prefix_code[local]:
  !sa a1 a11 a12 a13 src len ctr hdr fn.
    emit_op MLOAD [src] sa = (len,a1) /\
    cs_extends a1 a11 /\
    emit_inst ASSIGN [Lit 0w] [ctr] a11 = ((),a12) /\
    emit_inst JMP [Label hdr] [] a12 = ((),a13) /\
    fn_has_code sa a13 fn ==>
    fn_has_code a1 a11 fn /\
    (!s. at_point sa s ==>
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME
          (mk_inst sa.cs_next_id MLOAD [src]
             [STRING #"%" (toString sa.cs_next_var)])) /\
    (!s. at_point a11 s ==>
      ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME
          (mk_inst a11.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
        get_instruction bb (SUC s.vs_inst_idx) = SOME
          (mk_inst a12.cs_next_id JMP [Label hdr] []))
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa a1` by metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_extends a11 a12 /\ cs_extends a12 a13` by
    metis_tac[cs_extends_emit_inst] >>
  `cs_extends a11 a13 /\ cs_extends sa a11` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa a1 fn /\ fn_has_code a11 a13 fn` by
    metis_tac[fn_has_code_split] >>
  conj_tac >- metis_tac[fn_has_code_mid] >> conj_tac
  >- (qspecl_then [`sa`, `a1`, `fn`] mp_tac fn_has_code_same_block >>
      disch_then (qspec_then
        `[mk_inst sa.cs_next_id MLOAD [src]
          [STRING #"%" (toString sa.cs_next_var)]]` mp_tac) >>
      impl_tac
      >- gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
             comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
      strip_tac >> rpt strip_tac >> gvs[at_point_def] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qspecl_then [`a11`, `a13`, `fn`] mp_tac fn_has_code_same_block >>
  disch_then (qspec_then
    `[mk_inst a11.cs_next_id ASSIGN [Lit 0w] [ctr];
      mk_inst a12.cs_next_id JMP [Label hdr] []]` mp_tac) >>
  impl_tac
  >- gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> rpt strip_tac >> gvs[at_point_def] >>
  qpat_x_assum `!i. i < 2 ==> _`
    (fn th => map_every (fn i => mp_tac (Q.SPEC i th)) [`0`,`1`]) >>
  simp[ADD1]
QED

(* Compose the two value-establishing endpoints with the ordinary fragment
   bound of the middle.  The bound is chosen before any runtime values. *)
Theorem dynarray_prefix_outcome[local]:
  !G ctx fn sa mid tail Kmid len ctr src id0 id1 id2 hdr N Wv s.
    no_phi_fn fn /\ callees_stable G ctx fn /\
    mid.cs_current_bb = sa.cs_current_bb /\
    LENGTH mid.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    (!u. at_point sa u ==>
      ?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME (mk_inst id0 MLOAD [src] [len])) /\
    frag_fuel {} {} {} mid tail Kmid /\ fn_has_code mid tail fn /\
    N <= mid.cs_next_var /\ var_below mid.cs_next_var len /\
    ~var_below N len /\ ~var_below N ctr /\ len <> ctr /\
    (!u. at_point tail u ==>
      ?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME (mk_inst id1 ASSIGN [Lit 0w] [ctr]) /\
           get_instruction bb (SUC u.vs_inst_idx) = SOME (mk_inst id2 JMP [Label hdr] [])) /\
    at_point sa s ==>
    ?j. j <= Kmid + 1 /\ fuel_outcome G ctx fn s j
      (\t. ?n. n < dimword(:256) /\
           t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
           lookup_var ctr t = SOME 0w /\ lookup_var len t = SOME (n2w n) /\
           vars_kept N Wv s t)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!u. at_point sa u ==> _` drule >> strip_tac >>
  drule_at (Pos (el 3)) dynarray_load_outcome >>
  disch_then (qspecl_then [`G`, `ctx`, `fn`, `N`, `Wv`] mp_tac) >>
  simp[] >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. ?n. n < dimword(:256) /\ t.vs_current_bb = hdr /\
                t.vs_inst_idx = 0 /\ lookup_var ctr t = SOME 0w /\
                lookup_var len t = SOME (n2w n) /\ vars_kept N Wv s t`,
     `Kmid + 1`] mp_tac) >>
  impl_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      `at_point mid t` by gvs[at_point_def] >>
      drule_all dynarray_body_outcome >> strip_tac >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then
        [`\u. ?n. n < dimword(:256) /\ u.vs_current_bb = hdr /\
                    u.vs_inst_idx = 0 /\ lookup_var ctr u = SOME 0w /\
                    lookup_var len u = SOME (n2w n) /\ vars_kept N Wv s u`,
         `1`] mp_tac) >>
      impl_tac
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          qpat_x_assum `!u. at_point tail u ==> _` drule >> strip_tac >>
          `lookup_var len t' = SOME (n2w n)` by gvs[vars_kept_def] >>
          qexists_tac `1` >> simp[] >>
          irule fuel_outcome_weaken >>
          irule_at Any dynarray_initialize_outcome >>
          simp[] >> metis_tac[]) >>
      disch_then (qx_choose_then `jtail` strip_assume_tac) >>
      qexists_tac `jtail` >> simp[] >> decide_tac) >>
  simp[]
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
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `type_memory_bytes cenv dst_elem = type_memory_bytes cenv src_elem /\ dst_elem = src_elem`
  >- (simp[Once (cj 6 compile_store_memory_typed_def), compile_copy_memory_dynamic_def] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >>
      simp[is_terminator_def]) >>
  simp[fuel_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all dynarray_compile_structure >> strip_tac >> simp[] >>
  drule_all dynarray_counted_run >> strip_tac >>
  drule_all dynarray_body_cut_bound >> strip_tac >>
  drule_all dynarray_prefix_middle_bound >> strip_tac >>
  drule_all dynarray_register_layout >> strip_tac >>
  `cs_extends st a1` by
    metis_tac[cs_appends_def, cs_appends_emit_helpers] >>
  `cs_extends a11 a12` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends st a12` by metis_tac[cs_extends_trans] >>
  qexists_tac `Kmid + 1 + dimword(:256) * (Kbody + 2)` >>
  simp[frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  drule_all dynarray_loop_intervals >> strip_tac >>
  drule_all dynarray_prefix_code >> strip_tac >>
  drule_all dynarray_condition_code >> strip_tac >>
  qpat_assum `fn_has_code a23 a26 fn`
    (mp_then (Pos (el 4)) mp_tac dynarray_increment_code) >>
  disch_then (qspecl_then [`a24`, `a25`, `ctr`, `next`, `hdr`] mp_tac) >>
  simp[] >> disch_tac >>
  `?j. j <= Kmid + 1 /\ fuel_outcome G ctx fn s j
    (\t. ?n. n < dimword(:256) /\
         t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
         lookup_var ctr t = SOME 0w /\ lookup_var lv t = SOME (n2w n) /\
         vars_kept N Wv s t)` by
    (irule dynarray_prefix_outcome >>
     `~var_below N ctr /\ ~var_below N lv` by
       metis_tac[var_below_def, LESS_EQ_TRANS] >>
     simp[] >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. vars_kept N Wv s t /\
          (at_point st' t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx = 0))`,
     `dimword(:256) * (Kbody + 2)`] mp_tac) >>
  impl_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      qabbrev_tac `H = \i u. u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
        lookup_var ctr u = SOME (n2w i) /\
        lookup_var lv u = SOME (n2w n) /\ vars_kept N Wv s u` >>
      qabbrev_tac `Q = \u. u.vs_current_bb = exit /\ u.vs_inst_idx = 0 /\
        vars_kept N Wv s u` >>
      `!i u. i <= n /\ H i u ==>
        ?j. j <= Kbody + 2 /\ fuel_outcome G ctx fn u j
          (\v. Q v \/ (i < n /\ H (i + 1) v))` by
        (simp[Abbr `H`, Abbr `Q`] >>
         match_mp_tac dynarray_round_outcome >> simp[] >>
         qpat_assum `frag_fuel {} {} {} a18 a23 Kbody`
           (irule_at Any) >> simp[] >>
         simp[mk_inst_def] >>
         qexists_tac `tmp` >> simp[] >>
         `next = Var tmp` by
           (qpat_x_assum `emit_op ADD [Var ctr; Lit 1w] a23 = _` mp_tac >>
            simp[emit_op_def, comp_bind_def, comp_return_def, fresh_var_def,
                 fresh_id_def, emit_def, emit_inst_def, comp_ignore_bind_def]) >>
         `~var_below N ltv /\ ~var_below N donev /\
          ~var_below N ctr /\ ~var_below N tmp` by
           metis_tac[var_below_def, LESS_EQ_TRANS] >>
         gvs[mk_inst_def] >>
         metis_tac[]) >>
      `!i u. H i u ==> lookup_var ctr u = SOME (n2w i)` by
        simp[Abbr `H`] >>
      qpat_assum `!i u. i <= n /\ H i u ==> _`
        (mp_then (Pos (el 3)) mp_tac dynarray_counted_iteration) >>
      disch_then (qspec_then `ctr` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `t` mp_tac) >>
      impl_tac >- (qexists_tac `0` >> gvs[Abbr `H`]) >>
      disch_then (qx_choose_then `jloop` strip_assume_tac) >>
      qexists_tac `jloop` >> simp[] >>
      irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
      simp[Abbr `Q`]) >>
  disch_then (qx_choose_then `jall` strip_assume_tac) >>
  qexists_tac `jall` >> gvs[]
QED

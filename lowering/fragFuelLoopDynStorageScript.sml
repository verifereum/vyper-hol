(*
 * Fuel bound for the sparse storage store (compile_store_slots).
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_store_slots
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelLoopDynarray
  compileEnv emitHelper context venomInst fragExec venomExecSemantics
  venomState words arithmetic
Libs
  fragFuelLib

(* ===== The element loop ===== *)

(* Cutting every jump gives the compile-state projections without the
   loop's termination. *)
Theorem copy_elements_structure[local]:
  !cenv src slot elem cnt tr st x st'.
    (!s sl Wv E. fuel_ok Wv {} E (compile_store_slots cenv s sl elem tr)) /\
    compile_copy_elements_to_slots cenv src slot elem cnt tr st = (x, st') ==>
    cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    (cs_no_phi st ==> cs_no_phi st')
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} UNIV
     (compile_copy_elements_to_slots cenv src slot elem cnt tr)`
    suffices_by metis_tac[fuel_ok_def] >>
  simp_tac std_ss [Once compile_store_slots_def, LET_THM] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jmp, fuel_ok_emit_inst_jnz,
             fuel_ok_emit_inst] >>
  simp[is_terminator_def]
QED

(* Each monadic cut as a run equation; the element store stays opaque. *)
Theorem copy_elements_run[local]:
  !cenv src slot elem cnt tr s0 x sz.
    compile_copy_elements_to_slots cenv src slot elem cnt tr s0 = (x, sz) ==>
    ?hdr body exit ctr ltv donev tmp so se lo le
     a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19.
      fresh_label "dyn_cond" s0 = (hdr,a1) /\
      fresh_label "dyn_body" a1 = (body,a2) /\
      fresh_label "dyn_exit" a2 = (exit,a3) /\
      fresh_var a3 = (ctr,a4) /\
      emit_inst ASSIGN [Lit 0w] [ctr] a4 = ((),a5) /\
      emit_inst JMP [Label hdr] [] a5 = ((),a6) /\
      new_block hdr a6 = (a6.cs_current_bb,a7) /\
      emit_op LT [Var ctr; cnt] a7 = (Var ltv,a8) /\
      emit_op ISZERO [Var ltv] a8 = (Var donev,a9) /\
      emit_inst JNZ [Var donev; Label exit; Label body] [] a9 = ((),a10) /\
      new_block body a10 = (a10.cs_current_bb,a11) /\
      emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem))] a11 =
        (so,a12) /\
      emit_op ADD [src; so] a12 = (se,a13) /\
      emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem DIV 32))]
        a13 = (lo,a14) /\
      emit_op ADD [slot; lo] a14 = (le,a15) /\
      compile_store_slots cenv se le elem tr a15 = ((),a16) /\
      emit_op ADD [Var ctr; Lit 1w] a16 = (Var tmp,a17) /\
      emit_inst ASSIGN [Var tmp] [ctr] a17 = ((),a18) /\
      emit_inst JMP [Label hdr] [] a18 = ((),a19) /\
      new_block exit a19 = (a19.cs_current_bb,sz) /\ x = () /\
      a4.cs_blocks = s0.cs_blocks /\ a4.cs_current_bb = s0.cs_current_bb /\
      a4.cs_current_insts = s0.cs_current_insts /\
      ctr = STRING #"%" (toString s0.cs_next_var) /\
      ltv = STRING #"%" (toString a7.cs_next_var) /\
      donev = STRING #"%" (toString a8.cs_next_var) /\
      tmp = STRING #"%" (toString a16.cs_next_var) /\
      a7.cs_next_var = s0.cs_next_var + 1 /\
      a8.cs_next_var = s0.cs_next_var + 2 /\
      a11.cs_next_var = s0.cs_next_var + 3
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_elements_to_slots _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[new_block_def, emit_op_def, emit_inst_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      fresh_label_def, emit_def]
QED

(* The body cut ends before the increment, so the counter is kept. *)
Theorem copy_elements_body_cut[local]:
  !cenv elem tr ctr src slot so se lo le a11 a12 a13 a14 a15 a16.
    (!s sl Wv E. fuel_ok Wv {} E (compile_store_slots cenv s sl elem tr)) /\
    emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem))] a11 =
      (so,a12) /\
    emit_op ADD [src; so] a12 = (se,a13) /\
    emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem DIV 32))]
      a13 = (lo,a14) /\
    emit_op ADD [slot; lo] a14 = (le,a15) /\
    compile_store_slots cenv se le elem tr a15 = ((),a16) ==>
    cs_extends a11 a16 /\ a11.cs_next_var <= a16.cs_next_var /\
    ?Kbody. frag_fuel {} {} {} a11 a16 Kbody
Proof
  rpt gen_tac >> strip_tac >>
  `fuel_ok {} {} {}
    (do so <- emit_op MUL [Var ctr; Lit (n2w (type_memory_bytes cenv elem))];
        se <- emit_op ADD [src; so];
        lo <- emit_op MUL
                [Var ctr; Lit (n2w (type_memory_bytes cenv elem DIV 32))];
        le <- emit_op ADD [slot; lo];
        compile_store_slots cenv se le elem tr
     od)` by
    (fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  pop_assum mp_tac >> rewrite_tac[fuel_ok_def] >>
  disch_then (qspec_then `a11` mp_tac) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* With no value, the count stops the run at the header's comparison. *)
Theorem copy_elements_undefined_count[local]:
  !G ctx fn s bb ctr cnt lt id1 P.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id1 LT [Var ctr; cnt] [lt]) /\
    eval_operand cnt s = NONE ==>
    fuel_outcome G ctx fn s 0 P
Proof
  rpt strip_tac >> simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
  `!g. run_from g ctx fn s = run_from 0 ctx fn s` suffices_by simp[] >>
  gen_tac >>
  qspecl_then [`g`, `ctx`, `fn`, `s`, `bb`,
    `mk_inst id1 LT [Var ctr; cnt] [lt]`] mp_tac run_from_nonterm >>
  qspecl_then [`0`, `ctx`, `fn`, `s`, `bb`,
    `mk_inst id1 LT [Var ctr; cnt] [lt]`] mp_tac run_from_nonterm >>
  simp[mk_inst_def, is_terminator_def, step_inst_non_invoke] >>
  simp[GSYM mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def]
QED

(* The element loop runs at most 2 ** 256 rounds: the counter counts up
   from 0 while below the count, which is a literal or a variable
   allocated before the loop, so the body keeps it. *)
Theorem copy_elements_fuel[local]:
  !cenv src slot elem cnt tr.
    (!s sl Wv E. fuel_ok Wv {} E (compile_store_slots cenv s sl elem tr)) ==>
    !Wv E.
      fuel_okS (\st. (!x. cnt = Var x ==> var_below st.cs_next_var x) /\
                     !l. cnt <> Label l) Wv {} E
        (compile_copy_elements_to_slots cenv src slot elem cnt tr)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  pure_rewrite_tac[fuel_okS_def] >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `!x n. cnt = Var x /\ st.cs_next_var <= n ==>
         x <> STRING #"%" (toString n)` by
    (rpt strip_tac >> qpat_x_assum `!x. cnt = Var x ==> _` drule >>
     simp[var_below_def] >> metis_tac[]) >>
  drule_all copy_elements_structure >> strip_tac >> simp[] >>
  drule copy_elements_run >> strip_tac >>
  drule_all copy_elements_body_cut >> strip_tac >>
  `cs_extends st a4` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends a4 a5 /\ cs_extends a5 a6` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends st a5 /\ cs_extends a4 a6` by metis_tac[cs_extends_trans] >>
  `st.cs_next_var <= a11.cs_next_var /\ a11.cs_next_var <= a16.cs_next_var`
    by simp[] >>
  (* The loop registers, as fresh names; their spelling is dropped below. *)
  `ctr <> ltv /\ ctr <> donev /\ var_below a11.cs_next_var ctr /\
   !M. M <= st.cs_next_var ==>
       ~var_below M ltv /\ ~var_below M donev /\ ~var_below M ctr /\
       ~var_below M tmp` by
    (simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac
     >- decide_tac >>
     metis_tac[LESS_EQ_TRANS, DECIDE ``!a:num. a <= a + 1 /\ a <= a + 2``]) >>
  `!x. cnt = Var x ==>
       var_below a11.cs_next_var x /\ x <> ltv /\ x <> donev /\ x <> ctr /\
       x <> tmp` by
    (gen_tac >> strip_tac >> simp[var_below_def] >> rpt strip_tac >>
     gvs[] >> metis_tac[LESS_EQ_TRANS, DECIDE ``!a:num. a <= a + 1 /\ a <= a + 2``]) >>
  qexists_tac `1 + dimword(:256) * (Kbody + 2)` >>
  simp[frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  qspecl_then [`st`, `a5`, `a6`, `a7`, `a8`, `a9`, `a10`, `a11`, `a16`, `a17`,
    `a18`, `a19`, `st'`, `hdr`, `body`, `exit`, `ctr`, `cnt`, `Var ltv`,
    `Var donev`, `Var tmp`, `fn`] mp_tac dynarray_loop_intervals >>
  impl_tac >- simp[] >> strip_tac >>
  `?cb. lookup_block hdr fn.fn_blocks = SOME cb /\
        cb.bb_instructions =
          [mk_inst a7.cs_next_id LT [Var ctr; cnt] [ltv];
           mk_inst a8.cs_next_id ISZERO [Var ltv] [donev];
           mk_inst a9.cs_next_id JNZ [Var donev; Label exit; Label body] []]`
    by (qspecl_then [`a6`, `a7`, `a8`, `a9`, `a10`, `a11`, `hdr`, `body`,
          `exit`, `ctr`, `cnt`, `Var ltv`, `Var donev`, `fn`] mp_tac
          dynarray_condition_code >> simp[]) >>
  `!u. at_point a16 u ==>
     ?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb u.vs_inst_idx =
         SOME (mk_inst a16.cs_next_id ADD [Var ctr; Lit 1w] [tmp]) /\
       get_instruction bb (SUC u.vs_inst_idx) =
         SOME (mk_inst a17.cs_next_id ASSIGN [Var tmp] [ctr]) /\
       get_instruction bb (SUC (SUC u.vs_inst_idx)) =
         SOME (mk_inst a18.cs_next_id JMP [Label hdr] [])` by
    (qspecl_then [`a16`, `a17`, `a18`, `a19`, `ctr`, `Var tmp`, `hdr`, `fn`]
       mp_tac dynarray_increment_code >> simp[]) >>
  `fn_has_code a4 a6 fn` by metis_tac[fn_has_code_split] >>
  `at_point a4 s` by fs[at_point_def] >>
  drule_all dynarray_init_code >> strip_tac >>
  qpat_x_assum `!s. at_point a4 s ==> _` drule >> strip_tac >>
  `~var_below N ltv /\ ~var_below N donev /\ ~var_below N ctr /\
   ~var_below N tmp` by metis_tac[] >>
  qpat_x_assum `ctr = _` kall_tac >> qpat_x_assum `ltv = _` kall_tac >>
  qpat_x_assum `donev = _` kall_tac >> qpat_x_assum `tmp = _` kall_tac >>
  qabbrev_tac `Out = \t. vars_kept N Wv s t /\
    (at_point st' t \/ t.vs_current_bb IN E /\ t.vs_inst_idx = 0)` >>
  `fuel_outcome G ctx fn s 1
     (\t. t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
          lookup_var ctr t = SOME 0w /\
          eval_operand cnt t = eval_operand cnt s /\ vars_kept N Wv s t)` by
    (irule dynarray_initialize_outcome >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Out`, `dimword(:256) * (Kbody + 2)`] mp_tac) >>
  reverse impl_tac
  >- (strip_tac >> qexists_tac `j` >> simp[] >> fs[Abbr `Out`]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  Cases_on `eval_operand cnt s`
  >- (qexists_tac `0` >> simp[] >>
      irule copy_elements_undefined_count >>
      qexistsl_tac [`cb`, `ctr`, `cnt`, `a7.cs_next_id`, `ltv`] >>
      gvs[get_instruction_def]) >>
  rename1 `eval_operand cnt s = SOME w` >>
  `?n. n < dimword(:256) /\ w = n2w n` by
    (qexists_tac `w2n w` >> simp[w2n_lt]) >>
  qpat_x_assum `w = _` SUBST_ALL_TAC >>
  qspecl_then [`G`, `ctx`, `fn`, `N`, `Wv`, `s`, `ctr`, `cnt`, `ltv`, `donev`,
    `tmp`, `n`, `hdr`, `body`, `exit`, `a7.cs_next_id`, `a8.cs_next_id`,
    `a9.cs_next_id`, `a16.cs_next_id`, `a17.cs_next_id`, `a18.cs_next_id`,
    `cb`, `a11`, `a16`, `Kbody`] mp_tac dynarray_round_outcome >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`G`, `ctx`, `fn`, `ctr`,
    `\i u. u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
           lookup_var ctr u = SOME (n2w i) /\
           eval_operand cnt u = SOME (n2w n) /\ vars_kept N Wv s u`,
    `\u. u.vs_current_bb = exit /\ u.vs_inst_idx = 0 /\ vars_kept N Wv s u`,
    `n`, `Kbody + 2`] mp_tac dynarray_counted_iteration >>
  impl_tac >- (BETA_TAC >> simp[] >> metis_tac[]) >>
  disch_then (qspec_then `t` mp_tac) >>
  impl_tac >- (qexists_tac `0` >> gvs[]) >>
  strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[Abbr `Out`]
QED

(* ===== The store, by its mutual recursion ===== *)

Theorem store_slots_fuel[local]:
  (!cenv src slot ty tr.
     !Wv E. fuel_ok Wv {} E (compile_store_slots cenv src slot ty tr)) /\
  (!cenv src slot members mo so tr.
     !Wv E. fuel_ok Wv {} E
       (compile_store_slots_members cenv src slot members mo so tr)) /\
  (!cenv src slot elem cnt tr.
     !Wv E. fuel_okS (\st. (!x. cnt = Var x ==> var_below st.cs_next_var x) /\
                           !l. cnt <> Label l) Wv {} E
       (compile_copy_elements_to_slots cenv src slot elem cnt tr))
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac >>
  goalStack.print_tac "PROBE" >> cheat
QED

Theorem fuel_ok_compile_store_slots:
  !cenv src slot ty tr Wv E.
    fuel_ok Wv {} E (compile_store_slots cenv src slot ty tr)
Proof
  metis_tac[store_slots_fuel]
QED

(*
 * Fuel bound for the static-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_sarray_typed
 *)

Theory fragFuelLoopSarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  venomExecSemantics venomExecProps venomExecProofs venomInstProps
  venomState words finite_map arithmetic
  typedCopyLoopLayoutPtr
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

(* Initialization and the counter back edge. *)
Theorem sa_initialize[local]:
  no_phi_fn fn /\ ~var_below N c /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ai /\
  ai.inst_opcode = ASSIGN /\ ai.inst_operands = [Lit 0w] /\
  ai.inst_outputs = [c] /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME ji /\
  ji.inst_opcode = JMP /\ ji.inst_operands = [Label lc] ==>
  fuel_outcome G ctx fn s 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME 0w)
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (update_var c 0w s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn u` by
    (gen_tac >> `~is_terminator ai.inst_opcode` by simp[is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[is_terminator_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, eval_operand_def, Abbr `u`]) >>
  `fuel_outcome G ctx fn u 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME 0w)` by
    (irule fuel_outcome_jump >>
     conj_tac >- simp[] >> qexistsl_tac [`bb`, `ji`, `lc`] >>
     simp[Abbr `u`, update_var_def, is_terminator_def,
          step_inst_base_opcode_eqs, jump_to_def, vars_kept_def,
          lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `x = c` >> gvs[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

Theorem sa_increment[local]:
  no_phi_fn fn /\ ~var_below N c /\ ~var_below N vnext /\ c <> vnext /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ai /\
  ai.inst_opcode = ADD /\ ai.inst_operands = [Var c; Lit 1w] /\
  ai.inst_outputs = [vnext] /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME ci /\
  ci.inst_opcode = ASSIGN /\ ci.inst_operands = [Var vnext] /\
  ci.inst_outputs = [c] /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME ji /\
  ji.inst_opcode = JMP /\ ji.inst_operands = [Label lc] /\
  lookup_var c s = SOME (n2w k) ==>
  fuel_outcome G ctx fn s 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME (n2w (k+1)))
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (update_var vnext (n2w (k+1)) s)
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = (update_var c (n2w (k+1)) u)
                    with vs_inst_idx := SUC u.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn u` by
    (gen_tac >> `~is_terminator ai.inst_opcode` by simp[is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[is_terminator_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
          GSYM word_add_n2w, Abbr `u`]) >>
  `!f. run_from f ctx fn u = run_from f ctx fn v` by
    (gen_tac >>
     `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME ci /\
      ~is_terminator ci.inst_opcode` by
       simp[Abbr `u`, update_var_def, is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
          eval_operand_def, Abbr `v`, Abbr `u`, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `fuel_outcome G ctx fn v 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME (n2w (k+1)))` by
    (irule fuel_outcome_jump >> conj_tac >- simp[] >>
     qexistsl_tac [`bb`, `ji`, `lc`] >>
     simp[Abbr `v`, Abbr `u`, update_var_def, is_terminator_def,
          step_inst_base_opcode_eqs, jump_to_def, vars_kept_def,
          lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `x = c` >> Cases_on `x = vnext` >> gvs[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

Theorem sa_increment_bound[local]:
  k < w2n (n2w n : 256 word) ==>
  k+1 <= w2n (n2w n : 256 word) /\
  w2n (n2w (k+1) : 256 word) = k+1 /\
  w2n (n2w n : 256 word) - (k+1) < w2n (n2w n : 256 word) - k
Proof
  strip_tac >>
  `w2n (n2w n : 256 word) < dimword (:256)` by simp[w2n_lt] >>
  `k+1 < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w, LESS_MOD]
QED

(* The layout theorem is purely symbolic: its only non-definitional premise
   is the slow-branch guard.  It uses compile_copy_sarray_typed_slow, whose
   proof is one unfolding of compile_store_memory_typed_def. *)
Theorem sarray_slow_structure[local]:
  (!d s Wv E. fuel_ok Wv {} E
      (compile_store_memory_typed ce d dt s st)) /\
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sz) ==>
  cs_extends sa sz /\ sa.cs_next_var <= sz.cs_next_var /\
  (cs_no_phi sa ==> cs_no_phi sz)
Proof
  strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `cs_extends si se /\ si.cs_next_var <= se.cs_next_var /\
   (cs_no_phi si ==> cs_no_phi se)` by
    (qpat_x_assum `!d s Wv E. _` (qspecl_then [`Var dp`, `Var sp`, `{}`, `{}`] mp_tac) >>
     pure_rewrite_tac[fuel_ok_def] >> disch_then drule >> metis_tac[]) >>
  (* These frontier facts also apply to the witnesses reused by the runtime
     proof: the counter is below both ends of the recursive child. *)
  `si.cs_next_var = sa.cs_next_var + 7 /\
   sa.cs_next_var < si.cs_next_var /\ sa.cs_next_var < se.cs_next_var` by
    (gvs[] >> decide_tac) >>
  `cs_extends sa si` by
    (simp[cs_extends_def] >>
     qexists_tac `TAKE 2 si.cs_blocks` >> simp[]) >>
  `cs_extends se sz` by
    (simp[cs_extends_def] >> qexists_tac `[HD sz.cs_blocks]` >> simp[]) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- gvs[] >>
  strip_tac >>
  `cs_no_phi si` by
    (simp[cs_no_phi_def, venomInstTheory.mk_inst_def] >>
     gvs[cs_no_phi_def]) >>
  `cs_no_phi se` by metis_tac[] >>
  simp[cs_no_phi_def, venomInstTheory.mk_inst_def] >>
  gvs[cs_no_phi_def]
QED

(* Body pointer prefix: its values may fail to evaluate, but no instruction
   writes the loop counter or a variable from before the loop. *)
Theorem sa_body_prefix[local]:
  !G ctx fn N c lb vs vd ps pd ss ds src dst bb m0 m1 a0 a1 s.
    callees_stable G ctx fn /\
    lookup_block lb fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME m0 /\
    get_instruction bb 1 = SOME m1 /\
    get_instruction bb 2 = SOME a0 /\
    get_instruction bb 3 = SOME a1 /\
    m0.inst_opcode = MUL /\ m0.inst_operands = [Var c; Lit ss] /\
    m0.inst_outputs = [vs] /\
    m1.inst_opcode = MUL /\ m1.inst_operands = [Var c; Lit ds] /\
    m1.inst_outputs = [vd] /\
    a0.inst_opcode = ADD /\ a0.inst_operands = [src; Var vs] /\
    a0.inst_outputs = [ps] /\
    a1.inst_opcode = ADD /\ a1.inst_operands = [dst; Var vd] /\
    a1.inst_outputs = [pd] /\
    ~MEM c [vs;vd;ps;pd] /\
    EVERY (\x. ~var_below N x) [vs;vd;ps;pd] /\
    s.vs_current_bb = lb /\ s.vs_inst_idx = 0 ==>
    fuel_outcome G ctx fn s 0
      (\t. t.vs_current_bb = lb /\ t.vs_inst_idx = 4 /\
           vars_kept N {} s t /\ lookup_var c t = lookup_var c s)
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`s`, `bb`, `m0`] mp_tac)
    run_from_nonterm_stable >> simp[is_terminator_def] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `t1` strip_assume_tac) assume_tac)
  >- (drule_then (qspecl_then [`t1 with vs_inst_idx := 1`, `bb`, `m1`] mp_tac)
        run_from_nonterm_stable >> simp[is_terminator_def] >>
      disch_then (DISJ_CASES_THEN2
        (qx_choose_then `t2` strip_assume_tac) assume_tac)
      >- (drule_then (qspecl_then [`t2 with vs_inst_idx := 2`, `bb`, `a0`] mp_tac)
            run_from_nonterm_stable >> simp[is_terminator_def] >>
          disch_then (DISJ_CASES_THEN2
            (qx_choose_then `t3` strip_assume_tac) assume_tac)
          >- (drule_then (qspecl_then [`t3 with vs_inst_idx := 3`, `bb`, `a1`] mp_tac)
                run_from_nonterm_stable >> simp[is_terminator_def] >>
              disch_then (DISJ_CASES_THEN2
                (qx_choose_then `t4` strip_assume_tac) assume_tac)
              >- (simp[fuel_outcome_def] >> disj1_tac >>
                  qexists_tac `t4 with vs_inst_idx := 4` >>
                  gvs[vars_kept_def, venomStateTheory.lookup_var_def] >>
                  metis_tac[]) >>
              simp[fuel_outcome_def]) >>
          simp[fuel_outcome_def]) >>
      simp[fuel_outcome_def]) >>
  simp[fuel_outcome_def]
QED

(* Adapt the recursive copy's empty-write fragment to the loop invariant. *)
Theorem sa_recursive_boundary[local]:
  frag_fuel {} {} {} a z Kb /\ fn_has_code a z fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  N <= a.cs_next_var /\ var_below a.cs_next_var c /\ at_point a s ==>
  ?j. j <= Kb /\ fuel_outcome G ctx fn s j
    (\t. at_point z t /\ vars_kept N {} s t /\
         lookup_var c t = lookup_var c s)
Proof
  strip_tac >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  simp[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `a.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[vars_kept_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  gvs[var_below_def] >> metis_tac[LESS_EQ_TRANS]
QED

(* A complete round.  Code hypotheses are lookups, so later code may follow
   the opened exit and the recursive fragment may contain arbitrary blocks. *)
Theorem sa_round[local]:
  no_phi_fn fn /\ callees_stable G ctx fn /\
  lookup_block lc fn.fn_blocks = SOME bc /\
  get_instruction bc 0 = SOME (mk_inst i0 LT [Var c; Lit (n2w n)] [vlt]) /\
  get_instruction bc 1 = SOME (mk_inst i1 ISZERO [Var vlt] [vdone]) /\
  get_instruction bc 2 = SOME (mk_inst i2 JNZ [Var vdone; Label le; Label lb] []) /\
  vlt <> c /\ vdone <> c /\ vlt <> vdone /\
  ~var_below N vlt /\ ~var_below N vdone /\
  lookup_block lb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME (mk_inst i3 MUL [Var c; Lit ss] [vs]) /\
  get_instruction bb 1 = SOME (mk_inst i4 MUL [Var c; Lit ds] [vd]) /\
  get_instruction bb 2 = SOME (mk_inst i5 ADD [src; Var vs] [ps]) /\
  get_instruction bb 3 = SOME (mk_inst i6 ADD [dst; Var vd] [pd]) /\
  ~MEM c [vs;vd;ps;pd] /\
  EVERY (\x. ~var_below N x) [vs;vd;ps;pd] /\
  a.cs_current_bb = lb /\ LENGTH a.cs_current_insts = 4 /\
  frag_fuel {} {} {} a z Kb /\ fn_has_code a z fn /\
  N <= a.cs_next_var /\ var_below a.cs_next_var c /\
  ~var_below N c /\ ~var_below N vnext /\ c <> vnext /\
  lookup_block z.cs_current_bb fn.fn_blocks = SOME bz /\
  get_instruction bz (LENGTH z.cs_current_insts) =
    SOME (mk_inst i7 ADD [Var c; Lit 1w] [vnext]) /\
  get_instruction bz (SUC (LENGTH z.cs_current_insts)) =
    SOME (mk_inst i8 ASSIGN [Var vnext] [c]) /\
  get_instruction bz (SUC (SUC (LENGTH z.cs_current_insts))) =
    SOME (mk_inst i9 JMP [Label lc] []) /\
  s.vs_current_bb = lc /\ s.vs_inst_idx = 0 /\
  vars_kept N {} r s /\ lookup_var c s = SOME (n2w k) /\
  k <= w2n (n2w n : 256 word) ==>
  ?j. j <= Kb+2 /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {} r t /\
      ((t.vs_current_bb = le /\ t.vs_inst_idx = 0) \/
       (t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
        ?k'. k' <= w2n (n2w n : 256 word) /\
          lookup_var c t = SOME (n2w k') /\
          w2n (n2w n : 256 word) - w2n (THE (lookup_var c t)) <
          w2n (n2w n : 256 word) - w2n (THE (lookup_var c s)))))
Proof
  strip_tac >>
  `fuel_outcome G ctx fn s 1
    (\t. vars_kept N {} s t /\ lookup_var c t = SOME (n2w k) /\
      ((k = w2n (n2w n : 256 word) /\
        t.vs_current_bb = le /\ t.vs_inst_idx = 0) \/
       (k < w2n (n2w n : 256 word) /\
        t.vs_current_bb = lb /\ t.vs_inst_idx = 0)))` by
    (irule sa_condition >> simp[] >>
     qexistsl_tac [`bc`, `mk_inst i0 LT [Var c; Lit (n2w n)] [vlt]`,
       `mk_inst i1 ISZERO [Var vlt] [vdone]`,
       `mk_inst i2 JNZ [Var vdone; Label le; Label lb] []`] >>
     simp[mk_inst_def]) >>
  qmatch_abbrev_tac `?j. j <= Kb+2 /\ fuel_outcome G ctx fn s j Post` >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Post`, `Kb+1`] mp_tac) >>
  impl_tac
  >- (simp[] >> qx_gen_tac `t` >> strip_tac
      >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
          simp[Abbr `Post`] >> metis_tac[vars_kept_trans]) >>
      `fuel_outcome G ctx fn t 0
        (\u. u.vs_current_bb = lb /\ u.vs_inst_idx = 4 /\
             vars_kept N {} t u /\ lookup_var c u = lookup_var c t)` by
        (irule sa_body_prefix >> simp[mk_inst_def] >> gvs[]) >>
      drule fuel_outcome_compose >>
      disch_then (qspecl_then [`Post`, `Kb+1`] mp_tac) >>
      impl_tac
      >- (simp[] >> qx_gen_tac `u` >> strip_tac >>
          `at_point a u` by simp[at_point_def] >>
          drule_all sa_recursive_boundary >> strip_tac >>
          drule fuel_outcome_compose >>
          disch_then (qspecl_then [`Post`, `1`] mp_tac) >>
          impl_tac
          >- (simp[] >> qx_gen_tac `v` >> strip_tac >>
              `fuel_outcome G ctx fn v 1
                (\w. w.vs_current_bb = lc /\ w.vs_inst_idx = 0 /\
                  vars_kept N {} v w /\ lookup_var c w = SOME (n2w (k+1)))` by
                (irule sa_increment >> gvs[at_point_def, mk_inst_def]) >>
              qexists_tac `1` >> simp[] >>
              irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
              simp[Abbr `Post`] >> qx_gen_tac `w` >> strip_tac >>
              conj_tac >- metis_tac[vars_kept_trans] >>
              `k+1 < dimword (:256)` by
                (mp_tac (Q.ISPEC `n2w n : 256 word` w2n_lt) >>
                 rewrite_tac[w2n_n2w] >>
                 CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
              `k < dimword (:256)` by decide_tac >>
              disj2_tac >> simp[] >> qexists_tac `k+1` >>
              gvs[LESS_MOD]) >>
          strip_tac >> qexists_tac `j'` >> simp[] >> decide_tac) >>
      simp[]) >>
  simp[]
QED

(* The round measure is uniformly bounded even outside the invariant. *)
Theorem sa_measure_bound[local]:
  !n c s. w2n (n2w n : 256 word) - w2n (THE (lookup_var c s)) < 2 ** 256
Proof
  rpt gen_tac >>
  `dimword (:256) = 2 ** 256` by simp[dimword_def] >>
  mp_tac (Q.ISPEC `n2w n : 256 word` w2n_lt) >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem sa_slow_semantics[local]:
  (!d s Wv E. fuel_ok Wv {} E
    (compile_store_memory_typed ce d dt s st)) /\
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sz) ==>
  ?lc c Kb. !G ctx fn N r.
    fn_has_code sa sz fn /\ no_phi_fn fn /\ callees_stable G ctx fn /\
    N <= sa.cs_next_var /\ at_point sa r ==>
    fuel_outcome G ctx fn r 1
      (\s. s.vs_current_bb = lc /\ s.vs_inst_idx = 0 /\
        vars_kept N {} r s /\ lookup_var c s = SOME 0w) /\
    (!s k. s.vs_current_bb = lc /\ s.vs_inst_idx = 0 /\
      vars_kept N {} r s /\ lookup_var c s = SOME (n2w k) /\
      k <= w2n (n2w n : 256 word) ==>
      ?j. j <= Kb+2 /\ fuel_outcome G ctx fn s j
        (\t. vars_kept N {} r t /\
          (at_point sz t \/
           (t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
            ?k'. k' <= w2n (n2w n : 256 word) /\
              lookup_var c t = SOME (n2w k') /\
              w2n (n2w n : 256 word) - w2n (THE (lookup_var c t)) <
              w2n (n2w n : 256 word) - w2n (THE (lookup_var c s))))))
Proof
  strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `cs_extends si se /\ si.cs_next_var <= se.cs_next_var /\
   ?Kb. frag_fuel {} {} {} si se Kb` by
    (qpat_x_assum `!d s Wv E. _`
       (qspecl_then [`Var dp`, `Var sp`, `{}`, `{}`] mp_tac) >>
     gvs[fuel_ok_def]) >>
  qpat_x_assum `!d s Wv E. _` kall_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` kall_tac >>
  qexistsl_tac [`cond`, `ctr`, `Kb`] >> rpt gen_tac >> strip_tac >>
  `?entry test back.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME entry /\
    entry.bb_instructions = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
       mk_inst (sa.cs_next_id+1) JMP [Label cond] []] /\
    lookup_block cond fn.fn_blocks = SOME test /\
    test = HD si.cs_blocks /\
    lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = tail.cs_current_insts /\
    fn_has_code si se fn /\
    (?bb. lookup_block body' fn.fn_blocks = SOME bb /\
          isPREFIX si.cs_current_insts bb.bb_instructions)` by
    (mp_tac typed_copy_loop_slice_locations >>
     disch_then (qspecl_then [`ce`, `Var dp`, `dt`, `Var sp`, `st`,
       `sa`, `si`, `se`, `sz`, `HD (TL si.cs_blocks)`,
       `HD si.cs_blocks`, `HD sz.cs_blocks`, `fn`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> asm_rewrite_tac[] >>
         qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
         qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th]) >>
         qpat_assum `sc = _` (fn th => simp_tac (srw_ss()) [th]) >>
         qpat_assum `sz = _` (fn th => simp_tac (srw_ss()) [th]) >>
         qpat_assum `tail = _` (fn th => simp_tac (srw_ss()) [th]) >>
         simp[]) >> strip_tac >>
     qexistsl_tac [`HD (TL si.cs_blocks)`, `HD si.cs_blocks`, `HD sz.cs_blocks`] >>
     `(HD (TL si.cs_blocks)).bb_label = sa.cs_current_bb /\
      (HD si.cs_blocks).bb_label = cond /\
      (HD sz.cs_blocks).bb_label = se.cs_current_bb /\
      si.cs_current_bb = body'` by
       (rpt conj_tac >>
        qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
        qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th]) >>
        qpat_assum `sc = _` (fn th => simp_tac (srw_ss()) [th]) >>
        qpat_assum `sz = _` (fn th => simp_tac (srw_ss()) [th])) >>
     gvs[IgnAsm `sc = _`, IgnAsm `sb = _`, IgnAsm `si = _`,
         IgnAsm `sz = _`, IgnAsm `tail = _`] >>
     rpt conj_tac >>
     qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sc = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sz = _` (fn th => simp_tac (srw_ss()) [th])) >>
  `test.bb_instructions =
     [mk_inst sc.cs_next_id LT [Var ctr; Lit (n2w n)] [lt];
      mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
      mk_inst (sc.cs_next_id+2) JNZ [Var done; Label exit; Label body'] []] /\
   si.cs_current_bb = body' /\ si.cs_next_var = sa.cs_next_var+7 /\
   si.cs_current_insts =
     [mk_inst sb.cs_next_id MUL [Var ctr; Lit (n2w (type_memory_bytes ce st))] [so];
      mk_inst (sb.cs_next_id+1) MUL [Var ctr; Lit (n2w (type_memory_bytes ce dt))] [doff];
      mk_inst (sb.cs_next_id+2) ADD [src; Var so] [sp];
      mk_inst (sb.cs_next_id+3) ADD [dst; Var doff] [dp]] /\
   sz.cs_current_bb = exit /\ sz.cs_current_insts = [] /\
   back.bb_instructions = se.cs_current_insts ++
     [mk_inst se.cs_next_id ADD [Var ctr; Lit 1w] ["%" ++ toString se.cs_next_var];
      mk_inst (se.cs_next_id+1) ASSIGN [Var ("%" ++ toString se.cs_next_var)] [ctr];
      mk_inst (se.cs_next_id+2) JMP [Label cond] []]` by
    (rpt conj_tac >> asm_rewrite_tac[] >>
     qpat_assum `test = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `back.bb_instructions = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sz = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `tail = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th]) >>
     qpat_assum `sc = _` (fn th => simp_tac (srw_ss()) [th]) >> simp[]) >>
  map_every (fn p => qpat_x_assum p kall_tac)
    [`sc = _`, `sb = _`, `si = _`, `tail = _`, `sz = _`, `test = _`,
     `back.bb_instructions = tail.cs_current_insts`] >>
  conj_tac
  >- (irule sa_initialize >> simp[] >>
      conj_tac >- (irule var_below_fresh >> simp[]) >>
      qexistsl_tac [`mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]`, `entry`,
        `mk_inst (sa.cs_next_id+1) JMP [Label cond] []`] >>
      gvs[at_point_def, get_instruction_def, listTheory.EL_APPEND_EQN, mk_inst_def]) >>
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[at_point_def] >>
  qpat_assum `sz.cs_current_bb = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `sz.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[listTheory.LENGTH] >> irule sa_round >>
  `~var_below N ctr` by (simp[] >> irule var_below_fresh >> simp[]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexists_tac `k` >> asm_rewrite_tac[]) >>
  qpat_assum `frag_fuel _ _ _ si se Kb` (irule_at Any) >>
  qpat_assum `lookup_block se.cs_current_bb _ = _` (irule_at Any) >>
  qpat_assum `lookup_block body' _ = _` (irule_at Any) >>
  simp_tac pure_ss [optionTheory.SOME_11, boolTheory.UNWIND_THM2] >>
  qexistsl_tac [`so`, `"%" ++ toString se.cs_next_var`, `lt`, `done`, `doff`,
    `n2w (type_memory_bytes ce st)`, `src`, `sp`, `dp`,
    `se.cs_next_id+2`, `se.cs_next_id+1`, `se.cs_next_id`,
    `sb.cs_next_id+3`, `sb.cs_next_id+2`, `sb.cs_next_id+1`, `sb.cs_next_id`,
    `sc.cs_next_id+2`, `sc.cs_next_id+1`, `sc.cs_next_id`,
    `dst`, `n2w (type_memory_bytes ce dt)`] >>
  qexists_tac `test` >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  simp[get_instruction_def, listTheory.EL_APPEND_EQN,
       ASCIInumbersTheory.STRCAT_toString_inj] >>
  simp[arithmeticTheory.ADD_CLAUSES, var_below_def,
       ASCIInumbersTheory.toString_inj] >>
  `SUC (SUC (LENGTH se.cs_current_insts)) - LENGTH se.cs_current_insts = 2` by decide_tac >>
  asm_rewrite_tac[] >> simp[]
QED

(* Runtime-only assembly: the compiler boundary supplies these two phases. *)
Theorem sa_iterate_initialized[local]:
  fuel_outcome G ctx fn r 1
    (\s. s.vs_current_bb = lc /\ s.vs_inst_idx = 0 /\
         vars_kept N {} r s /\
         ?k. k <= w2n (n2w n : 256 word) /\
             lookup_var c s = SOME (n2w k)) /\
  (!s. s.vs_current_bb = lc /\ s.vs_inst_idx = 0 /\
       vars_kept N {} r s /\
       (?k. k <= w2n (n2w n : 256 word) /\
            lookup_var c s = SOME (n2w k)) ==>
    ?j. j <= Kr /\ fuel_outcome G ctx fn s j
      (\t. (at_point sz t /\ vars_kept N {} r t) \/
           ((t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
             vars_kept N {} r t /\
             ?k. k <= w2n (n2w n : 256 word) /\
                 lookup_var c t = SOME (n2w k)) /\
            w2n (n2w n : 256 word) - w2n (THE (lookup_var c t)) <
            w2n (n2w n : 256 word) - w2n (THE (lookup_var c s))))) ==>
  ?j. j <= 1 + (2 ** 256) * Kr /\
      fuel_outcome G ctx fn r j
        (\t. at_point sz t /\ vars_kept N {} r t)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `fuel_outcome G ctx fn r 1 H` >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn r _ Q` >>
  qabbrev_tac `mu = \s. w2n (n2w n : 256 word) -
                         w2n (THE (lookup_var c s))` >>
  irule fuel_outcome_compose >> qexists_tac `H` >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule fuel_outcome_iterate >> qexistsl_tac [`H`, `mu`] >>
  asm_simp_tac bool_ss [Abbr `mu`, sa_measure_bound, Abbr `H`, Abbr `Q`]
QED

(* The slow branch's frag_fuel: initialize, then at most 2 ** 256 rounds. *)
Theorem sa_slow_frag_fuel[local]:
  (!d s Wv E. fuel_ok Wv {} E
    (compile_store_memory_typed ce d dt s st)) /\
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sz) ==>
  ?Kc. frag_fuel {} {} {} sa sz Kc
Proof
  strip_tac >> drule_all sa_slow_semantics >> strip_tac >>
  qexists_tac `1 + 2 ** 256 * (Kb + 2)` >>
  rewrite_tac[frag_fuel_def, pred_setTheory.NOT_IN_EMPTY] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`G`, `ctx`, `fn`, `N`, `s`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  mp_tac (INST [``r:venom_state`` |-> ``s:venom_state``,
                ``Kr:num`` |-> ``Kb + 2``] sa_iterate_initialized) >>
  impl_tac
  >- (conj_tac
      >- (irule fuel_outcome_weaken >>
          qpat_x_assum `fuel_outcome _ _ _ _ 1 _` (irule_at Any) >>
          BETA_TAC >> rpt strip_tac >> asm_rewrite_tac[] >>
          qexists_tac `0` >> simp[]) >>
      qx_gen_tac `u` >> strip_tac >>
      qpat_x_assum `!s k. _` (qspecl_then [`u`, `k`] mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >> strip_tac >>
      qexists_tac `j` >> asm_rewrite_tac[] >>
      irule fuel_outcome_weaken >>
      qpat_x_assum `fuel_outcome _ _ _ u j _` (irule_at Any) >>
      BETA_TAC >> rpt strip_tac >> metis_tac[]) >>
  strip_tac >> qexists_tac `j` >> asm_rewrite_tac[] >>
  irule fuel_outcome_weaken >>
  qpat_x_assum `fuel_outcome _ _ _ s j _` (irule_at Any) >>
  BETA_TAC >> rpt strip_tac >> asm_rewrite_tac[]
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
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `type_memory_bytes cenv dst_elem = type_memory_bytes cenv src_elem /\
            ~is_abi_dynamic cenv.ce_struct_fields dst_elem`
  >- (simp_tac std_ss [Once compile_store_memory_typed_def, LET_THM] >>
      asm_rewrite_tac[] >> simp[fuel_ok_compile_copy_memory]) >>
  simp_tac std_ss [fuel_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `x` >>
  drule_all sarray_slow_structure >> drule_all sa_slow_frag_fuel >>
  rpt strip_tac >> asm_simp_tac std_ss [] >>
  qexists_tac `Kc` >> irule frag_fuel_mono >>
  qpat_x_assum `frag_fuel _ _ _ _ _ Kc` (irule_at Any) >>
  simp[]
QED

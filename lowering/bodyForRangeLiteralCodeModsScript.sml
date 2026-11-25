(* Compiler intervals for a literal-ended range. The target prefix uses the
   two immediate words, then enters the same declared interval in both runs. *)
Theory bodyForRangeLiteralCodeMods
Ancestors
  bodyFullForRange stmtLoweringMono stmtSimForParts stmtSimForLoop stmtSimFor
  stmtSimProps stmtFragPtr bodyExprPreFacts fragExec localPtrsProps loweringStateRelDefs
  exprLoweringProps
  gasShadow gasShadowCompileBase gasShadowCompileStmtBase gasShadowState
  emitHelper compileEnv stmtLowering venomInst venomInstProps
  finite_map list ASCIInumbers integer_word

val _ = Parse.hide "body";

(* Keep the entire body entry state, not just its current block: the
   prefix is the part we must relate to the shadow compiler's state. *)
Theorem range_lit_split[local]:
  compile_stmt cenv lctx ty
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) sa =
    ((),sb) /\ cenv.ce_alloca_locals ==>
  ?bc sb0 sb1 sj.
    let p = STRING #"%" (toString sa.cs_next_var);
        cv = STRING #"%" (toString (sa.cs_next_var + 1));
        ev = STRING #"%" (toString (sa.cs_next_var + 2));
        dv = STRING #"%" (toString (sa.cs_next_var + 3));
        en = fresh_label_output "for_entry" sa.cs_next_label;
        cn = fresh_label_output "for_cond" (sa.cs_next_label + 1);
        bl = fresh_label_output "for_body" (sa.cs_next_label + 2);
        inc = fresh_label_output "for_incr" (sa.cs_next_label + 3);
        ex = fresh_label_output "for_exit" (sa.cs_next_label + 4)
    in
    declare_local cenv id typ sa = (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
    sb0 = sa with <|
      cs_next_var := sa.cs_next_var + 4; cs_next_label := sa.cs_next_label + 5;
      cs_next_id := sa.cs_next_id + 8; cs_current_bb := bl;
      cs_current_insts := [mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] []];
      cs_blocks :=
        <|bb_label := cn; bb_instructions :=
          [mk_inst (sa.cs_next_id + 5) EQ [Var cv; Var ev] [dv];
           mk_inst (sa.cs_next_id + 6) JNZ [Var dv; Label ex; Label bl] []]|> ::
        <|bb_label := en; bb_instructions :=
          [mk_inst (sa.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
           mk_inst (sa.cs_next_id + 3) ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
           mk_inst (sa.cs_next_id + 4) JMP [Label cn] []]|> ::
        <|bb_label := sa.cs_current_bb; bb_instructions :=
          sa.cs_current_insts ++
          [mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p];
           mk_inst (sa.cs_next_id + 1) JMP [Label en] []]|> :: sa.cs_blocks|> /\
    compile_stmts bc (InLoop ex inc) ty body sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated inc sb1 = ((),sj) /\
    sb = sj with <|
      cs_next_var := sj.cs_next_var + 1; cs_next_id := sj.cs_next_id + 3;
      cs_current_bb := ex; cs_current_insts := [];
      cs_blocks :=
        <|bb_label := inc; bb_instructions :=
          [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w]
             [STRING #"%" (toString sj.cs_next_var)];
           mk_inst (sj.cs_next_id + 1) ASSIGN
             [Var (STRING #"%" (toString sj.cs_next_var))] [cv];
           mk_inst (sj.cs_next_id + 2) JMP [Label cn] []]|> ::
        <|bb_label := sj.cs_current_bb; bb_instructions := sj.cs_current_insts|> ::
        sj.cs_blocks|>
Proof
  strip_tac >>
  namedCases_on `declare_local cenv id typ sa` ["bc st1"] >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, lower_value_int_lit, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM, emit_local_alloca_def, fresh_label_def,
       emit_inst_def, emit_op_def, emit_void_def, fresh_id_def, emit_def,
       new_block_def, fresh_var_def, GSYM arithmeticTheory.ADD_ASSOC] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_stmts bc _ ty body sb0` >>
  rename1 `compile_stmts bc _ ty body sb0 = ((),sb1)` >>
  rename1 `emit_jmp_if_not_terminated _ sb1 = ((),sj)` >>
  qexistsl_tac [`sb1`,`sj`] >>
  unabbrev_all_tac >>
  `!xs (x:instruction) y. (xs ++ [x]) ++ [y] = xs ++ [x;y]` by
    (Induct >> simp[]) >>
  qpat_x_assum `!xs x y. _` (fn app =>
    qpat_x_assum `compile_stmts _ _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [app])) >>
  simp[EQ_SYM_EQ]
QED

Theorem range_lit_jump[local]:
  emit_jmp_if_not_terminated inc a = ((),b) ==>
  cs_extends a b /\ b.cs_next_var = a.cs_next_var /\
  (~block_is_terminated a ==>
    b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
    b.cs_current_insts = a.cs_current_insts ++ [mk_inst a.cs_next_id JMP [Label inc] []])
Proof
  Cases_on `block_is_terminated a` >>
  simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def,
       emit_inst_def, comp_ignore_bind_def, comp_return_def, LET_THM,
       fresh_id_def, emit_def] >>
  strip_tac >> gvs[cs_extends_refl] >> irule cs_extends_same_block >> simp[]
QED

Theorem range_lit_body_start[local]:
  cs_extends a b /\ fn_has_code a b f /\ a.cs_current_insts = [i] ==>
  ?bb. lookup_block a.cs_current_bb f.fn_blocks = SOME bb /\ get_instruction bb 0 = SOME i
Proof
  strip_tac >> drule_all fn_has_code_start >> strip_tac >>
  qexists_tac `bb` >> simp[] >> Cases_on `bb.bb_instructions` >>
  gvs[get_instruction_def]
QED

Theorem range_lit_lookup[local]:
  fn_has_code a b f ==>
  !bb lbl. bb.bb_label = lbl /\ MEM bb (emitted_blocks a b) ==>
    lookup_block lbl f.fn_blocks = SOME bb
Proof
  simp[fn_has_code_def] >> rpt strip_tac >> gvs[]
QED

Theorem range_literal_code_mods:
  stmt_env cenv lctx ty
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) sa =
    (cenv,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty
    (gas_shadow_stmt
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body)) ssa =
    (gas_shadow_env T cenv,ssb) /\
  gas_shadow_state sa ssa /\ fn_has_code sa sb func /\ fn_has_code ssa ssb sfunc /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ cenv.ce_alloca_locals /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  32 <= type_memory_bytes cenv typ /\ type_memory_size tyv = 32 /\ word_memory_type tyv ==>
  ?p sz ainst cv ev dv nv en cn bl inc ex bc body_cenv sb0 sb1 sj ss0 ss1 bbb.
    p = STRING #"%" (toString sa.cs_next_var) /\ sz = type_memory_bytes cenv typ /\
    ainst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p] /\
    cv = STRING #"%" (toString (sa.cs_next_var + 1)) /\
    ev = STRING #"%" (toString (sa.cs_next_var + 2)) /\
    dv = STRING #"%" (toString (sa.cs_next_var + 3)) /\
    nv = STRING #"%" (toString sj.cs_next_var) /\
    en = fresh_label_output "for_entry" sa.cs_next_label /\
    cn = fresh_label_output "for_cond" (sa.cs_next_label + 1) /\
    bl = fresh_label_output "for_body" (sa.cs_next_label + 2) /\
    inc = fresh_label_output "for_incr" (sa.cs_next_label + 3) /\
    ex = fresh_label_output "for_exit" (sa.cs_next_label + 4) /\
    declare_local cenv id typ sa = (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
    lookup_block sa.cs_current_bb func.fn_blocks =
      SOME <|bb_label := sa.cs_current_bb; bb_instructions :=
        sa.cs_current_insts ++ [ainst; mk_inst (sa.cs_next_id + 1) JMP [Label en] []]|> /\
    lookup_block en func.fn_blocks =
      SOME <|bb_label := en; bb_instructions :=
        [mk_inst (sa.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
         mk_inst (sa.cs_next_id + 3) ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
         mk_inst (sa.cs_next_id + 4) JMP [Label cn] []]|> /\
    for_code func cenv bc ty body id tyv p sz ainst cv ev dv nv cn ex bl inc
      (sa.cs_next_id + 5) (sa.cs_next_id + 6) (sa.cs_next_id + 7)
      bbb sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sb0 sb1 sj /\
    sb0.cs_current_bb = bl /\
    sb0.cs_current_insts = [mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
    sb.cs_current_bb = ex /\ sb.cs_current_insts = [] /\
    sb0.cs_next_var = sa.cs_next_var + 4 /\ sb0.cs_next_var <= sb.cs_next_var /\
    sj.cs_next_var = sb1.cs_next_var /\
    sa.cs_next_id <= sb0.cs_next_id /\ cs_extends sa sb /\
    ~not_fresh_at sa p /\ ~not_fresh_at sa cv /\ ~not_fresh_at sa ev /\ ~not_fresh_at sa dv /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb0 x) /\
    cs_extends sa sb0 /\ cs_extends sb0 sb1 /\ cs_extends sb1 sb /\
    cs_extends ssa ss0 /\ cs_extends ss1 ssb /\
    stmts_env bc (InLoop ex inc) ty body sb0 = (body_cenv,sb1) /\
    stmts_env (gas_shadow_env T bc) (InLoop ex inc) ty (MAP gas_shadow_stmt body) ss0 =
      (gas_shadow_env T body_cenv,ss1) /\
    gas_shadow_state sb0 ss0 /\ gas_shadow_state sb1 ss1 /\
    fn_has_code sb0 sb1 func /\ fn_has_code ss0 ss1 sfunc
Proof
  simp[range_full_outer_env, gas_shadow_expr_def] >> strip_tac >>
  qpat_assum `compile_stmt cenv _ _ _ sa = _`
    (mp_then Any mp_tac range_lit_split) >> simp[LET_THM] >>
  disch_then (qx_choosel_then [`bc`,`sb1`,`sj`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `compile_stmts bc _ ty body sb0` >>
  qpat_assum `compile_stmt (gas_shadow_env T cenv) _ _ _ ssa = _`
    (mp_then Any mp_tac range_lit_split) >> simp[LET_THM] >>
  disch_then (qx_choosel_then [`sbc`,`ss1`,`ssj`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `compile_stmts sbc _ ty (MAP gas_shadow_stmt body) ss0` >>
  (`sbc = gas_shadow_env T bc` by
    (mp_tac (SRULE [gas_shadow_compiles_env_def]
       (Q.INST [`ty` |-> `typ`, `sd` |-> `T`] gas_shadow_compiles_env_declare_local)) >>
     disch_then (qspecl_then [`sa`,`ssa`] mp_tac) >> simp[])) >>
  qpat_x_assum `sbc = _` SUBST_ALL_TAC >>
  `gas_shadow_state sb0 ss0` by
    (qpat_assum `gas_shadow_state sa ssa`
       (strip_assume_tac o REWRITE_RULE [gas_shadow_state_def]) >>
     simp[Abbr `sb0`, Abbr `ss0`, gas_shadow_state_def, gas_shadow_block_def,
          gas_shadow_inst_def] >>
     irule LIST_REL_APPEND_suff >> simp[gas_shadow_inst_def]) >>
  `ssa.cs_next_label = sa.cs_next_label` by fs[gas_shadow_state_def] >>
  suspend "intervals"
QED

Resume range_literal_code_mods[intervals]:
  `cs_extends sa sb0` by
    (simp[Abbr `sb0`, cs_extends_def] >> qexists_tac `[_;_;_]` >> simp[]) >>
  `cs_extends ssa ss0` by
    (simp[Abbr `ss0`, cs_extends_def] >> qexists_tac `[_;_;_]` >> simp[]) >>
  qpat_assum `compile_stmts bc _ ty body sb0 = _`
    (mp_then Any strip_assume_tac (REWRITE_RULE [cs_mono_def] (cj 2 compile_stmt_cs_mono))) >>
  qpat_assum `emit_jmp_if_not_terminated _ sb1 = _`
    (mp_then Any strip_assume_tac range_lit_jump) >>
  qpat_assum `emit_jmp_if_not_terminated _ ss1 = _`
    (mp_then Any strip_assume_tac range_lit_jump) >>
  `cs_extends sj sb` by
    (qpat_assum `sb = _` SUBST1_TAC >> simp[cs_extends_def] >>
     qexists_tac `[_;_]` >> simp[]) >>
  `cs_extends ssj ssb` by
    (qpat_assum `ssb = _` SUBST1_TAC >> simp[cs_extends_def] >>
     qexists_tac `[_;_]` >> simp[]) >>
  `cs_extends sb1 sb` by (irule cs_extends_trans >> qexists_tac `sj` >> simp[]) >>
  `cs_extends ss1 ssb` by (irule cs_extends_trans >> qexists_tac `ssj` >> simp[]) >>
  `cs_extends sb0 sb` by (irule cs_extends_trans >> qexists_tac `sb1` >> simp[]) >>
  `cs_extends sa sb1` by (irule cs_extends_trans >> qexists_tac `sb0` >> simp[]) >>
  `fn_has_code sb0 sb1 func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sa`] >> simp[]) >>
  `fn_has_code sb1 sj func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sa`] >> simp[]) >>
  `fn_has_code sa sb0 func` by
    (irule (cj 1 fn_has_code_split) >> simp[] >> qexists_tac `sb` >> simp[]) >>
  `cs_extends sa sj` by (irule cs_extends_trans >> qexists_tac `sb1` >> simp[]) >>
  `fn_has_code sj sb func` by
    (irule (cj 2 fn_has_code_split) >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sa` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ssa.cs_next_label = _` (fn lbl =>
    qpat_x_assum `compile_stmts (gas_shadow_env T bc) _ _ _ ss0 = _`
      (assume_tac o PURE_REWRITE_RULE [lbl])) >>
  drule_all range_body_pair_containment >>
  disch_then (qx_choose_then `body_cenv` strip_assume_tac) >>
  suspend "layout"
QED

Resume range_literal_code_mods[layout]:
  `sb0.cs_current_bb = fresh_label_output "for_body" (sa.cs_next_label + 2) /\
   sb0.cs_current_insts = [mk_inst (sa.cs_next_id + 7) MSTORE
     [Var (STRING #"%" (toString sa.cs_next_var));
      Var (STRING #"%" (toString (sa.cs_next_var + 1)))] []] /\
   sb0.cs_next_var = sa.cs_next_var + 4 /\ sa.cs_next_id <= sb0.cs_next_id` by
    simp[Abbr `sb0`] >>
  qpat_assum `sb0.cs_current_insts = [_]`
    (mp_then Any mp_tac range_lit_body_start) >>
  disch_then (qspecl_then [`func`,`sb1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `bbb` strip_assume_tac) >>
  `emitted_blocks sa sb0 = [HD sb0.cs_blocks; HD (TL sb0.cs_blocks);
                            HD (TL (TL sb0.cs_blocks))]` by
    (irule emitted_blocks_append >> simp[Abbr `sb0`]) >>
  `emitted_blocks sj sb = [HD sb.cs_blocks; HD (TL sb.cs_blocks)]` by
    (irule emitted_blocks_append >> simp[]) >>
  `cs_extends sa sb` by (irule cs_extends_trans >> qexists_tac `sb0` >> simp[]) >>
  qpat_assum `fn_has_code sa sb0 func`
    (assume_tac o MATCH_MP range_lit_lookup) >>
  qpat_assum `fn_has_code sj sb func`
    (assume_tac o MATCH_MP range_lit_lookup) >>
  qexistsl_tac [`body_cenv`,`sb0`,`sb1`,`sj`,`ss0`,`ss1`,`bbb`] >>
  conj_asm1_tac
  >- (qpat_assum `!bb lbl. _ /\ MEM bb (emitted_blocks sa sb0) ==> _` irule >>
      conj_tac >- simp[NoAsms] >>
      qpat_assum `emitted_blocks sa sb0 = _` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[MEM] >> disj2_tac >> disj2_tac >> disj1_tac >>
      simp[NoAsms, Abbr `sb0`]) >>
  conj_tac
  >- (qpat_assum `!bb lbl. _ /\ MEM bb (emitted_blocks sa sb0) ==> _` irule >>
      conj_tac >- simp[NoAsms] >>
      qpat_assum `emitted_blocks sa sb0 = _` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[MEM] >> disj2_tac >> disj1_tac >>
      simp[NoAsms, Abbr `sb0`]) >>
  conj_tac >- suspend "for_code" >>
  qpat_assum `sb = _` (fn out =>
    qpat_assum `cs_extends sa sb` (assume_tac o PURE_REWRITE_RULE [out]) >>
    qpat_assum `cs_extends sb1 sb` (assume_tac o PURE_REWRITE_RULE [out])) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
  qexists_tac `sa` >> simp[]
QED

Resume range_literal_code_mods[for_code]:
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >>
     simp[] >> irule declare_local_reserved >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb func.fn_blocks = SOME _`
       (mp_then Any mp_tac lookup_block_fn_insts) >> simp[]) >>
  REWRITE_TAC [for_code_def] >>
  conj_tac
  >- (qpat_assum `!bb lbl. _ /\ MEM bb (emitted_blocks sa sb0) ==> _` irule >>
      conj_tac >- simp[NoAsms] >>
      qpat_assum `emitted_blocks sa sb0 = _` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[MEM] >> disj1_tac >> simp[NoAsms, Abbr `sb0`]) >>
  conj_tac
  >- (qpat_assum `sb0.cs_current_bb = _` (fn at =>
        qpat_assum `lookup_block sb0.cs_current_bb func.fn_blocks = SOME bbb`
          (ACCEPT_TAC o PURE_REWRITE_RULE [at]))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `!bb lbl. _ /\ MEM bb (emitted_blocks sj sb) ==> _` irule >>
      conj_tac >- simp[NoAsms] >>
      qpat_assum `emitted_blocks sj sb = _` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[MEM] >> disj1_tac >>
      qpat_assum `sb = _` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  `sa.cs_next_var + 4 <= sj.cs_next_var` by
    (qpat_assum `sb0.cs_next_var <= sb1.cs_next_var` mp_tac >> simp[]) >>
  `!scs. not_local_ptr cenv scs (STRING #"%" (toString (sa.cs_next_var + 1))) /\
         not_local_ptr cenv scs (STRING #"%" (toString (sa.cs_next_var + 3))) /\
         not_local_ptr cenv scs (STRING #"%" (toString sj.cs_next_var))` by
    (gen_tac >> rpt conj_tac >> irule reserved_fresh_not_local >>
     qexists_tac `sa` >> simp[] >> decide_tac) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    simp[block_is_terminated_def, mk_inst_def, is_terminator_def,
         not_fresh_at_def, ASCIInumbersTheory.toString_inj])
QED

Finalise range_literal_code_mods

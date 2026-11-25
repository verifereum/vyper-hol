(* Static compiler boundaries for fixed-Bytes bitwise and shift expressions. *)
Theory entryCreateBopBytesGeometry
Ancestors
  bodyFullBopWordLayout bodyPtrBopScalarDispatch bodyPtrBopScalarSeq
  createSizeOperandCode createSizeBuiltinBodyCode entryCreateIntervalLayout
  s1PrefixDefs exprLoweringProps exprSimHyps exprSimHypsDefs fragExec
  createSizeCutCode freshWrites vyperTypeSystem vyperValue compileEnv venomInst
  exprSimAbiGasBridge list pred_set

Triviality bop_bytes_word_guards:
  (?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  MEM bop [And;Or;XOr;ShL;ShR] /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2)
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv` by
    (qpat_assum `expr_body_pre _ _ _ e1 _`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `expr_type e1 = BaseT (BytesT (Fixed m))` SUBST_ALL_TAC >>
  gvs[well_typed_binop_def, is_int_type_def, is_word_type_def,
      evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
  Cases_on `expr_type e2` >> gvs[is_int_type_def, is_word_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, is_word_type_def]
QED

Triviality scalar_suffix_no_create:
  !code R A B. bop_scalar_seq R A code B ==>
    EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) code
Proof
  Induct >> simp[Once bop_scalar_seq_def] >> rpt strip_tac >>
  gvs[mk_inst_def, MEM] >> metis_tac[]
QED

Triviality bop_bytes_admin_inventory:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el a = (op,b) ==>
  (?B. bop_scalar_seq {z | not_fresh_at a z} ({x;y} UNION IMAGE Lit UNIV)
         (emitted_insts a b) B /\ op IN B) /\
  create_cut_code {} a b /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) bop_scalar_compile_binop_typed >>
  disch_then (drule_at (Pat `well_typed_binop _ _ _ _`)) >>
  disch_then (qspecl_then [`{z | not_fresh_at a z}`, `{x;y} UNION IMAGE Lit UNIV`] mp_tac) >>
  simp[] >> strip_tac >>
  `create_cut_code {} a b` by metis_tac[builtin_binop_code, pairTheory.SND] >>
  fs[same_blocks_def] >>
  `frag_code a b = emitted_insts a b` by simp[frag_code_def, emitted_blocks_def] >>
  conj_tac >- (qexists_tac `B` >> simp[]) >> simp[] >>
  drule_then assume_tac bop_scalar_seq_opcodes >>
  drule_then assume_tac scalar_suffix_no_create >>
  fs[create_cut_code_def, EVERY_MEM] >> metis_tac[]
QED

Theorem create_bop_bytes_geometry:
  (?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  MEM bop [And;Or;XOr;ShL;ShR] /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (Builtin ann (Bop bop) [e1;e2]) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) /\
  create_layout sa sb ==>
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  ?x y s1 s2 shadow_s1 shadow_s2.
    lower_value compile_expr ce (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr ce (expr_type e1) e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
      (gas_shadow_expr e1) sha = (x,shadow_s1) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
      (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
    compile_binop bop x y (expr_type e1)
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
    gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    s2.cs_next_var <= sb.cs_next_var /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
    (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
    cs_extends sha shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
    cs_extends shadow_s2 shb /\
    fn_has_code sa s1 f /\ fn_has_code s1 s2 f /\ fn_has_code s2 sb f /\
    fn_has_code sha shadow_s1 shf /\ fn_has_code shadow_s1 shadow_s2 shf /\
    fn_has_code shadow_s2 shb shf /\ fn_has_code s1 sb f /\
    create_layout sa s1 /\ create_layout s1 s2 /\ create_layout s1 sb /\ create_layout s2 sb /\
    create_cut_code {} sa s1 /\ create_cut_code {} s1 s2 /\
    create_cut_code {} s1 sb /\ create_cut_code {} s2 sb /\
    (?B. bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
           (emitted_insts s2 sb) B /\ op IN B) /\
    sb.cs_current_bb = s2.cs_current_bb /\
    sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
    EVERY (\i. i.inst_id IN frag_ids s2 sb /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts s2 sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_bytes_word_guards >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN `bop <> In /\ bop <> NotIn` (map_every assume_tac o CONJUNCTS)
  >- fs[MEM] >>
  qpat_x_assum `MEM bop _` kall_tac >>
  qpat_x_assum `?m. expr_type e1 = BaseT (BytesT (Fixed m))` kall_tac >>
  fs[expr_sim_full_pre_def] >> drule_all bop_full_layout >> strip_tac >>
  asm_rewrite_tac[] >> qexistsl_tac [`x`,`y`,`s1`,`s2`,`shadow_s1`,`shadow_s2`] >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    metis_tac[expr_body_pre_bop] >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) bop_bytes_admin_inventory >>
  disch_then (drule_at (Pat `well_typed_binop _ _ _ _`)) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code s1 sb f` by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `create_layout sa s1 /\ create_layout s1 s2 /\
   create_layout s1 sb /\ create_layout s2 sb` by
    (rpt conj_tac >> metis_tac[create_layout_subinterval, cs_extends_refl,
                              cs_extends_trans]) >>
  `create_cut_code {} sa s1 /\ create_cut_code {} s1 s2` by
    (rpt conj_tac >> metis_tac[cj 2 create_operand_cut_code, pairTheory.SND]) >>
  simp[] >> irule create_cut_code_join >> qexists_tac `s2` >> simp[]
QED

(* Compiler boundaries for word/word binary expressions, independent of execution. *)
Theory entryCreateBopWordGeometry
Ancestors
  bodyFullBopWordLayout augAssignPtrCompiler freshWrites
  createSizeOperandCode createSizeBuiltinBodyCode entryCreateIntervalLayout
  s1PrefixDefs exprLoweringProps exprSimHyps emitHelperProps fragExec
  createSizeCutCode exprSimAbiGasBridge vyperTypeSystem
  compileEnv venomInst list pred_set

Triviality bop_word_admin_inventory:
  well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el a = (op,b) ==>
  create_cut_code {} a b /\
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >>
  `create_cut_code {} a b` by
    metis_tac[builtin_binop_code, pairTheory.SND] >>
  `MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
            UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt;
            GtE; Exp; Min; Max; In; NotIn]` by
    (qpat_x_assum `well_typed_binop _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bop` >>
     simp[well_typed_binop_def]) >>
  drule compile_binop_straight_fresh_ptr >> simp[straight_fresh_def] >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `MEM bop _` kall_tac >> simp[] >>
  `frag_code a b = emitted_insts a b` by
    simp[frag_code_def, emitted_blocks_def] >>
  fs[create_cut_code_def, writes_fresh_def, EVERY_MEM] >>
  gen_tac >> disch_tac >>
  `i.inst_id IN frag_ids a b /\ fresh_write_op i.inst_opcode` by metis_tac[] >>
  simp[] >>
  qpat_x_assum `fresh_write_op _`
    (strip_assume_tac o SIMP_RULE bool_ss [fresh_write_op_def, MEM]) >>
  simp[is_terminator_def]
QED

Theorem create_bop_word_geometry:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty
    (Builtin ann (Bop bop) [e1;e2]) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) /\
  create_layout sa sb ==>
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
    fn_has_code shadow_s2 shb shf /\
    fn_has_code s1 sb f /\
    create_layout sa s1 /\ create_layout s1 s2 /\
    create_layout s1 sb /\ create_layout s2 sb /\
    create_cut_code {} sa s1 /\ create_cut_code {} s1 s2 /\
    create_cut_code {} s1 sb /\ create_cut_code {} s2 sb /\
    sb.cs_current_bb = s2.cs_current_bb /\
    sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
    EVERY (\i. i.inst_id IN frag_ids s2 sb /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (emitted_insts s2 sb)
Proof
  strip_tac >> fs[expr_sim_full_pre_def] >>
  drule_all bop_word_full_layout >> strip_tac >>
  qexistsl_tac [`x`,`y`,`s1`,`s2`,`shadow_s1`,`shadow_s2`] >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    metis_tac[expr_body_pre_bop] >>
  drule_all bop_word_admin_inventory >> strip_tac >>
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

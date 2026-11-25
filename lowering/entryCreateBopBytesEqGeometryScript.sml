(* The two ordered operand intervals and the installed comparison suffix. *)
Theory entryCreateBopBytesEqGeometry
Ancestors
  bodyFullBopBytesEqLayout entryCreateIntervalLayout createSizeOperandCode
  exprSimFullBundleProps exprSimOperators exprLoweringProps exprBopLowering
  exprLowering createSizeCutCode exprSimAbiGasBridge abiEncoderProps
  compileEnv emitHelper fragExec venomInst rich_list list arithmetic

Theorem bop_bytes_eq_suffix_geometry:
  (bop = Eq \/ bop = NotEq) /\
  compile_binop bop x y ty NONE NONE a = (op,b) ==>
  create_cut_code {} a b /\
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >> gvs[compile_binop_def, compile_compare_def, comp_bind_def,
    comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_return_def] >>
  simp[create_cut_code_def, frag_code_def, emitted_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, frag_ids_def, is_terminator_def] >>
  rpt strip_tac >> pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[cs_extends_def, create_cut_targets_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp_tac std_ss [rich_listTheory.IS_PREFIX_APPEND3, APPEND, NOT_CONS_NIL]
QED

Theorem create_bop_bytes_eq_geometry:
  (bop = Eq \/ bop = NotEq) /\
  (expr_type e1 = BaseT AddressT \/ ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  lower_value compile_expr ce ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2])) sha = (op,shb) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) /\
  create_layout sa sb ==>
  ?x s1 y s2 sh1 sh2.
    lower_value compile_expr ce (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr ce (expr_type e1) e2 s1 = (y,s2) /\
    compile_binop bop x y (expr_type e1) NONE NONE s2 = (op,sb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
      (gas_shadow_expr e1) sha = (x,sh1) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
      (gas_shadow_expr e2) sh1 = (y,sh2) /\
    compile_binop bop x y (expr_type e1) NONE NONE sh2 = (op,shb) /\
    gas_shadow_state s1 sh1 /\ gas_shadow_state s2 sh2 /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono sha sh1 /\ ci_mono sh1 sh2 /\
    cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
    cs_extends s1 sb /\ s2.cs_next_id <= sb.cs_next_id /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (sa,s1,sha,sh1) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (s1,s2,sh1,sh2) /\
    create_layout sa s1 /\ create_layout s1 sb /\
    create_layout s1 s2 /\ create_layout s2 sb /\
    create_cut_code {} sa s1 /\ create_cut_code {} s1 s2 /\
    create_cut_code {} s2 sb /\ create_cut_code {} s1 sb /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code s2 sb func /\ fn_has_code s1 sb func /\
    sb.cs_current_bb = s2.cs_current_bb /\
    sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
    EVERY (\i. i.inst_id IN frag_ids s2 sb /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts s2 sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_sim_full_code_fields >> strip_tac >>
  drule_all bop_bytes_eq_layout >> strip_tac >>
  qexistsl_tac [`x`,`s1`,`y`,`s2`,`sh1`,`sh2`] >> asm_rewrite_tac[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono sha sh1 /\ ci_mono sh1 sh2` by
    metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends sha sh1 /\ cs_extends sh1 sh2` by
    fs[ci_mono_def] >>
  `cs_extends s2 sb /\ cs_extends sh2 shb` by
    metis_tac[compile_binop_shape] >>
  `cs_extends s1 sb /\ cs_extends sh1 shb` by metis_tac[cs_extends_trans] >>
  `create_cut_code {} s2 sb /\
   sb.cs_current_bb = s2.cs_current_bb /\
   sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb /\
   EVERY (\i. i.inst_id IN frag_ids s2 sb /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts s2 sb)` by
    (irule bop_bytes_eq_suffix_geometry >>
     qpat_assum `compile_binop _ _ _ _ _ _ s2 = _` (irule_at Any) >> simp[]) >>
  `s2.cs_next_id <= sb.cs_next_id` by fs[create_cut_code_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
   fn_has_code sha sh1 shfunc /\ fn_has_code sh1 shb shfunc` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
   fn_has_code sh1 sh2 shfunc` by metis_tac[fn_has_code_split] >>
  `create_layout sa s1 /\ create_layout s1 sb /\
   create_layout s1 s2 /\ create_layout s2 sb` by
    metis_tac[create_layout_subinterval, cs_extends_refl, cs_extends_trans] >>
  `create_cut_code {} sa s1 /\ create_cut_code {} s1 s2` by
    metis_tac[create_operand_cut_code, pairTheory.SND] >>
  `create_cut_code {} s1 sb` by metis_tac[create_cut_code_join] >>
  simp[expr_sim_full_code_def]
QED

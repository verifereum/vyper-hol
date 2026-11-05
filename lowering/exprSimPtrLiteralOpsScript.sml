(* Opcode boundaries for literal buffer construction. *)
Theory exprSimPtrLiteralOps
Ancestors
  allocationPtr typedCopyPtr exprSimLiteralBuffer exprSimHypsDefs
  exprLowering ptrDiscipline venomExecSemantics venomMemDefs finite_map
  vyperTypeSystem vyperValue vyperAST exprSimProps compileEnv venomState venomInst

Theorem literal_nonword_classify:
  expr_sim_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
  (?bs n. l = BytesL bs /\ ann = BaseT (BytesT (Dynamic n))) \/
  (?str n. l = StringL str /\ ann = BaseT (StringT n))
Proof
  strip_tac >> gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `l` >> gvs[well_typed_literal_def, is_word_type_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[well_typed_literal_def, is_word_type_def, well_formed_type_def,
      vyperValueTheory.evaluate_type_def]
QED

Theorem literal_mstore_ghost:
  lookup_var dst s = SOME a ==>
  step_prov PG G (mk_inst id MSTORE [Var dst; Lit w] [])
    (mstore (w2n a) w s) = G /\
  step_taint (mk_inst id MSTORE [Var dst; Lit w] []) s
    (mstore (w2n a) w s) tn =
    tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  strip_tac >>
  drule mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`, `Lit w`, `w`] mp_tac) >>
  simp[eval_operand_def, op_taint_def] >> strip_tac >>
  simp[taint_component_equality, step_taint_def, imm_taint_def, mk_inst_def]
QED

Theorem literal_add_ghost:
  FLOOKUP G src = SOME site ==>
  step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
    (update_var dst v s) = G |+ (dst,site) /\
  step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
    (update_var dst v s) tn = tn with t_var := tn.t_var |+ (dst,{})
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, step_taint_def, set_var_taint_def,
       out_taint_def, eval_operand_def, mem_taint_def, new_site_bytes_def,
       update_var_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       taint_component_equality, FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
  Cases_on `lookup_var src s` >> simp[] >> metis_tac[]
QED

(* Static operand shapes at the end of the RawLog topic prefix. *)
Theory bodyRawLogOperandShapeMods
Ancestors
  exprWordOperand exprLoweringProps loweringShapeDefs loweringStateRelDefs
  exprLowering compileEnv vyperTypeSystem vyperAST finite_map list
Libs pairLib

Theorem raw_log_topic_operand_shape_mods:
  !suffix cenv env topics sa ops sm.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
           well_formed_type env.type_defs t) /\
    EVERY (\e. well_typed_expr env e /\
               expr_type e = BaseT (BytesT (Fixed 32))) topics /\
    EVERY (\e. MEM e topics) suffix /\
    compile_multi_exprs compile_expr cenv suffix sa = (ops,sm) ==>
    EVERY (\op. (!x. op = Var x ==> not_fresh_at sm x) /\
                 (!l. op <> Label l)) ops
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_multi_exprs compile_expr cenv suffix sa = (ops,sm)` mp_tac >>
  qpat_x_assum `EVERY (\e. MEM e topics) suffix` mp_tac >>
  map_every qid_spec_tac [`sm`,`ops`,`sa`,`suffix`] >>
  Induct >> simp[compile_multi_exprs_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `well_typed_expr env h /\ is_word_type (expr_type h)` by
    (fs[EVERY_MEM] >> simp[is_word_type_def] >> metis_tac[]) >>
  drule_all lower_value_word_shape >> strip_tac >>
  `ci_mono cs' (SND (compile_multi_exprs compile_expr cenv suffix cs'))` by
    (irule ci_mono_compile_multi_exprs >> simp[compile_expr_ci_mono]) >>
  gvs[ci_mono_def] >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
              qexists_tac `cs'` >> metis_tac[]) >>
  metis_tac[]
QED

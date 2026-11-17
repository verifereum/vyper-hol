(* Fixed-byte binary operators use typed words for both operands and result. *)
Theory exprSimBopBytes
Ancestors
  exprBopBytes exprSimBopTyped exprSimHyps exprSimSource exprSimHypsDefs
  exprSimDefs exprSimProps exprLoweringProps loweringPosts
  exprBopSimProps exprLowering compileEnv valueEncoding
  vyperTypeSystem vyperValue vyperTyping vyperAST vyperInterpreter
  list option

Theorem compile_bop_bytes_case:
  !nocalls ctx func cenv cx ann bop e1 e2.
    expr_sim_case nocalls ctx func cenv cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     expr_sim_case nocalls ctx func cenv cx e2) /\
    MEM bop [And;Or;XOr;ShL;ShR] /\
    (?m. expr_type e1 = BaseT (BytesT (Fixed m))) ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >> simp[Once expr_sim_case_def] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_operands >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `(nocalls ==> int_calls_expr e1 = []) /\
   (nocalls ==> int_calls_expr e2 = [])` by
    (Cases_on `nocalls` >> gvs[int_calls_expr_def]) >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `ann = expr_type e1 /\ is_word_type ann /\
   is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
   ~is_bytestring_type (expr_type e1) /\ ~is_ArrayT (expr_type e2)` by
    (gvs[] >> gvs[well_typed_binop_def, is_word_type_def,
                  is_int_type_def, is_bytestring_type_def]) >>
  `?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1` by
    (drule expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  `?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2` by
    (drule expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  irule compile_bop_rel_sim >> rpt conj_tac
  >~ [`binop_frag_post`]
  >- (qexistsl_tac [`tv1`, `tv2`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`,
                   `INL v1`, `es1`] mp_tac expr_body_pre_word_type_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v1` mp_tac) >> simp[] >> strip_tac >>
      `expr_body_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      `expr_sim_case nocalls ctx func cenv cx e2` by
        (drule eval_expr_read_INL >> strip_tac >> first_x_assum irule >>
         metis_tac[]) >>
      conj_tac >- (irule expr_sim_case_apply >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1 with gas_obs := gs2`,
                   `INL v2`, `es2`] mp_tac expr_body_pre_word_type_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v2` mp_tac) >> simp[] >> strip_tac >>
      drule eval_expr_read_INL >> strip_tac >>
      rev_drule eval_expr_read_INL >> strip_tac >>
      `(bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i)` by
        (strip_tac >> irule eval_expr_shift_amount >> metis_tac[]) >>
      irule binop_frag_bytes_typed >> simp[] >> metis_tac[])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`expr_sim`]
  >- (irule expr_sim_case_apply >> metis_tac[]) >>
  gvs[]
QED

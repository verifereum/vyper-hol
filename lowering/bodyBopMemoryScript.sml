(* Memory-checked binary operators at the body's judgments: S1's
   compile_bop_word_case (exprSimOperators) for expr_sim_mem, from the
   operands' body_expr_mem_ok. *)
Theory bodyBopMemory
Ancestors
  bodyBinopFamiliesMemory bodyBinopFragMemory bodyMemoryPreds exprSimOperators
  exprSimHyps
  exprSimSource exprSimHypsDefs exprSimMemDefs exprSimProps exprSimDefs
  exprBopSimDefs
  exprBopLowering compileEnv vyperTyping vyperValue vyperTypeSystem
  vyperInterpreter vyperState vyperAST

(* Two operands of word_value_type: compile_bop_sim_mem, the operands'
   simulation from their body_expr_mem_ok, e2's where e1 evaluates and is
   read, and binop_frag_typed_mem. *)
Theorem body_bop_word_mem:
  !cx ann bop e1 e2.
    body_expr_mem_ok cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     body_expr_mem_ok cx e2) /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
      expr_sim_mem ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop_operands >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `is_word_type (expr_type e1) /\ ~is_ArrayT (expr_type e1) /\
   ~is_bytestring_type (expr_type e1) /\
   is_word_type (expr_type e2) /\ ~is_ArrayT (expr_type e2) /\
   ~is_bytestring_type (expr_type e2)` by gvs[word_value_type_word] >>
  imp_res_tac expr_body_pre_type_evaluates >>
  `type_bits (expr_type e1) MOD 8 = 0` by
    (irule byte_widths_expr_type >> gvs[expr_body_pre_def]) >>
  `is_word_type ann` by (drule_all well_typed_binop_word_result >> simp[]) >>
  irule compile_bop_sim_mem >> rpt conj_tac
  >~ [`binop_frag_mem`]
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`,
                   `INL v1`, `es1`] mp_tac expr_body_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v1` mp_tac) >> simp[] >> strip_tac >>
      rename1 `value_has_type tv1 v1` >>
      `expr_body_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      `body_expr_mem_ok cx e2` by
        (drule eval_expr_read_INL >> strip_tac >> first_x_assum irule >>
         metis_tac[]) >>
      conj_tac >- gvs[] >>
      conj_tac
      >- (gvs[body_expr_mem_ok_def] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1 with gas_obs := gs2`,
                   `INL v2`, `es2`] mp_tac expr_body_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v2` mp_tac) >> simp[] >>
      strip_tac >> rename1 `value_has_type tv2 v2` >> simp[] >>
      drule eval_expr_read_INL >> strip_tac >>
      rev_drule eval_expr_read_INL >> strip_tac >>
      `(!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
       (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n)` by
        metis_tac[eval_expr_int_literal_agrees] >>
      `(bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i)` by
        (strip_tac >> irule eval_expr_shift_amount >> metis_tac[]) >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `e1`, `e2`,
                   `v1`, `v2`, `es2`, `tv1`, `tv2`] mp_tac binop_frag_typed_mem >>
      impl_tac >- (simp[] >> metis_tac[]) >> simp[binop_frag_val_mem_def])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`expr_sim_mem`]
  >- (gvs[body_expr_mem_ok_def] >> metis_tac[]) >>
  gvs[]
QED

(* == and != on two address or two bytesN operands: compile_bop_typed_sim_mem,
   the operands held in their typed words, with compile_compare_bytes_sim_mem
   for the EQ on them (S1's compile_bop_bytes_eq_case). *)
Theorem body_bop_bytes_eq_mem:
  !cx ann bop e1 e2.
    body_expr_mem_ok cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     body_expr_mem_ok cx e2) /\
    (bop = Eq \/ bop = NotEq) /\
    (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m))) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
      expr_sim_mem ctx func cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `expr_type e2 = expr_type e1 /\ ann = BaseT BoolT` by
    (qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
     gvs[well_typed_binop_def]) >>
  `?ot. evaluate_type (get_tenv cx) (expr_type e1) = SOME ot` by
    (qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`] mp_tac
       expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
   ~is_bytestring_type (expr_type e1) /\ ~is_ArrayT (expr_type e2)` by
    (qpat_x_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
     gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION,
         is_word_type_def, is_bytestring_type_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e2) = SOME ot` by gvs[] >>
  irule compile_bop_typed_sim_mem >> rpt conj_tac
  >~ [`binop_frag_mem`]
  >- (qexistsl_tac [`ot`, `ot`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es with gas_obs := gs1`,
                   `INL v1`, `es1`] mp_tac expr_body_pre_word_type_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v1` mp_tac) >> simp[] >> strip_tac >>
      `expr_body_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      `body_expr_mem_ok cx e2` by
        (drule eval_expr_read_INL >> strip_tac >> first_x_assum irule >>
         metis_tac[]) >>
      conj_tac
      >- (gvs[body_expr_mem_ok_def] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1 with gas_obs := gs2`,
                   `INL v2`, `es2`] mp_tac expr_body_pre_word_type_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `v2` mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
      gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
      Cases_on `v1` >> Cases_on `v2` >> gvs[value_has_type_def] >>
      irule compile_compare_bytes_sim_mem >> fs[value_has_type_def])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >>
      drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
  >~ [`expr_sim_mem`]
  >- (gvs[body_expr_mem_ok_def] >> metis_tac[]) >>
  gvs[is_word_type_def]
QED

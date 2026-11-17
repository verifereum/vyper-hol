(* Memory case of the body induction: the binary operators bodyMemBop and
   bodyMemBopHeld leave, which typing narrows to in and not in with a word
   needle on an array that is not a literal.  The memory twin of S1's
   exprSimBopRestWord (compile_bop_rest_word_case). *)
Theory bodyMemBopRestWord
Ancestors
  bodyMemoryPreds compileEnv bodyMemBopRestWordSim exprSimBopRestWordFacts
  exprSimMemoryStack exprSimOperators exprSimHyps exprSimHypsDefs exprLoweringProps
  bodyBinopFragMemory bodyBinopFamiliesMemory exprBopBytes exprBopBitwise exprBopShift exprSimBinopFrag
  exprSimSource exprSimMemDefs exprSimDefs exprSimProps exprBopSimProps
  exprLowering exprBopLowering loweringPosts valueEncoding valueEncodingProofs
  valueEncodingBitwise vyperTypeSystem vyperTyping vyperValueOperation
  vyperContext vyperValue vyperInterpreter vyperState vyperAST
  list option words


Theorem body_bop_bytes_sim_mem:
  !cx ann bop e1 e2.
    body_exprs_mem_ok cx [e1; e2] /\
    MEM bop [And;Or;XOr;ShL;ShR] /\
    (?m. expr_type e1 = BaseT (BytesT (Fixed m))) ==>
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
  `?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1` by
    (qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`] mp_tac
       expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  `?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2` by
    (qspecl_then [`cenv`, `cx`, `env`, `e2`, `es`] mp_tac
       expr_body_pre_type_evaluates >> simp[IS_SOME_EXISTS]) >>
  `ann = expr_type e1 /\ is_word_type ann /\
   is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
   ~is_bytestring_type (expr_type e1) /\ ~is_ArrayT (expr_type e2)` by
    (qpat_x_assum `expr_type e1 = BaseT (BytesT (Fixed m))` SUBST_ALL_TAC >>
     gvs[well_typed_binop_def, is_word_type_def,
                  is_int_type_def, is_bytestring_type_def,
                  vyperValueTheory.evaluate_type_def,
                  optionTheory.IF_EQUALS_OPTION] >>
     Cases_on `expr_type e2` >> gvs[is_int_type_def, is_word_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  `body_expr_mem_ok cx e1 /\
   ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv,t) /\
                      read_result cx tv s1 = (INL v,t1)) ==>
    body_expr_mem_ok cx e2)` by
    (fs[body_exprs_mem_ok_def] >> first_assum ACCEPT_TAC) >>
  irule compile_bop_rel_sim_mem >> rpt conj_tac
  >~ [`binop_frag_mem_post`] >- suspend "fragment"
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

Resume body_bop_bytes_sim_mem[fragment]:
  qexistsl_tac [`tv1`, `tv2`] >>
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
  conj_tac >- (gvs[body_expr_mem_ok_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1 with gas_obs := gs2`,
               `INL v2`, `es2`] mp_tac expr_body_pre_word_type_result >>
  impl_tac >- gvs[] >> strip_tac >>
  first_x_assum (qspec_then `v2` mp_tac) >> simp[] >> strip_tac >>
  drule eval_expr_read_INL >> strip_tac >>
  rev_drule eval_expr_read_INL >> strip_tac >>
  `(bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i)` by
    (strip_tac >> irule eval_expr_shift_amount >> metis_tac[]) >>
  irule binop_frag_bytes_typed_mem >> simp[] >> metis_tac[]
QED
Finalise body_bop_bytes_sim_mem

Theorem body_bop_rest_word_mem:
  !cx ty bop e1 e2.
    ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
    ~((bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  qmatch_goalsub_rename_tac
    `expr_sim_mem ctx func cenv cx result_ty (Builtin ty (Bop bop) [e1;e2]) es` >>
  `well_typed_binop ty bop (expr_type e1) (expr_type e2)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.well_typed_builtin_app_def]) >>
  `IS_SOME (evaluate_type (get_tenv cx) ty)` by
    (drule expr_body_pre_type_evaluates >> simp[expr_type_def]) >>
  `expr_sim_mem ctx func cenv cx result_ty (Builtin ty (Bop bop) [e1;e2]) es /\
   is_word_type ty` by
    (drule_all rest_word_typed_membership >> strip_tac
     >- (conj_tac
         >- (irule body_bop_bytes_sim_mem >> metis_tac[]) >>
         qpat_x_assum `expr_type e1 = BaseT (BytesT (Fixed m))` SUBST_ALL_TAC >>
         qpat_assum `MEM bop [And;Or;XOr;ShL;ShR]`
           (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
         gvs[well_typed_binop_def, is_word_type_def,
             vyperValueTheory.evaluate_type_def,
             optionTheory.IF_EQUALS_OPTION, IS_SOME_EXISTS]) >>
     (conj_tac
     >- (irule compile_rest_word_membership_sim_mem >> metis_tac[]) >>
     gvs[well_typed_binop_def, is_word_type_def])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule body_expr_vv_sim_mem_stack_word >> simp[compile_bop_stack] >>
  rpt conj_tac
  >>~- ([`Value`], metis_tac[eval_expr_builtin_value]) >>
  fs[vyperASTTheory.expr_type_def]
QED

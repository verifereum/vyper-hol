(* Linked strict binary bit operations on fixed-width bytes. *)
Theory bodyBopFixedBytesBitsMods
Ancestors
  bodyBopWordOperandsMods bodyBopWordNormalPostMods bodyFullBopWordSuccess
  bodyPtrBopScalarDispatch exprSimBopRestWordFacts exprBopBytes
  exprSafeOperand exprWordOperand exprSimOperators exprSimHyps exprBodyPreProps
  bodySimStmtFacts gasShadowCompileStmtHelpers exprSimFullBundleProps
  gasOutcomeFullPostMods exprBopSimProps exprBopLowering exprSimSource
  exprLoweringProps vyperTypeSystem vyperTypeBuiltins vyperTypeInvariants
  vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperStorageTrace gasStorage compileEnv
  bodyFullPostsMods loweringPosts fragExec exprBopSimDefs freshWrites
  exprSimHypsDefs list
Libs monadsyntax

Theorem fixed_bits_typing[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  bop <> In /\ bop <> NotIn /\
  ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
  ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
  ~((bop = Eq \/ bop = NotEq) /\ (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) ==>
  (?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  MEM bop [And;Or;XOr;ShL;ShR] /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e2) /\
  well_typed_expr env e1 /\ well_typed_expr env e2 /\
  (!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def,
       constSubstCorrectTheory.frame_well_typed_exprs_cons] >> strip_tac >>
  `(?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\ MEM bop [And;Or;XOr;ShL;ShR]` by
    (drule rest_word_typed_membership >>
     (impl_tac >- (asm_rewrite_tac[] >> simp[])) >> simp[]) >>
  `bop = ShL \/ bop = ShR ==> shift_amount_ok e2` by
    (strip_tac >> gvs[builtin_operands_ok_def]) >>
  simp[] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv` by
    (qpat_assum `well_typed_expr env e1`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] well_typed_expr_type_well_formed)) >>
     asm_rewrite_tac[] >> simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `!t. is_int_type t ==> is_word_type t` by
    (Cases >> simp[is_int_type_def] >> rename1 `is_int_type (BaseT bt) ==> _` >>
     Cases_on `bt` >> simp[is_int_type_def, is_word_type_def]) >>
  qpat_x_assum `expr_type e1 = BaseT (BytesT (Fixed m))` SUBST_ALL_TAC >>
  qpat_x_assum `MEM bop [And;Or;XOr;ShL;ShR]` (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  gvs[well_typed_binop_def, is_int_type_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `!t. is_int_type t ==> _` irule >> first_assum ACCEPT_TAC))
QED

(* The forced source value at a successful child landing is typed at the
   linked environment; for shift amounts this includes the sign check. *)
Theorem fixed_bits_read_typed[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  expr_sim_inv_mods mods ce cx env ee /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (shift_amount_ok e ==> ?i. v = IntV i /\ 0 <= i)
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[value_runtime_typed_def] >>
  simp[] >> conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] bop_value_scopes_dom) >> simp[]) >>
  strip_tac >> drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  drule_all eval_expr_shift_amount >> simp[]
QED

Theorem fixed_bits_operand_encoding[local]:
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op u /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==> eval_operand op u = SOME (typed_val_to_w256 tv v)
Proof
  strip_tac >> fs[expr_post_mods_def,expr_post_def,post_value_type_word] >>
  drule_all expr_val_rel_typed >> simp[]
QED

Theorem fixed_bits_child_pres[local]:
  expr_body_pre_mods mods ce cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_body_pre_mods mods ce cx env e1 es /\
  (!mid. expr_sim_inv_mods mods ce cx env mid ==> expr_body_pre_mods mods ce cx env e2 mid)
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, well_typed_builtin_app_def,
       vyperTypeCallGraphTheory.int_calls_expr_def, allocLimitsTheory.alloc_limits_expr_def,
       supportedExprTraverseTheory.supported_expr_exists_def, EVERY_APPEND,
       byte_widths_expr_def, supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  strip_tac >> drule_then assume_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  drule_then assume_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  fs[constSubstCorrectTheory.frame_well_typed_exprs_cons]
QED

Theorem fixed_bits_raw_run[local]:
  expr_type e1 = BaseT (BytesT (Fixed m)) /\ MEM bop [And;Or;XOr;ShL;ShR] /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e2) /\
  expr_body_pre_mods mods ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs1) = (INL v1,mid) /\
  bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs2) = (INL v2,fin) /\
  expr_post_mods H1 ctx func ce cx e1 es sa s1 s0 mid v1 x t /\
  expr_post_mods H2 ctx func ce cx e2 mid s1 s2 t fin v2 y u /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ s1.cs_next_var <= s2.cs_next_var /\
  compile_binop bop x y (expr_type e1) bl el s2 = (op,sb) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  ?v r. bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
        run_inst_seq (emitted_insts s2 sb) u = OK r /\ expr_val_rel cx ann v op r
Proof
  strip_tac >> drule_then strip_assume_tac fixed_bits_child_pres >>
  drule_all_then strip_assume_tac fixed_bits_read_typed >>
  qpat_assum `!mid. expr_sim_inv_mods _ _ _ _ mid ==> _`
    (qspec_then `mid` (drule_then assume_tac)) >>
  drule_all_then strip_assume_tac fixed_bits_read_typed >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v1)` by
    (irule fixed_bits_operand_encoding >> conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `eval_operand y u = SOME (typed_val_to_w256 tv' v2)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
         fixed_bits_operand_encoding) >>
     simp[] >> disch_then irule >> qexists_tac `tv'` >> simp[]) >>
  simp[] >>
  `eval_operand x u = SOME (typed_val_to_w256 tv v1)` by
    (irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s1`,`t`] >> fs[expr_post_mods_def,expr_post_def]) >>
  `!z. x = Var z ==> not_fresh_at s2 z` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `expr_type e1 = _` SUBST_ALL_TAC >>
  irule compile_bytes_binop_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`expr_type e2`,`get_tenv cx`,`tv`,`tv'`] >> simp[] >> metis_tac[]
QED

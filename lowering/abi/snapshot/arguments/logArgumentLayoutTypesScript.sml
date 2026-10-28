(* TOP-LEVEL: the compiler's produced Log argument layout types evaluate
   under the same source type environment as their checked annotations. *)
Theory logArgumentLayoutTypes
Ancestors
  logArgumentTyping logArgumentTypes logArgumentTypeEval typedCopyCompatibility
  eventTopicValueProps abiTypeShape vyperTypeSystem vyperTypeInvariants
  exprLowering stmtLowering eventLoweringStructure compileEnv vyperAST vyperValue list arithmetic combin

Theorem well_formed_bytestring_bound_narrow:
  (!tenv bound size.
    well_formed_type tenv (BaseT (StringT bound)) /\ size <= bound ==>
    well_formed_type tenv (BaseT (StringT size))) /\
  (!tenv bound size.
    well_formed_type tenv (BaseT (BytesT (Dynamic bound))) /\ size <= bound ==>
    well_formed_type tenv (BaseT (BytesT (Dynamic size))))
Proof
  conj_tac >> rpt gen_tac >>
  simp[well_formed_type_def, Once evaluate_type_def, type_slot_size_def] >>
  strip_tac >> drule_all word_size_monotone >>
  simp[Once evaluate_type_def, type_slot_size_def] >> decide_tac
QED

Theorem compatible_bytestring_type_well_formed:
  !tenv ann ty.
    well_formed_type tenv ann /\ event_arg_compatible ann ty /\
    (ty = ann \/ (?n. ty = BaseT (StringT n)) \/ (?n. ty = BaseT (BytesT (Dynamic n)))) ==>
    well_formed_type tenv ty
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  gvs[event_arg_compatible_bytestring_rhs] >>
  FIRST [drule_all (CONJUNCT1 well_formed_bytestring_bound_narrow) >> simp[],
    drule_all (CONJUNCT2 well_formed_bytestring_bound_narrow) >> simp[]]
QED

Theorem lowered_literal_value_type_cases:
  !cenv ann lit.
    lowered_value_type cenv (Literal ann lit) = ann \/
    (?n. lowered_value_type cenv (Literal ann lit) = BaseT (StringT n)) \/
    (?n. lowered_value_type cenv (Literal ann lit) = BaseT (BytesT (Dynamic n)))
Proof
  rpt gen_tac >> Cases_on `ann` >> Cases_on `lit` >>
  simp[lowered_value_type_def, expr_type_def] >>
  rename1 `Literal (BaseT bt) _` >> Cases_on `bt` >>
  simp[lowered_value_type_def, expr_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[lowered_value_type_def, expr_type_def]
QED

Theorem lowered_value_type_cases:
  !cenv e.
    lowered_value_type cenv e = expr_type e \/
    (?n. lowered_value_type cenv e = BaseT (StringT n)) \/
    (?n. lowered_value_type cenv e = BaseT (BytesT (Dynamic n)))
Proof
  rpt gen_tac >> Cases_on `e` >>
  FIRST [simp_tac bool_ss [expr_type_def] >> MATCH_ACCEPT_TAC lowered_literal_value_type_cases,
    simp[lowered_value_type_def, expr_type_def] >>
      rename1 `TypeBuiltin _ tb _ _` >> Cases_on `tb` >>
      simp[lowered_value_type_def, expr_type_def, LET_THM]]
QED

Theorem checked_expr_lowered_type_well_formed:
  !env cx st cenv e.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_expr env e ==>
    well_formed_type env.type_defs (lowered_value_type cenv e)
Proof
  rpt gen_tac >> strip_tac >>
  `well_formed_type env.type_defs (expr_type e)` by
    (drule_all checked_expr_type_well_formed >> simp[]) >>
  `event_arg_compatible (expr_type e) (expr_type e)` by
    simp[event_arg_compatible_reflexive] >>
  drule_all checked_expr_event_arg_compatible >> DISCH_TAC >>
  qspecl_then [`env.type_defs`, `expr_type e`, `lowered_value_type cenv e`]
    mp_tac compatible_bytestring_type_well_formed >>
  impl_tac >- simp[lowered_value_type_cases] >> simp[]
QED

Theorem compatible_lowered_nonbytes_type:
  !cenv e.
    event_arg_compatible (expr_type e) (lowered_value_type cenv e) /\
    ~is_bytestring_type (expr_type e) ==>
    lowered_value_type cenv e = expr_type e
Proof
  rpt gen_tac >> strip_tac >> qspecl_then [`cenv`, `e`] mp_tac lowered_value_type_cases >>
  strip_tac >> gvs[event_arg_compatible_bytestring_rhs, is_bytestring_type_def]
QED

Theorem checked_exprs_lowered_type_evaluations:
  !args env cx st cenv.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_exprs env args ==>
    ?tvs. LIST_REL (\e tv. evaluate_type env.type_defs (lowered_value_type cenv e) = SOME tv) args tvs
Proof
  Induct_on `args` >- simp[] >> rpt gen_tac >>
  rename1 `well_typed_exprs env (e::rest)` >>
  simp_tac bool_ss [Once well_typed_expr_def] >> strip_tac >>
  `well_formed_type env.type_defs (lowered_value_type cenv e)` by
    (drule_all checked_expr_lowered_type_well_formed >> simp[]) >>
  qpat_x_assum `well_formed_type _ _`
    (mp_tac o REWRITE_RULE [well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  disch_then (qx_choose_then `tv` ASSUME_TAC) >>
  first_x_assum drule_all >> disch_then (qx_choose_then `tvs` ASSUME_TAC) >>
  qexists_tac `tv::tvs` >> simp[]
QED

Theorem checked_compile_log_eval_all_type_evaluations:
  !env cx st cenv args cs.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_exprs env args ==>
    ?tvs. LIST_REL (\arg tv. evaluate_type env.type_defs (SND arg) = SOME tv)
      (FST (compile_log_eval_all cenv args cs)) tvs
Proof
  rpt gen_tac >> strip_tac >> drule_all checked_exprs_lowered_type_evaluations >>
  disch_then (qx_choose_then `tvs` ASSUME_TAC) >> qexists_tac `tvs` >>
  `LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv)
    (MAP SND (FST (compile_log_eval_all cenv args cs))) tvs` by
    (simp_tac bool_ss [compile_log_eval_all_types] >> simp[LIST_REL_MAP1, o_DEF]) >>
  fs[LIST_REL_MAP1, o_DEF]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked produced Log layout type evaluation: " ^ name)
  end) (DB.thms "logArgumentLayoutTypes")

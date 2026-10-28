Theory sourceMeaningCode
Ancestors
  sourceMeaningDefs sourceMeaningValue sourceExprElaborate sourceConstValueProps sourceConstValueStructuredProps
  sourceConstValueStructured sourceConstValue sourceExprDefs
  vyperInterpreter vyperAST vyperState vyperValue vyperContext
  vyperValueOperation vyperTyping vyperTypeSystem alist finite_map vfmTypes

(* A code relation, not a definition of source meaning. The source rules and
   evaluator in sourceMeaningDefs make no reference to this relation. *)
Inductive source_meaning_code:
[literal:]
  source_const_value_literal sv = SOME lit /\
  sourceConstValueStructured$source_const_reify FEMPTY tenv ty sv = SOME e /\
  expr_type e = ty ==>
  source_meaning_code tenv bindings (SM_Literal ty lit) e
[name:]
  ALOOKUP bindings path = SOME (SE_Runtime e) /\ expr_type e = ty ==>
  source_meaning_code tenv bindings (SM_Name ty path) e
[unary:]
  source_meaning_code tenv bindings m e ==>
  source_meaning_code tenv bindings (SM_Unary ty uop m)
    (Builtin ty (source_expr_unary uop) [e])
[binary:]
  source_meaning_code tenv bindings l le /\ source_meaning_code tenv bindings r re ==>
  source_meaning_code tenv bindings (SM_Binary ty bop l r)
    (Builtin ty (Bop (source_expr_binary bop)) [le;re])
[conditional:]
  source_meaning_code tenv bindings c ce /\ source_meaning_code tenv bindings l le /\
  source_meaning_code tenv bindings r re ==>
  source_meaning_code tenv bindings (SM_If ty c l r) (IfExp ty ce le re)
[revert:]
  source_meaning_code tenv bindings m e ==>
  source_meaning_code tenv bindings (SM_Revert ty m) (Call ty RawRevert [e] NONE)
[aggregate:]
  sourceConstValueStructured$source_const_reify FEMPTY tenv ty sv = SOME e /\
  expr_type e = ty ==>
  source_meaning_code tenv bindings (SM_Constant ty sv) e
End

Definition source_meaning_names_def:
  source_meaning_names (SM_Literal ty lit) = [] /\
  source_meaning_names (SM_Name ty path) = [path] /\
  source_meaning_names (SM_Unary ty op m) = source_meaning_names m /\
  source_meaning_names (SM_Binary ty op l r) = source_meaning_names l ++ source_meaning_names r /\
  source_meaning_names (SM_If ty c l r) =
    source_meaning_names c ++ source_meaning_names l ++ source_meaning_names r /\
  source_meaning_names (SM_Revert ty m) = source_meaning_names m /\
  source_meaning_names (SM_Constant ty sv) = []
End

Theorem source_meaning_boolean_literal_code:
  source_meaning_code tenv bindings
    (SM_Literal (BaseT BoolT) (BoolL b)) (Literal (BaseT BoolT) (BoolL b))
Proof
  irule literal >> simp[expr_type_def] >> qexists_tac `SCV_Bool b` >>
  simp[source_const_value_literal_def] >>
  irule source_const_reify_primitive_agrees >>
  simp[sourceConstValueTheory.source_const_reify_def,
    source_const_value_literal_def,
    well_formed_type_def, well_typed_literal_def, evaluate_type_def]
QED

Theorem source_meaning_boolean_code:
  !ms es. LIST_REL (source_meaning_code tenv bindings) ms es ==>
  source_meaning_code tenv bindings (source_meaning_boolean op ms)
    (source_expr_boolean_runtime op es)
Proof
  Induct >> Cases_on `es` >>
  simp[source_meaning_boolean_def, source_expr_boolean_runtime_def,
    source_meaning_boolean_literal_code] >> rpt strip_tac >>
  Cases_on `ms` >> Cases_on `t` >> gvs[] >>
  Cases_on `op` >> simp[] >> irule conditional >>
  simp[source_meaning_boolean_literal_code]
QED

Theorem source_meaning_boolean_names:
  !ms path. MEM path (source_meaning_names (source_meaning_boolean op ms)) ==>
    ?m. MEM m ms /\ MEM path (source_meaning_names m)
Proof
  Induct >> simp[source_meaning_boolean_def, source_meaning_names_def] >>
  rpt strip_tac >> Cases_on `ms` >> gvs[source_meaning_names_def] >>
  Cases_on `op` >> gvs[source_meaning_names_def] >> metis_tac[]
QED

Theorem source_meaning_code_type:
  !tenv bindings m e. source_meaning_code tenv bindings m e ==>
    expr_type e = source_meaning_type m
Proof
  ntac 2 gen_tac >> ho_match_mp_tac source_meaning_code_ind >>
  rw[source_meaning_type_def, expr_type_def]
QED

(* Scalar reification has the independently specified literal value. It leaves
   all state unchanged, without assuming any state well-formedness invariant. *)
Theorem source_meaning_reify_evaluates:
  sourceConstValueStructured$source_const_reify FEMPTY tenv ty sv = SOME e /\
  source_const_value_literal sv = SOME lit /\ get_tenv cx = tenv ==>
  !st. eval_expr cx e st = (INL (Value (evaluate_literal lit)),st)
Proof
  strip_tac >> drule sourceConstValueStructuredPropsTheory.source_const_reify_sound >>
  strip_tac >> drule source_const_value_literal_represents >> strip_tac >>
  `source_const_represents sv v` by
    (Cases_on `sv` >> gvs[source_const_value_literal_def,
      source_const_structured_represents_def]) >>
  `v = evaluate_literal lit` by metis_tac[source_const_represents_unique] >> gvs[]
QED

Theorem source_meaning_aggregate_evaluates:
  sourceConstValueStructured$source_const_reify FEMPTY tenv ty sv = SOME e /\
  get_tenv cx = tenv ==>
  eval_expr cx e = source_meaning_eval cx meanings (SM_Constant ty sv)
Proof
  strip_tac >> drule source_meaning_value_reify >> strip_tac >>
  simp[FUN_EQ_THM, source_meaning_eval_def, lift_option_type_def,
    lift_option_def, bind_def, return_def]
QED

Theorem source_meaning_args_code:
  !es. source_meaning_args cx (MAP (eval_expr cx) es) = eval_exprs cx es
Proof
  Induct >> simp[source_meaning_args_def, Once evaluate_def, FUN_EQ_THM]
QED

Theorem source_meaning_args_one:
  source_meaning_args cx [eval_expr cx e] = eval_exprs cx [e]
Proof
  mp_tac (Q.SPEC `[e]` source_meaning_args_code) >> simp[]
QED

Theorem source_meaning_args_two:
  source_meaning_args cx [eval_expr cx l;eval_expr cx r] = eval_exprs cx [l;r]
Proof
  mp_tac (Q.SPEC `[l;r]` source_meaning_args_code) >> simp[]
QED

Theorem source_meaning_unary_runtime:
  eval_expr cx (Builtin ty (source_expr_unary op) [e]) =
  source_meaning_apply cx ty (source_expr_unary op) [expr_type e] [eval_expr cx e]
Proof
  Cases_on `op` >>
  simp[source_expr_unary_def, Once evaluate_def, source_meaning_apply_def,
       source_meaning_args_one, bind_def,
       ignore_bind_def, return_def, FUN_EQ_THM] >>
  rpt gen_tac >> rpt (CASE_TAC >> gvs[])
QED

Theorem source_meaning_binary_runtime:
  eval_expr cx (Builtin ty (Bop (source_expr_binary op)) [l;r]) =
  source_meaning_apply cx ty (Bop (source_expr_binary op)) [expr_type l;expr_type r]
    [eval_expr cx l;eval_expr cx r]
Proof
  simp[Once evaluate_def, source_meaning_apply_def,
       source_meaning_args_two, bind_def,
       ignore_bind_def, return_def, FUN_EQ_THM] >>
  rpt gen_tac >> rpt (CASE_TAC >> gvs[])
QED

Theorem source_meaning_code_evaluates_on:
  !tenv bindings m e. source_meaning_code tenv bindings m e ==>
  !cx meanings.
    get_tenv cx = tenv /\
    (!path code. MEM path (source_meaning_names m) /\
      ALOOKUP bindings path = SOME (SE_Runtime code) ==>
      eval_expr cx code = meanings path) ==>
    eval_expr cx e = source_meaning_eval cx meanings m
Proof
  ntac 2 gen_tac >> ho_match_mp_tac source_meaning_code_strongind >> rpt conj_tac >>
  rpt gen_tac >> simp[source_meaning_names_def] >> rpt strip_tac >>
  TRY (irule source_meaning_aggregate_evaluates >> metis_tac[] >> NO_TAC)
  >- (simp[source_meaning_eval_def, FUN_EQ_THM, return_def] >>
      irule source_meaning_reify_evaluates >> metis_tac[])
  >- (simp[source_meaning_eval_def] >> metis_tac[])
  >- (drule source_meaning_code_type >> strip_tac >>
      simp[source_meaning_eval_def, source_meaning_unary_runtime] >> metis_tac[])
  >- (imp_res_tac source_meaning_code_type >>
      simp[source_meaning_eval_def, source_meaning_binary_runtime] >> metis_tac[])
  >- (simp[source_meaning_eval_def, Once evaluate_def] >> metis_tac[])
  >> simp[source_meaning_eval_def, Once evaluate_def,
          GSYM source_meaning_args_code] >> metis_tac[]
QED

(* Stronger, local agreement suffices for code simulation. This includes
   arbitrary effectful bindings, but requires their actual denotations at all
   states reached by left-to-right evaluation, not an initial-state tautology. *)
Theorem source_meaning_code_evaluates:
  !tenv bindings m e. source_meaning_code tenv bindings m e ==>
  !cx meanings.
    get_tenv cx = tenv /\
    (!path code. ALOOKUP bindings path = SOME (SE_Runtime code) ==>
      eval_expr cx code = meanings path) ==>
    eval_expr cx e = source_meaning_eval cx meanings m
Proof
  ntac 2 gen_tac >> ho_match_mp_tac source_meaning_code_strongind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >>
  TRY (irule source_meaning_aggregate_evaluates >> metis_tac[] >> NO_TAC)
  >- (simp[source_meaning_eval_def, FUN_EQ_THM, return_def] >>
      irule source_meaning_reify_evaluates >> metis_tac[])
  >- (simp[source_meaning_eval_def] >> metis_tac[])
  >- (drule source_meaning_code_type >> strip_tac >>
      simp[source_meaning_eval_def, source_meaning_unary_runtime] >> metis_tac[])
  >- (imp_res_tac source_meaning_code_type >>
      simp[source_meaning_eval_def, source_meaning_binary_runtime] >> metis_tac[])
  >- (simp[source_meaning_eval_def, Once evaluate_def] >> metis_tac[])
  >> simp[source_meaning_eval_def, Once evaluate_def,
          GSYM source_meaning_args_code] >> metis_tac[]
QED

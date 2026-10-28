Theory sourceConstValueProps
Ancestors
  sourceConstValue vyperTypeValues vyperInterpreter vyperState
  vyperAST vyperValue vyperValueOperation vyperTyping vyperTypeSystem option
  sourceConstEval

(* ===== Literal conversion boundary ===== *)

Theorem source_const_value_literal_represents:
  source_const_value_literal sv = SOME lit ==>
  source_const_represents sv (evaluate_literal lit)
Proof
  Cases_on `sv` >>
  simp[source_const_value_literal_def, source_const_represents_def,
       evaluate_literal_def] >> rpt strip_tac >> gvs[evaluate_literal_def]
QED

Theorem source_const_represents_unique:
  source_const_represents sv v /\ source_const_represents sv w ==> v = w
Proof
  Cases_on `sv` >> simp[source_const_represents_def]
QED

Theorem source_const_reify_literal:
  source_const_reify tenv ty sv = SOME e ==>
  ?lit. e = Literal ty lit /\ source_const_value_literal sv = SOME lit /\
        well_formed_type tenv ty /\ well_typed_literal ty lit
Proof
  simp[source_const_reify_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem source_const_reify_iff:
  source_const_reify tenv ty sv = SOME e <=>
  ?lit. e = Literal ty lit /\ source_const_value_literal sv = SOME lit /\
        well_formed_type tenv ty /\ well_typed_literal ty lit
Proof
  eq_tac >- simp[source_const_reify_literal] >>
  rpt strip_tac >> gvs[source_const_reify_def]
QED

Theorem source_const_reify_well_typed:
  source_const_reify env.type_defs ty sv = SOME e ==>
  expr_type e = ty /\ well_typed_expr env e
Proof
  strip_tac >> drule source_const_reify_literal >> strip_tac >>
  gvs[well_typed_expr_def, expr_type_def]
QED

(* TOP-LEVEL: a successful local reification has a represented, typed runtime
   value and evaluates to it without changing ANY component of the state.
   No correspondence between cx and tenv (or state invariant) is necessary:
   literals do not consult either context or state. *)
Theorem source_const_reify_sound:
  source_const_reify tenv ty sv = SOME e ==>
  ?tv v. evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
         source_const_represents sv v /\
         (!cx st. eval_expr cx e st = (INL (Value v), st))
Proof
  strip_tac >> drule source_const_reify_literal >> strip_tac >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  drule_all well_typed_literal_sound >> strip_tac >>
  drule source_const_value_literal_represents >> strip_tac >>
  qexists_tac `evaluate_literal lit` >>
  simp[Once evaluate_def, return_def]
QED

(* The combined public certificate includes static expression typing as well
   as runtime typing. The expected type comes from the caller. *)
Theorem source_const_reify_correct:
  source_const_reify env.type_defs ty sv = SOME e ==>
  expr_type e = ty /\ well_typed_expr env e /\
  ?tv v. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v /\
         source_const_represents sv v /\
         (!cx st. eval_expr cx e st = (INL (Value v), st))
Proof
  strip_tac >> drule source_const_reify_well_typed >> strip_tac >>
  drule source_const_reify_sound >> simp[]
QED

Theorem source_const_reify_value_ok:
  source_const_reify tenv ty sv = SOME e ==> source_const_value_ok sv
Proof
  strip_tac >> drule source_const_reify_literal >> strip_tac >>
  Cases_on `sv` >> gvs[source_const_value_literal_def, source_const_value_ok_def]
QED

(* Aggregate values are not serialized into BytesL or otherwise flattened.
   Extending this bridge must supply structured expressions and separate
   nominal identity / array bound / child representation obligations. *)
Theorem source_const_reify_aggregate_rejected[simp]:
  source_const_reify tenv ty (SCV_List vs) = NONE /\
  source_const_reify tenv ty (SCV_Tuple vs) = NONE /\
  source_const_reify tenv ty (SCV_Struct path fields) = NONE
Proof
  simp[source_const_reify_def, source_const_value_literal_def]
QED

Theorem source_const_reify_bytes_type_rejected[simp]:
  source_const_reify tenv ty (SCV_BytesType fixed n) = NONE /\
  ~source_const_represents (SCV_BytesType fixed n) v
Proof
  simp[source_const_reify_def, source_const_value_literal_def,
       source_const_represents_def]
QED

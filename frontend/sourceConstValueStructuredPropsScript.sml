Theory sourceConstValueStructuredProps
Ancestors
  sourceConstValueAggregateLib sourceConstValueStructured sourceConstValueProps
  sourceConstValue sourceConstEval vyperTypeValues vyperInterpreter vyperState
  vyperContext vyperAST vyperValue vyperValueOperation vyperTyping
  vyperTypeSystem list rich_list option pair

Theorem source_const_reify_list_certificate:
  well_formed_type tenv (ArrayT et bd) /\
  compatible_bound bd (LENGTH ss) /\ evaluate_type tenv et = SOME tv /\
  LENGTH ps = LENGTH ss /\
  LIST_REL (\(t,s) p. source_const_reify_certificate nominal tenv t s p)
    (ZIP (REPLICATE (LENGTH ss) et,ss)) ps ==>
  source_const_reify_certificate nominal tenv (ArrayT et bd) (SCV_List ss)
    (Builtin (ArrayT et bd) (MakeArray (SOME et) bd) (MAP FST ps),
     ArrayV (make_array_value tv bd (MAP SND ps)))
Proof
  strip_tac >>
  qspecl_then [`ss`,`REPLICATE (LENGTH ss) et`,`ps`] mp_tac source_const_certificates >>
  simp[] >> strip_tac >>
  simp[source_const_reify_certificate_def, expr_type_def] >> rpt conj_tac
  >- (rpt strip_tac >> simp[Once well_typed_expr_def,
        well_typed_builtin_app_def, builtin_operands_ok_def,
        EVERY_REPLICATE])
  >- (gvs[well_formed_type_def, IS_SOME_EXISTS] >>
      drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
      irule source_const_array_value_typed >> simp[] >>
      irule source_const_homogeneous_values >> goal_assum drule >>
      qexists_tac `LENGTH ss` >> simp[])
  >- (simp[source_const_structured_represents_def] >>
      qexistsl_tac [`tv`,`bd`,`MAP SND ps`] >> fs[LIST_REL_EL_EQN])
  >> rpt strip_tac >> irule source_const_eval_array >> simp[] >>
  rpt strip_tac >> irule source_const_eval_exprs >> simp[]
QED

Theorem source_const_reify_tuple_certificate:
  well_formed_type tenv (TupleT ts) /\ LENGTH ts = LENGTH ss /\
  LIST_REL (\(t,s) p. source_const_reify_certificate nominal tenv t s p)
    (ZIP (ts,ss)) ps ==>
  source_const_reify_certificate nominal tenv (TupleT ts) (SCV_Tuple ss)
    (Builtin (TupleT ts) (MakeArray NONE (Fixed (LENGTH ss))) (MAP FST ps),
     ArrayV (TupleV (MAP SND ps)))
Proof
  strip_tac >> drule_all source_const_certificates >> strip_tac >>
  simp[source_const_reify_certificate_def, expr_type_def] >> rpt conj_tac
  >- (rpt strip_tac >> simp[Once well_typed_expr_def,
        well_typed_builtin_app_def, builtin_operands_ok_def, compatible_bound_def])
  >- (irule source_const_tuple_value_typed >> simp[])
  >- fs[source_const_structured_represents_def, LIST_REL_EL_EQN]
  >> rpt strip_tac >> irule source_const_eval_tuple >> simp[] >>
  rpt strip_tac >> irule source_const_eval_exprs >> simp[]
QED

Theorem source_const_reify_struct_certificate:
  well_formed_type tenv (StructT sid) /\
  FLOOKUP nominal path = SOME sid /\
  FLOOKUP tenv sid = SOME (StructArgs args) /\
  MAP FST fields = MAP FST args /\ LENGTH (MAP SND args) = LENGTH (MAP SND fields) /\
  LIST_REL (\(t,s) p. source_const_reify_certificate nominal tenv t s p)
    (ZIP (MAP SND args,MAP SND fields)) ps ==>
  source_const_reify_certificate nominal tenv (StructT sid) (SCV_Struct path fields)
    (StructLit (StructT sid) sid (ZIP (MAP FST fields,MAP FST ps)),
     StructV (ZIP (MAP FST fields,MAP SND ps)))
Proof
  strip_tac >> drule_all source_const_certificates >> strip_tac >> gvs[] >>
  simp[source_const_reify_certificate_def, expr_type_def] >> rpt conj_tac
  >- (rpt strip_tac >> simp[Once well_typed_expr_def, GSYM MAP_MAP_o, MAP_ZIP] >>
      irule source_const_named_exprs_zip >> simp[])
  >- (irule source_const_struct_value_typed >> simp[] >> goal_assum drule)
  >- (simp[source_const_structured_represents_def] >>
      qexists_tac `MAP SND ps` >> fs[LIST_REL_EL_EQN])
  >> rpt strip_tac >> irule source_const_eval_struct >> simp[] >>
  rpt strip_tac >> irule source_const_eval_exprs >> simp[]
QED

Theorem source_const_reify_primitive_certificate:
  sourceConstValue$source_const_reify tenv ty sv = SOME e /\
  source_const_value_literal sv = SOME lit ==>
  source_const_reify_certificate nominal tenv ty sv (e,evaluate_literal lit)
Proof
  strip_tac >> drule sourceConstValuePropsTheory.source_const_reify_literal >>
  strip_tac >> gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  drule_all well_typed_literal_sound >> strip_tac >>
  Cases_on `sv` >>
  gvs[source_const_reify_certificate_def, source_const_structured_represents_def,
      source_const_value_literal_def, source_const_represents_def,
      well_formed_type_def, IS_SOME_EXISTS, well_typed_expr_def, expr_type_def,
      Once evaluate_def, return_def, evaluate_literal_def]
QED

Theorem source_const_reify_step_certificate:
  (!t s p. f t s = SOME p ==>
    source_const_reify_certificate nominal tenv t s p) /\
  source_const_reify_step f nominal tenv ty sv = SOME p ==>
  source_const_reify_certificate nominal tenv ty sv p
Proof
  strip_tac >> Cases_on `sv` >>
  gvs[source_const_reify_step_def, AllCaseEqs()] >>
  TRY (drule_all source_const_reify_primitive_certificate >> simp[] >> NO_TAC) >>
  drule_all source_const_reify_many_rel >> strip_tac >>
  FIRST [drule_all source_const_reify_list_certificate,
         drule_all source_const_reify_tuple_certificate,
         drule_all source_const_reify_struct_certificate] >> simp[]
QED

Theorem source_const_reify_fuel_certificate:
  !n nominal tenv ty sv p.
    source_const_reify_fuel n nominal tenv ty sv = SOME p ==>
    source_const_reify_certificate nominal tenv ty sv p
Proof
  Induct >> simp[Once source_const_reify_fuel_def] >>
  rpt gen_tac >> strip_tac >> irule source_const_reify_step_certificate >>
  qexists_tac `source_const_reify_fuel n nominal tenv` >> simp[]
QED

(* Runtime context agreement is essential: MakeArray evaluates its element
   type using get_tenv cx. No state invariant is needed and ALL state fields
   are preserved. The old primitive theorem remains context-free. *)
Theorem source_const_reify_correct:
  sourceConstValueStructured$source_const_reify nominal env.type_defs ty sv = SOME e ==>
  expr_type e = ty /\ well_typed_expr env e /\
  ?tv v. evaluate_type env.type_defs ty = SOME tv /\ value_has_type tv v /\
    source_const_structured_represents nominal sv v /\
    (!cx st. get_tenv cx = env.type_defs ==>
       eval_expr cx e st = (INL (Value v),st))
Proof
  simp[sourceConstValueStructuredTheory.source_const_reify_def, AllCaseEqs()] >>
  rpt strip_tac >> drule source_const_reify_fuel_certificate >>
  simp[source_const_reify_certificate_def] >> strip_tac >> gvs[] >>
  rename1 `source_const_structured_represents nominal sv (SND result)` >>
  qexists_tac `SND result` >> simp[]
QED

Theorem source_const_reify_sound:
  sourceConstValueStructured$source_const_reify nominal tenv ty sv = SOME e ==>
  ?tv v. evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    source_const_structured_represents nominal sv v /\
    (!cx st. get_tenv cx = tenv ==> eval_expr cx e st = (INL (Value v),st))
Proof
  simp[sourceConstValueStructuredTheory.source_const_reify_def, AllCaseEqs()] >>
  rpt strip_tac >> drule source_const_reify_fuel_certificate >>
  simp[source_const_reify_certificate_def] >> strip_tac >> gvs[] >>
  rename1 `source_const_structured_represents nominal sv (SND result)` >>
  qexists_tac `SND result` >> simp[]
QED

(* Primitive success embeds in the structured API. Its stronger, context-free
   certificate remains available to existing sourceExpr callers unchanged. *)
Theorem source_const_reify_primitive_agrees:
  sourceConstValue$source_const_reify tenv ty sv = SOME e ==>
  sourceConstValueStructured$source_const_reify nominal tenv ty sv = SOME e
Proof
  strip_tac >>
  drule sourceConstValuePropsTheory.source_const_reify_value_ok >> strip_tac >>
  drule sourceConstValuePropsTheory.source_const_reify_literal >> strip_tac >>
  Cases_on `sv` >> gvs[source_const_value_literal_def] >>
  simp[sourceConstValueStructuredTheory.source_const_reify_def,
       Once source_const_reify_fuel_def, source_const_reify_step_def,
       source_const_value_literal_def]
QED

Theorem source_const_reify_primitive_sound =
  sourceConstValuePropsTheory.source_const_reify_sound

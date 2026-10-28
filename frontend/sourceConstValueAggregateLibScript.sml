Theory sourceConstValueAggregateLib
Ancestors
  sourceConstValueStructured sourceConstValueProps vyperTypeValues
  vyperInterpreter vyperState vyperContext vyperAST vyperValue
  vyperValueOperation vyperTyping vyperTypeSystem sourceConstValueTypeMono
  vyperMisc list rich_list sorting option

Definition source_const_reify_certificate_def:
  source_const_reify_certificate nominal tenv ty sv p <=>
    expr_type (FST p) = ty /\
    (!env. env.type_defs = tenv ==> well_typed_expr env (FST p)) /\
    (?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv (SND p)) /\
    source_const_structured_represents nominal sv (SND p) /\
    (!cx st. get_tenv cx = tenv ==>
       eval_expr cx (FST p) st = (INL (Value (SND p)),st))
End

(* Small compositional interfaces, independent of reification recursion. *)
Theorem source_const_reify_many_rel:
  !ss ts ps f P.
    source_const_reify_many f ts ss = SOME ps /\
    (!t s p. f t s = SOME p ==> P t s p) ==>
    LIST_REL (\(t,s) p. P t s p) (ZIP (ts,ss)) ps /\
    LENGTH ts = LENGTH ss /\ LENGTH ps = LENGTH ss
Proof
  Induct >> Cases_on `ts` >>
  simp[source_const_reify_many_def, OPT_MMAP_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[source_const_reify_many_def] >> res_tac >> gvs[]
QED

Theorem source_const_certificates:
  !ss ts ps.
    LENGTH ts = LENGTH ss /\
    LIST_REL (\(t,s) p. source_const_reify_certificate nominal tenv t s p)
      (ZIP (ts,ss)) ps ==>
    MAP expr_type (MAP FST ps) = ts /\
    (!env. env.type_defs = tenv ==> well_typed_exprs env (MAP FST ps)) /\
    LIST_REL (source_const_structured_represents nominal) ss (MAP SND ps) /\
    LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
      ts (MAP SND ps) /\
    (!cx. get_tenv cx = tenv ==>
      EVERY (\p. !st. eval_expr cx (FST p) st = (INL (Value (SND p)),st)) ps) /\
    LENGTH ps = LENGTH ss
Proof
  Induct >> Cases_on `ts` >> Cases_on `ps` >>
  simp[source_const_reify_certificate_def, well_typed_expr_def] >>
  rpt strip_tac >> gvs[source_const_reify_certificate_def] >> res_tac >> gvs[]
QED

Theorem source_const_typed_values:
  !ts vs. LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\
    value_has_type tv v) ts vs ==>
    ?tvs. OPT_MMAP (evaluate_type tenv) ts = SOME tvs /\ values_have_types tvs vs
Proof
  Induct >> Cases_on `vs` >> simp[OPT_MMAP_def, value_has_type_def] >>
  rpt strip_tac >> res_tac >> simp[value_has_type_def]
QED

Theorem source_const_homogeneous_values:
  !n vs. LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\
    value_has_type tv v) (REPLICATE n et) vs /\
    evaluate_type tenv et = SOME tv ==> EVERY (value_has_type tv) vs
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac >> gvs[] >> res_tac
QED

Theorem source_const_tuple_value_typed:
  well_formed_type tenv (TupleT ts) /\
  LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
    ts vs ==>
  ?tv. evaluate_type tenv (TupleT ts) = SOME tv /\
       value_has_type tv (ArrayV (TupleV vs))
Proof
  strip_tac >> drule source_const_typed_values >> strip_tac >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type tenv (TupleT ts) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, evaluate_types_OPT_MMAP] >> strip_tac >> gvs[] >>
  simp[value_has_type_def]
QED

Theorem source_const_struct_zip_typed:
  !ks tvs vs. LENGTH ks = LENGTH tvs /\ values_have_types tvs vs ==>
    struct_has_type (ZIP (ks,tvs)) (ZIP (ks,vs))
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >> simp[value_has_type_def]
QED

Theorem source_const_struct_value_typed:
  well_formed_type tenv (StructT sid) /\
  FLOOKUP tenv sid = SOME (StructArgs args) /\
  LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v)
    (MAP SND args) vs ==>
  ?tv. evaluate_type tenv (StructT sid) = SOME tv /\
       value_has_type tv (StructV (ZIP (MAP FST args,vs)))
Proof
  strip_tac >> drule source_const_typed_values >> strip_tac >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type tenv (StructT sid) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule (CONJUNCT2 source_const_evaluate_type_mono) >> strip_tac >>
  gvs[evaluate_types_OPT_MMAP, value_has_type_def] >>
  irule source_const_struct_zip_typed >> simp[] >>
  gvs[OPT_MMAP_SOME_IFF]
QED

Theorem source_const_eval_exprs:
  !ps cx st.
    EVERY (\p. !st. eval_expr cx (FST p) st = (INL (Value (SND p)),st)) ps ==>
    eval_exprs cx (MAP FST ps) st = (INL (MAP SND ps),st)
Proof
  Induct >> simp[Once evaluate_def, return_def] >>
  Cases_on `h` >> rpt strip_tac >>
  simp[Once evaluate_def, bind_def, materialise_def, return_def]
QED

Theorem source_const_eval_array:
  (!st. eval_exprs cx es st = (INL vs,st)) /\
  compatible_bound bd (LENGTH es) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_expr cx (Builtin (ArrayT et bd) (MakeArray (SOME et) bd) es) st =
    (INL (Value (ArrayV (make_array_value tv bd vs))),st)
Proof
  strip_tac >> simp[Once evaluate_def, builtin_args_length_ok_def,
    type_check_def, assert_def, bind_def, ignore_bind_def, return_def,
    get_accounts_def, lift_sum_def, evaluate_builtin_def]
QED

Theorem source_const_eval_tuple:
  (!st. eval_exprs cx es st = (INL vs,st)) /\ LENGTH es = n ==>
  eval_expr cx (Builtin (TupleT ts) (MakeArray NONE (Fixed n)) es) st =
    (INL (Value (ArrayV (TupleV vs))),st)
Proof
  strip_tac >> simp[Once evaluate_def, builtin_args_length_ok_def,
    compatible_bound_def, type_check_def, assert_def, bind_def,
    ignore_bind_def, return_def, get_accounts_def, lift_sum_def,
    evaluate_builtin_def]
QED

Theorem source_const_named_exprs_zip:
  !ks es env. LENGTH ks = LENGTH es /\ well_typed_exprs env es ==>
    well_typed_named_exprs env (ZIP (ks,es))
Proof
  Induct >> Cases_on `es` >> simp[well_typed_expr_def]
QED

Theorem source_const_eval_struct:
  LENGTH ks = LENGTH es /\ (!st. eval_exprs cx es st = (INL vs,st)) ==>
  eval_expr cx (StructLit (StructT sid) sid (ZIP (ks,es))) st =
    (INL (Value (StructV (ZIP (ks,vs)))),st)
Proof
  Cases_on `sid` >> strip_tac >>
  simp[Once evaluate_def, MAP_ZIP, bind_def, return_def]
QED

Theorem source_const_enumerate_sorted:
  !vs d n. SORTED $< (MAP FST (enumerate_static_array d n vs))
Proof
  Induct >> simp[enumerate_static_array_def, LET_THM] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  assume_tac arithmeticTheory.transitive_LESS >>
  simp[SORTED_EQ] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  rename1 `MEM kv (enumerate_static_array _ _ _)` >>
  Cases_on `kv` >> gvs[MEM_enumerate_static_array_iff]
QED

Theorem source_const_array_value_typed:
  compatible_bound bd (LENGTH vs) /\ EVERY (value_has_type tv) vs ==>
  value_has_type (ArrayTV tv bd) (ArrayV (make_array_value tv bd vs))
Proof
  Cases_on `bd` >> simp[compatible_bound_def, make_array_value_def,
    value_has_type_def, all_have_type_EVERY] >> strip_tac >> conj_tac
  >- simp[source_const_enumerate_sorted] >>
  irule sparse_has_type_enumerate >> simp[]
QED

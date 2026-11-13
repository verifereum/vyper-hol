Theory bodyPtrBopInSourceTyping
Ancestors bodyPtrBopInEncoding exprSimSource exprSimHypsDefs
  vyperTypeSystem vyperTyping vyperValue compileEnv entryDecodeStaticProps list

Theorem membership_source_array_type:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\
  expr_type e2 = ArrayT et bd ==>
  expr_type e1 = et /\ ann = BaseT BoolT
Proof
  Cases_on `bop` >> simp[] >>
  simp[expr_body_pre_def, well_typed_expr_def,
       well_typed_builtin_app_def, well_typed_binop_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem membership_evaluated_word_bounds:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256) /\
  (!m. tv = BaseTV (IntT m) ==> 0 < m) /\
  (!m. tv = BaseTV (BytesT (Fixed m)) ==> m <= 32)
Proof
  strip_tac >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed] >>
  Cases_on `ty` >> gvs[is_word_type_def]
  >~ [`FlagT`]
  >- (gvs[evaluate_type_def, AllCaseEqs(), well_formed_type_value_def]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_word_type_def, evaluate_type_def, well_formed_type_value_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem membership_source_common_type:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT et bd /\
  eval_expr cx e1 es = (INL r1,es1) /\
  read_result cx r1 es1 = (INL v1,es1) /\
  eval_expr cx e2 es1 = (INL r2,es2) /\
  read_result cx r2 es2 = (INL v2,es2) ==>
  ?tv. evaluate_type (get_tenv cx) et = SOME tv /\
       value_has_type tv v1 /\
       value_has_type (ArrayTV tv bd) v2 /\
       expr_type e1 = et /\ is_word_type et /\
       (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
            m <= 256) /\
       (!m. tv = BaseTV (IntT m) ==> 0 < m) /\
       (!m. tv = BaseTV (BytesT (Fixed m)) ==> m <= 32)
Proof
  strip_tac >> drule membership_source_array_type >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- gvs[expr_body_pre_def] >>
     qexistsl_tac [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `expr_sim_inv cenv cx env es1` by
    (drule_all expr_body_pre_eval_result >> simp[]) >>
  `expr_body_pre cenv cx env e2 es1` by
    (irule expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     qexistsl_tac [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) et = SOME tv /\
        value_has_type tv v1 /\ value_has_type (ArrayTV tv bd) v2` by
    (gvs[evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  qexists_tac `tv` >> gvs[] >>
  drule_all membership_evaluated_word_bounds >> simp[]
QED

(* Consumer-side typing covers both dense elements and sparse defaults.
   No equality premise about the needle and element types is left over. *)
Theorem membership_array_encoding_reflects:
  is_word_type et /\ evaluate_type tenv et = SOME tv /\
  value_has_type tv needle /\ value_has_type (ArrayTV tv bd) arr ==>
  (!vs i. arr = ArrayV (DynArrayV vs) /\ i < LENGTH vs ==>
     (typed_val_to_w256 tv needle = typed_val_to_w256 tv (EL i vs) <=>
      needle = EL i vs)) /\
  (!kvs cap i. arr = ArrayV (SArrayV kvs) /\ bd = Fixed cap /\ i < cap ==>
     (typed_val_to_w256 tv needle =
        typed_val_to_w256 tv (sparse_val tv kvs i) <=>
      needle = sparse_val tv kvs i))
Proof
  strip_tac >>
  drule_all membership_evaluated_word_bounds >> strip_tac >>
  conj_tac >> rpt strip_tac
  >- (`value_has_type tv (EL i vs)` by
        (Cases_on `bd` >>
         gvs[value_has_type_def, all_have_type_EVERY, EVERY_EL]) >>
      irule membership_typed_word_encoding_reflects >> metis_tac[]) >>
  `value_has_type tv (sparse_val tv kvs i)` by
    (irule sparse_val_has_type >>
     gvs[value_has_type_def] >> metis_tac[]) >>
  irule membership_typed_word_encoding_reflects >> metis_tac[]
QED

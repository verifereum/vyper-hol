(* Source boundaries for live local tuple roots. Historical values are not assumed. *)
Theory bodyPtrSubscriptTupleSource
Ancestors
  bodyPtrSubscriptTupleDispatch bodyPtrSubscriptTupleLayout exprSimTuple
  exprSimHypsDefs exprSimDefs vyperState vyperInterpreter vyperValue
  vyperValueOperation vyperTyping loweringPosts vyperAST

Theorem memory_root_select:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value [sel] = INL child ==>
  select_result cx ty (PlaceR (MemoryPlace id [])) sel es =
    (INL (PlaceR (MemoryPlace id [sel])),es)
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, lift_option_type_def, bind_def,
       return_def, subscripts_type_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, ignore_bind_def, extend_memory_place_def]
QED

Theorem named_tuple_source:
  expr_body_pre cenv cx env (Subscript ann (Name (TupleT tys) id) idx) es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME entry.type /\
  value_has_type entry.type entry.value ==>
  ?ity k child ctv.
    idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann /\
    evaluate_type (get_tenv cx) ann = SOME ctv /\ value_has_type ctv child /\
    evaluate_subscripts entry.type entry.value [ValueSubscript (IntV (&k))] = INL child /\
    select_result cx (TupleT tys) (PlaceR (MemoryPlace id []))
      (ValueSubscript (IntV (&k))) es =
      (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV (&k))])),es) /\
    eval_expr cx (Subscript ann (Name (TupleT tys) id) idx) es =
      (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV (&k))])),es) /\
    read_result cx (PlaceR (MemoryPlace id [ValueSubscript (IntV (&k))])) es =
      (INL child,es)
Proof
  strip_tac >> drule tuple_subscript_pre >> simp[expr_type_def] >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all typed_tuple_child_layout >> strip_tac >>
  drule_all memory_root_select >> strip_tac >>
  qexistsl_tac [`ity`, `k`, `child`, `ctv`] >> gvs[] >>
  conj_tac
  >- (simp[tuple_subscript_source, Once evaluate_def, bind_def,
           get_scopes_def, return_def, type_check_def, assert_def, check_def,
           ignore_bind_def, expr_type_def]) >>
  (* The selected current path succeeds, so read_memory_path takes its INL
     branch before consulting history. No absence of history is inferred. *)
  simp[read_result_def, read_place_def, get_scopes_def, lift_option_type_def,
       bind_def, return_def, lift_sum_def, read_memory_path_def]
QED

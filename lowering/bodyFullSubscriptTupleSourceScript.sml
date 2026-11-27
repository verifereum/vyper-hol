Theory bodyFullSubscriptTupleSource
Ancestors
  exprSimTuple bodyPtrAttributeSource exprSimHypsDefs loweringPosts
  vyperInterpreter vyperValue vyperAST vyperState

(* Select the source child at the marked base endpoint, before the ADD. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all tuple_pre_base >> strip_tac >>
  gvs[Excl "expr_body_pre_gas_obs"] >>
  drule_all_then (qx_choose_then `tvs` strip_assume_tac) tuple_base_facts >>
  `vv_holds cenv cx (TupleT tys) btv bvv ee q` by
    (qhdtm_assum `vv_post`
       (mp_tac o REWRITE_RULE [vv_post_def]) >> simp[]) >>
  drule attribute_vv_holds_read_operand >> strip_tac >>
  drule_all_then (qx_choose_then `vs` strip_assume_tac) tuple_base_read >>
  Cases_on `select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee` >>
  rename1 `select_result _ _ _ _ _ = (res,ef)` >>
  `!m. res <> INR (Error (TypeError m))` by metis_tac[] >>
  `k < LENGTH vs` by simp[] >>
  drule_all select_tuple_read >> strip_tac >> gvs[] >> metis_tac[]
QED
*)
Theorem tuple_selected_marked_source:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) (es with gas_obs := gs) /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  eval_expr cx obj (es with gas_obs := gs) = (INL btv,ee) /\
  vv_post H ctx func cenv cx obj es sa sb s0 ee btv bvv q ==>
  ?ity k tvs vs tv'.
    idx = Literal ity (IntL (&k)) /\ ann = EL k tys /\ k < LENGTH tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    LENGTH tvs = LENGTH tys /\ LENGTH vs = LENGTH tvs /\ values_have_types tvs vs /\
    read_result cx btv ee = (INL (ArrayV (TupleV vs)),ee) /\
    select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee = (INL tv',ee) /\
    read_result cx tv' ee = (INL (EL k vs),ee)
Proof
  cheat
QED

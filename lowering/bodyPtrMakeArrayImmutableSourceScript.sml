(* Source semantics projected before allocation: the runtime state is unchanged. *)
Theory bodyPtrMakeArrayImmutableSource
Ancestors
  bodyPtrMakeArrayConsumerPost exprSimCopy loweringPosts vyperTypeValues
  vyperStorageBackend vyperState context compileEnv

Theorem make_array_immutable_consumer_read:
  vv_post ctx func cenv cx e es sa sb s0 es' raw (LocatedValue ty p) s /\
  p.ptr_location = LocCode ==>
  ?a tv v.
    ty = expr_type e /\
    eval_operand p.ptr_operand s = SOME a /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    well_formed_type_value tv /\
    read_result cx raw es' = (INL v,es') /\
    immutable_holds cenv cx ty (Value v) a es' s /\
    val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)
Proof
  simp[vv_post_def, vv_holds_def] >> rpt strip_tac >>
  `?tv v. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
     read_result cx raw es' = (INL v,es') /\
     immutable_holds cenv cx (expr_type e) (Value v) w es' s` by
    (fs[immutable_holds_def] >>
     goal_assum (drule_at Any) >> simp[immutable_holds_def] >>
     qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >>
     simp[read_result_def, return_def]) >>
  drule_all immutable_holds_bounds >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

(* Joint positional operands: representation adapters and CPS composition. *)
Theory bodyFullExtCallRequestPositional
Ancestors
  bodyFullExtCallRequestSnapshotMemory bodyFullExtCallRequestRetag
  bodyFullExtCallRequestSnapshotWord compileEnv
  exprSimSource exprSimHyps exprSimHypsDefs vyperTypeInvariants vyperTypeExprSoundness
  bodyPtrDefs loweringPosts exprLowering supportedExprTraverse vyperState

(* Discharge both typing premises at the immediate source read. *)
Theorem extcall_snapshot_located_retag:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  ~expr_has_effect e /\ ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e sa = (LocatedValue tag p,sm) /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (post_value_type ce e) raw (LocatedValue tag p) ee s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue tag p) ee G tn s ==>
  vv_holds ce cx (lowered_value_type ce e) raw
    (ext_call_arg_value (lowered_value_type ce e) (LocatedValue tag p)) ee s /\
  ptr_vv_ok cx (lowered_value_type ce e) raw
    (ext_call_arg_value (lowered_value_type ce e) (LocatedValue tag p)) ee G tn s
Proof
  strip_tac >> Cases_on `p.ptr_location = LocMemory`
  >- (`post_value_type ce e = expr_type e` by
        (irule post_value_type_not_int_call >> rpt strip_tac >>
         gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def]) >>
      `value_runtime_typed env (lowered_value_type ce e) v` by
        (irule memory_rhs_read_lowered_typed_unwidened >>
         qexistsl [`cx`, `es`, `ee`] >> simp[bind_def]) >>
      `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
      `env.type_defs = get_tenv cx` by
        gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      `?dv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dv /\
            value_has_type dv v` by gvs[value_runtime_typed_def] >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >>
      simp[ext_call_arg_value_def] >>
      irule extcall_request_memory_retag >> metis_tac[]) >>
  irule extcall_nonmemory_retag >> metis_tac[]
QED

(* The word branch can consume expr_sim_full, without repeating unwrap. *)
Theorem extcall_snapshot_word_lower_value:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  vv_holds ce cx (post_value_type ce e) tv vv ee s /\
  is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) /\
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv)
    sm = (sv,sb) ==>
  ?op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
       sv = StackValue (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) op
Proof
  strip_tac >> drule_all extcall_request_word_snapshot_unwrap >> strip_tac >>
  gvs[lower_value_def, comp_bind_def, comp_return_def] >>
  Cases_on `unwrap_value ce vv sm` >> gvs[]
QED

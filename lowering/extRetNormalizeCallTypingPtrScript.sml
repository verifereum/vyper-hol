Theory extRetNormalizeCallTypingPtr
Ancestors
  extRetInternalCallTypingPtr memoryLocalRhsProps exprSimHypsDefs
  vyperAST vyperInterpreter vyperTyping vyperTypeInvariants
  vyperTypeCallGraph vyperTypeSystem finite_map
Libs
  monadsyntax

(* Reuse ext_ret_internal_call_read_signature_typed for signature typing.
   Return supplies its typing and call-safety guards through
   type_stmt_return_some_iff and int_calls_stmt_def. This boundary only
   evaluates the signature layout; it does not establish a counted copy.
   extRetSemanticEntryPtr separately exports the Return-post and aggregate
   lowered-layout interfaces for normalization consumers. *)
Theorem normalize_internal_call_signature_layout:
  !ce cx env es ann id args drv sig v es'.
    expr_sim_inv ce cx env es /\
    well_typed_expr env (Call ann (IntCall id) args drv) /\
    call_evaluation_safe cx (int_calls_expr (Call ann (IntCall id) args drv)) /\
    FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v,es') ==>
    ?tv. evaluate_type (get_tenv cx) sig.ret_ty = SOME tv /\
         value_has_type tv v
Proof
  rpt strip_tac >>
  drule_all ext_ret_internal_call_read_signature_typed >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> metis_tac[]
QED

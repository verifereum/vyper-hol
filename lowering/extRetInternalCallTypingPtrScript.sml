Theory extRetInternalCallTypingPtr
Ancestors
  bodyPtrIfExpEndpointTyping exprSimHypsDefs exprSimDefs
  vyperAST vyperInterpreter vyperTyping vyperTypeInvariants
  vyperTypeCallGraph vyperTypeEvalSoundness vyperTypeSystem finite_map
Libs
  monadsyntax

(* Actual Return guards suffice: no supported-expression/body precondition. *)
Theorem ext_ret_internal_call_read_signature_typed:
  !cenv cx env es ann id args drv sig v es'.
    expr_sim_inv cenv cx env es /\
    well_typed_expr env (Call ann (IntCall id) args drv) /\
    call_evaluation_safe cx (int_calls_expr (Call ann (IntCall id) args drv)) /\
    FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env sig.ret_ty v
Proof
  rpt strip_tac >>
  `well_formed_type env.type_defs sig.ret_ty` by
    (drule_all ifexp_frame_signature_return_well_formed >> simp[]) >>
  `well_typed_expr env (Call sig.ret_ty (IntCall id) args drv)` by
    (Cases_on `id` >>
     gvs[well_typed_expr_def, type_widens_to_def] >> metis_tac[]) >>
  `(do r <- eval_expr cx (Call sig.ret_ty (IntCall id) args drv);
       read_result cx r od) es = (INL v, es')` by
    metis_tac[ifexp_internal_call_annotation_eval] >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_sim_inv_def, int_calls_expr_def, expr_type_def]
QED

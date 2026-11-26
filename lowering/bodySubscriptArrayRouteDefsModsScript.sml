(* Shared premises and route guards for linked value-array subscripts. *)
Theory bodySubscriptArrayRouteDefsMods
Ancestors
  bodyFullPredsMods exprSimMapDefs compileEnv exprLowering
  vyperInterpreter vyperState vyperAST vyperTypeSystem

(* Execution parameters absent from the premises are carried through so
   each route can use the same argument list as the exact interface. *)
Definition linked_subscript_array_context_mods_def:
  linked_subscript_array_context_mods mods exps cx ann obj idx
      DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bnd <=>
    (!s'' res t s3 res' t'.
       eval_expr cx obj s'' = (INL res,t) /\
       (if subscript_reads_base cx obj idx then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_full_ok_mods mods exps cx idx) /\
    body_expr_full_ok_mods mods exps cx obj /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = ArrayT et bnd /\
    place_type cenv obj = ValPT (ArrayT et bnd) /\
    post_value_type cenv obj = expr_type obj
End

Definition subscript_array_framed_code_case_mods_def:
  subscript_array_framed_code_case_mods cenv cx obj idx (bnd:bound) <=>
    (!t r t'. eval_expr cx idx t = (INL r,t') ==>
               t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
    (!s tr slot vt t.
       eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
    ~cenv.ce_is_ctor /\
    (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode)
End

Definition subscript_array_framed_memory_case_mods_def:
  subscript_array_framed_memory_case_mods cenv cx obj idx et bnd <=>
    (!t r t'. eval_expr cx idx t = (INL r,t') ==>
               t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
    (!s tr slot vt t.
       eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
    (?n. bnd = vyperAST$Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory)
End

Definition subscript_array_unframed_case_mods_def:
  subscript_array_unframed_case_mods cenv cx obj idx et bnd <=>
    ~(subscript_array_framed_code_case_mods cenv cx obj idx bnd \/
      subscript_array_framed_memory_case_mods cenv cx obj idx et bnd)
End

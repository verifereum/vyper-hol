Theory bodyMemSubscriptArrayFramed
Ancestors
  bodyMemSubscriptArrayFramedCompose bodyMemSubscriptArraySuffixMemory

Theorem compile_subscript_array_framed_base_mem_case:
  !ctx func cenv cx ann obj idx et bd.
    (!env ty es. expr_body_pre cenv cx env obj es ==>
                 expr_vv_sim_mem ctx func cenv cx ty obj es) /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              !env ty es. expr_body_pre cenv cx env idx es ==>
                          expr_sim_mem ctx func cenv cx ty idx es) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    post_value_type cenv obj = expr_type obj /\
    ((!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) ==>
    !env ty es. expr_body_pre cenv cx env (Subscript ann obj idx) es ==>
                expr_vv_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  match_mp_tac compile_subscript_array_framed_base_mem_case_from_suffix >>
  rpt gen_tac >>
  MATCH_ACCEPT_TAC framed_array_represented_suffix_summary_mem
QED

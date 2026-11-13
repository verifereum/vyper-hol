(* Complementary framed and place-base counted array selection. *)
Theory bodyMemSubscriptArray
Ancestors
  bodyMemSubscriptArrayFramed bodyMemSubscriptArrayPlaceBase bodyMemoryPreds

Theorem body_subscript_array_vv_mem:
  body_expr_mem_ok cx obj /\
  (!s tv t. eval_expr cx obj s = (INL tv,t) ==> body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
  post_value_type cenv obj = expr_type obj ==>
  expr_vv_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  rpt strip_tac >>
  `!env ty es. expr_body_pre cenv cx env obj es ==>
               expr_vv_sim_mem ctx func cenv cx ty obj es` by
    metis_tac[body_expr_mem_ok_def] >>
  `!s tv t. eval_expr cx obj s = (INL tv,t) ==>
            !env ty es. expr_body_pre cenv cx env idx es ==>
                        expr_sim_mem ctx func cenv cx ty idx es` by
    metis_tac[body_expr_mem_ok_def] >>
  Cases_on `(!t r t'. eval_expr cx idx t = (INL r,t') ==>
                        t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
            (!s tr slot vt t. eval_expr cx obj s <>
                (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
            ((~cenv.ce_is_ctor /\
              !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
             ((?n. bd = Fixed n) /\
              (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
              !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))`
  >- (irule compile_subscript_array_framed_base_mem_case >>
      simp[] >> metis_tac[]) >>
  irule compile_subscript_array_place_base_mem_case >>
  simp[] >> metis_tac[]
QED

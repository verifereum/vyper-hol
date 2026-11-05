(* Memory judgments of struct and array literals whose elements the lowering
   lays out at their own types: the main halves of bodyMemStructLit's and
   bodyMemMakeArray's cases, the memory twins of exprSimAggregates'
   compile_struct_lit_vv_case and compile_make_array_vv_case.  An element
   that is an internal call whose return type the call's type widens is the
   other half (bodyMemStructLitWidened, bodyMemMakeArrayWidened). *)
Theory bodyMemAggregate
Ancestors
  bodyMemoryPreds

Theorem body_structlit_nowiden_mem:
  !cx v7 src_id_opt id kes tops ctx func cenv env ty es.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
    (!e. MEM e (MAP SND kes) ==>
         int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
    expr_vv_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  cheat
QED

Theorem body_make_array_nowiden_mem:
  !cx ty t n es tops ctx func cenv env ty' st.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
    (!e. MEM e es ==>
         int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
    expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  cheat
QED

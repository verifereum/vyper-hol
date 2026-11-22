(* Request-prefix companion to bodyFullSubscriptArrayMemory. *)
Theory s1PrefixSubscriptArrayMemory
Ancestors
  s1PrefixPreds bodyFullSubscriptArrayMemory s1PrefixDefs

Theorem subscript_array_framed_memory_prefix:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et n.
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_prefix_ok cx e2) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  ~subscript_reads_base cx e1 e2 /\
  ~copies_subscript_base cenv e1 e2 /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et (Fixed n) /\
  place_type cenv e1 = ValPT (ArrayT et (Fixed n)) /\
  post_value_type cenv e1 = expr_type e1 /\
  (!t r t'. eval_expr cx e2 t = (INL r,t') ==>
      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!s tr slot vt t.
      eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
  (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
  (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  cheat
QED

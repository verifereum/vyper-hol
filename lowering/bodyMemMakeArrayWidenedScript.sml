(* Memory-safe MakeArray with physically widened internal-call elements.
   The shared assembly stores each child at its physical post-value type. *)
Theory bodyMemMakeArrayWidened
Ancestors
  bodyMemMakeArrayAssembly

Theorem body_make_array_widened_call_elem_mem:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) ==>
    !tops ctx func cenv env ty' st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
      (?e. MEM e es /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
      expr_vv_sim_mem ctx func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  metis_tac[body_make_array_sim_mem]
QED

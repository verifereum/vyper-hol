(* Memory case of the body induction, array literal (bodyMemMakeArray's
   dispatch): an element that is an internal call whose return type the
   call's type widens.  HELD with S1's body_make_array_widened_call_elem
   (bodySimMakeArrayWidened), which waits for the posts interface to
   describe a widened call's value at its lowered type. *)
Theory bodyMemMakeArrayWidened
Ancestors
  bodyMemoryPreds typedCopyControlPathMem typedCopyPrimitivePathMem typedCopyArrayEntryPathMem typedCopySarrayPathMem typedCopyDynarrayPathMem typedCopyArraySemanticPathMem typedCopyFieldStepMem

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
  cheat
QED

(* Memory case of the body induction, struct literal (bodyMemStructLit's
   dispatch): an element that is an internal call whose return type the
   call's type widens.  HELD with S1's body_struct_lit_widened_call_elem
   (bodySimStructLitWidened), which waits for the posts interface to
   describe a widened call's value at its lowered type. *)
Theory bodyMemStructLitWidened
Ancestors
  bodyMemoryPreds typedCopyRankMemory

Theorem body_struct_lit_widened_call_elem_mem:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      (?e. MEM e (MAP SND kes) /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  cheat
QED

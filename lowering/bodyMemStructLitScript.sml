(* Memory case of the body induction (bodyMemory's body_mem_mutual): struct
   literal.  As S1's body_structlit_case: bodyMemAggregate's
   body_structlit_nowiden_mem when no element is a widened internal call,
   bodyMemStructLitWidened otherwise. *)
Theory bodyMemStructLit
Ancestors
  bodyMemoryPreds bodyMemAggregate bodyMemStructLitWidened

Theorem body_structlit_mem_case:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) ==>
    body_expr_mem_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  rpt strip_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >> rpt gen_tac >>
  strip_tac >>
  Cases_on `!e. MEM e (MAP SND kes) ==>
              int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`
  >- (irule body_structlit_nowiden_mem >> metis_tac[]) >>
  irule body_struct_lit_widened_call_elem_mem >> metis_tac[]
QED

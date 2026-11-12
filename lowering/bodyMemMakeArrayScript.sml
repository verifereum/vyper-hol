(* Memory case of the body induction (bodyMemory's body_mem_mutual): array
   literal.  As S1's body_make_array_case: bodyMemAggregate's
   body_make_array_nowiden_mem when no element is a widened internal call,
   bodyMemMakeArrayWidened otherwise. *)
Theory bodyMemMakeArray
Ancestors
  bodyMemoryPreds bodyMemAggregate bodyMemMakeArrayWidened

Theorem body_make_array_mem_case:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (MakeArray t n) es)
Proof
  rpt strip_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >> rpt gen_tac >>
  strip_tac >>
  Cases_on `!e. MEM e es ==>
              int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e`
  >- (irule body_make_array_nowiden_mem >> metis_tac[]) >>
  irule body_make_array_widened_call_elem_mem >> metis_tac[]
QED

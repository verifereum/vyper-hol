(* Memory case of the body induction (bodyMemory's body_mem_mutual): for loop.
   The same split as S1's body_for_case: a range of two literals, a computed
   range, and an array, each in its own bodyMemFor* leaf. *)
Theory bodyMemFor
Ancestors
  bodyMemoryPreds bodyMemForRangeLit bodyMemForRange bodyMemForArray

Theorem body_for_mem_case:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_mem_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_mem_ok cx it) ==>
    body_stmt_mem_ok cx (For id typ it n body)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?a1 n1 a2 n2. it = Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))`
  >- (drule_all body_for_range_lit_mem >> simp[]) >>
  Cases_on `it`
  >- (irule body_for_array_mem >> simp[] >> metis_tac[]) >>
  irule body_for_range_mem >> simp[] >> metis_tac[]
QED

Theory boolChainOperandsGuarded
Ancestors
  exprLowering vyperAST

(* On a recognized chain node, only the head's guard is needed to
   carry the list judgment into the selected arm. *)
Theorem bool_chain_operands_guarded:
  (!e. P e ==> Q [e]) /\
  (!t c a b. P (IfExp t c a b) ==> P c /\ (G c ==> P a /\ P b)) /\
  (!c es. P c /\ (G c ==> Q es) ==> Q (c::es)) ==>
  !k e. P e ==> Q (bool_chain_operands d k e)
Proof
  strip_tac >> Induct
  >- simp[bool_chain_operands_def]
  >> gen_tac >> strip_tac >> Cases_on `e` >> simp[bool_chain_operands_def]
  >> Cases_on `d` >> gs[] >> IF_CASES_TAC >> simp[]
  >> first_x_assum irule >> metis_tac[]
QED

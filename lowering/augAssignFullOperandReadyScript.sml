Theory augAssignFullOperandReady
Ancestors
  stmtSimAugAssignPlace
Libs
  monadsyntax

(* The actual RHS type is supplied by the full RHS postcondition.  Statement
   typing alone does not type a value read in an arbitrary source state. *)
Theorem augassign_joint_operand_ready:
  type_stmt env ret_ty (AugAssign ty target bop e) = SOME env' /\
  (do raw <- eval_expr cx e; read_result cx raw od) st = (INL rhs,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs /\
  value_has_type tvrhs rhs ==>
  well_typed_binop ty bop ty (expr_type e) /\
  bop <> In /\ bop <> NotIn /\
  (bop = Exp ==>
    (?n. (if bop = Exp then expr_int_literal e else NONE) = SOME n /\
         0 <= n) /\
    (!n. (if bop = Exp then expr_int_literal e else NONE) = SOME n ==>
         rhs = IntV n)) /\
  (bop = ShL \/ bop = ShR ==>
    (?i. rhs = IntV i /\ 0 <= i) \/
    (ty = BaseT (BytesT (Fixed 32)) /\
     ?bs. rhs = BytesV bs /\ LENGTH bs = 32))
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  drule exprSimSourceTheory.eval_expr_read_INL >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[exprSimHypsTheory.eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==>
      (?i. rhs = IntV i /\ 0 <= i) \/
      (ty = BaseT (BytesT (Fixed 32)) /\
       ?bs. rhs = BytesV bs /\ LENGTH bs = 32))` by
    metis_tac[stmtSimAugAssignTheory.augassign_shift_operand] >>
  `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
    (strip_tac >>
     gvs[vyperTypeSystemTheory.nonneg_int_literal_def,
         GSYM exprSimHypsTheory.expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  Cases_on `bop = Exp` >> gvs[] >> first_assum ACCEPT_TAC
QED

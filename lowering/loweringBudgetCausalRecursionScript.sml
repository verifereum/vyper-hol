Theory loweringBudgetCausalRecursion
Ancestors
  bodyFullPreds loweringCallBudgetHistory sourceCallCountWitness
Libs
  loweringBudgetCausalSyntaxLib

Theorem causal_fold_zip[local]:
  !xs f g z.
    FOLDR (\p acc. g (FST p) (SND p) acc) z (ZIP (xs,MAP f xs)) =
    FOLDR (\e acc. g e (f e) acc) z xs
Proof
  Induct >> simp[]
QED

(* The datatype axiom has one algebra for each expression/base constructor.
   Its original child syntax is needed by the short-circuit guards. *)
Theorem causal_expr_base_recursion[local]:
  !N L R J. ?E B.
    (!e. E e = (N e /\
      (!a t n es. e = Builtin a (MakeArray t n) es /\ L t n (LENGTH es) ==>
        FOLDR (\e acc. E e /\ (R e ==> acc)) T es))) /\
    (!id. B (NameTarget id) = T) /\
    (!nid. B (TopLevelNameTarget nid) = T) /\
    (!t id. B (AttributeTarget t id) = B t) /\
    (!t e. B (SubscriptTarget t e) = (B t /\ (J t ==> E e)))
Proof
  rpt gen_tac >>
  qspecl_then [
    `\a b. N (Name a b)`,
    `\a b. N (TopLevelName a b)`,
    `\a b c. N (FlagMember a b c)`,
    `\a b c d eb ec ed. N (IfExp a b c d)`,
    `\a b. N (Literal a b)`,
    `\a b c ec. N (StructLit a b c)`,
    `\a b c eb ec. N (Subscript a b c)`,
    `\a c b eb. N (Attribute a b c)`,
    `\a b es bs. N (Builtin a b es) /\
      (!t n. b = MakeArray t n /\ L t n (LENGTH es) ==>
        FOLDR (\p acc. SND p /\ (R (FST p) ==> acc)) T (ZIP (es,bs)))`,
    `\a b c es bs. N (TypeBuiltin a b c es)`,
    `\a b eb. N (Pop a b)`,
    `\a b c d ec ed. N (Call a b c d)`,
    `\a. T`, `\a. T`,
    `\t e bt be. bt /\ (J t ==> be)`,
    `\id t bt. bt`
  ] mp_tac vyperASTTheory.expr_Axiom >>
  strip_tac >> qexistsl [`h0`,`h1`] >>
  conj_tac
  >- (gen_tac >> Cases_on `e` >> simp[causal_fold_zip]) >>
  simp[]
QED

Theorem causal_expr_base_exists:
  ^expr_base_exists_tm
Proof
  gen_tac >>
  qspecl_then [`^expr_nonrecursive cx`,
    `\t n len. builtin_args_length_ok (MakeArray t n) len`,
    `\e. ?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
       read_result cx tv s1 = (INL v,t1)`,
    `\t. ?s pv s1. eval_base_place cx t s = (INL pv,s1)`]
    mp_tac causal_expr_base_recursion >>
  strip_tac >> qexists_tac `(E,B)` >>
  pure_rewrite_tac [pairTheory.FST,pairTheory.SND] >>
  conj_tac
  >- (gen_tac >> qpat_x_assum `!e. E e = _` (qspec_then `e` mp_tac) >>
      BETA_TAC >> tautLib.TAUT_TAC) >>
  simp[]
QED

Theorem causal_expr_base_equations:
  ^expr_base_equations_tm
Proof
  gen_tac >> SELECT_ELIM_TAC >> simp[causal_expr_base_exists]
QED

Theorem causal_tuple_recursion[local]:
  !B J. ?tf.
    (!t v. tf (BaseTarget t) v = B t) /\
    (!gs v. tf (TupleTarget gs) v =
      (!vs. v = ArrayV (TupleV vs) ==>
        FOLDR (\g k vs. case vs of [] => T | x::xs =>
          tf g x /\ (J g x ==> k xs)) (\vs. T) gs vs))
Proof
  rpt gen_tac >>
  qspecl_then [`\t v. B t`,
    `\gs fs v. !vs. v = ArrayV (TupleV vs) ==>
      FOLDR (\p k vs. case vs of [] => T | x::xs =>
        SND p x /\ (J (FST p) x ==> k xs)) (\vs. T) (ZIP (gs,fs)) vs`]
    mp_tac vyperASTTheory.assignment_target_Axiom >>
  strip_tac >> qexists_tac `h` >> simp[causal_fold_zip]
QED

Theorem causal_tuple_exists:
  ^tuple_exists_tm
Proof
  gen_tac >>
  qspecl_then [`^B_base cx`,
    `\g v. ?s x t. assign_tuple_targets cx g v s = (INL x,t)`]
    mp_tac causal_tuple_recursion >>
  strip_tac >> qexists_tac `tf` >> simp[]
QED

Theorem causal_tuple_equations:
  ^tuple_equations_tm
Proof
  gen_tac >> SELECT_ELIM_TAC >> simp[causal_tuple_exists]
QED

Theorem causal_list_equations:
  ^list_equations_tm
Proof
  simp[]
QED

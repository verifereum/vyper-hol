(* Memory case of the body induction: the binary operators bodyMemBop and
   bodyMemBopHeld leave, which typing narrows to in and not in with a word
   needle on an array that is not a literal.  The memory twin of S1's
   exprSimBopRestWord (compile_bop_rest_word_case). *)
Theory bodyMemBopRestWord
Ancestors
  bodyMemoryPreds compileEnv bodyMemBopRestWordSim exprSimBopRestWordFacts
  exprSimMemoryStack exprSimOperators exprSimHyps exprSimHypsDefs exprLoweringProps

Theorem body_bop_rest_word_mem:
  !cx ty bop e1 e2.
    ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
    ~((bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_binop ty bop (expr_type e1) (expr_type e2)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.well_typed_builtin_app_def]) >>
  drule_all rest_word_typed_membership >> strip_tac >>
  (conj_asm1_tac
   >- (irule compile_rest_word_membership_sim_mem >> metis_tac[])) >>
  `is_word_type ty` by
    gvs[vyperTypeSystemTheory.well_typed_binop_def, is_word_type_def] >>
  irule body_expr_vv_sim_mem_stack_word >> simp[compile_bop_stack] >>
  rpt conj_tac
  >>~- ([`Value`], metis_tac[eval_expr_builtin_value]) >>
  fs[vyperASTTheory.expr_type_def]
QED

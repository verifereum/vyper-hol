(* Bytestring comparisons preserve memory by comparing source-ordered
   Keccak digests. Nonword membership is excluded by source typing. *)
Theory bodyMemBopHeld
Ancestors
  bodyMemoryPreds compileEnv bodyMemBopHeldFacts bodyMemBopHeldOperand bodyMemBopHeldCompare
  exprSimMemoryStack exprSimOperators exprSimHyps exprSimHypsDefs exprLoweringProps

Theorem body_bop_held_mem:
  !cx ty bop e1 e2.
    ((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) \/
     (bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `well_typed_binop ty bop (expr_type e1) (expr_type e2)` by
    (qpat_assum `expr_body_pre _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_body_pre_def,
         vyperTypeSystemTheory.well_typed_expr_def,
         vyperTypeSystemTheory.well_typed_builtin_app_def]) >> simp[]) >>
  `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)` by
    metis_tac[held_membership_word] >>
  `ty = BaseT BoolT` by metis_tac[held_bytestring_eqne_types] >>
  (conj_asm1_tac
   >- (irule held_bytestring_compare_sim_mem >> metis_tac[])) >>
  irule body_expr_vv_sim_mem_stack_word >> simp[compile_bop_stack] >>
  rpt conj_tac
  >>~- ([`Value`], metis_tac[eval_expr_builtin_value]) >>
  fs[vyperASTTheory.expr_type_def, is_word_type_def]
QED

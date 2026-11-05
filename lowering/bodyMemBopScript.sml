(* Memory case of the body induction (bodyMemory's body_mem_mutual): a binary
   operator on two operands, but in and not in on an array literal.  Operands
   of word values by bodyBopMemory's body_bop_word_mem, == and != on address
   and bytesN by body_bop_bytes_eq_mem, the rest by bodyMemBopRest. *)
Theory bodyMemBop
Ancestors
  bodyMemBopRest bodyBopMemory bodyMemoryPreds exprSimMemoryStack
  exprSimOperators exprSimHyps exprLoweringProps

Theorem body_bop_mem_case:
  !cx ty bop e1 e2.
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_mem_ok cx [e1; e2] ==> body_expr_mem_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rpt strip_tac >>
  reverse (Cases_on `(word_value_type (expr_type e1) /\
                      word_value_type (expr_type e2)) \/
                     ((bop = Eq \/ bop = NotEq) /\
                      (expr_type e1 = BaseT AddressT \/
                       ?m. expr_type e1 = BaseT (BytesT (Fixed m))))`)
  >- (match_mp_tac body_bop_rest_mem_case >> asm_rewrite_tac[] >> fs[]) >>
  gvs[body_exprs_mem_ok_def] >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  (conj_asm1_tac
   >- metis_tac[body_bop_word_mem, body_bop_bytes_eq_mem]) >>
  `is_word_type ty` by
    (drule expr_body_pre_bop >> strip_tac >>
     Cases_on `word_value_type (expr_type e1)`
     >- (drule_all well_typed_binop_word_result >> simp[]) >>
     gvs[vyperTypeSystemTheory.well_typed_binop_def,
         compileEnvTheory.is_word_type_def]) >>
  irule body_expr_vv_sim_mem_stack_word >> simp[compile_bop_stack] >>
  rpt conj_tac
  >>~- ([`Value`], metis_tac[eval_expr_builtin_value]) >>
  fs[vyperASTTheory.expr_type_def]
QED

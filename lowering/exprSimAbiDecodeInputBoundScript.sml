Theory exprSimAbiDecodeInputBound
Ancestors
  exprSimHypsDefs allocLimits compileEnv abiBuiltinAllocation
  vfmConstants words arithmetic list

Theorem abi_decode_body_input_bound:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) ==>
  abi_size_bound ce.ce_struct_fields
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < 2 ** 64
Proof
  strip_tac >>
  `alloc_limits_expr ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])` by
    fs[expr_body_pre_def] >>
  drule_all alloc_limits_abi_decode_bound >> strip_tac >>
  `alloc_limits_expr ce e` by
    (qpat_x_assum `alloc_limits_expr _ _` mp_tac >>
     simp[Once alloc_limits_expr_def] >>
     simp[alloc_limits_expr_def]) >>
  `type_alloc_ok ce (expr_type e)` by
    (Cases_on `e` >> gvs[alloc_limits_expr_def, vyperASTTheory.expr_type_def]) >>
  pop_assum mp_tac >>
  simp[type_alloc_ok_def, is_word_type_def, type_memory_bytes_def] >>
  qspec_then `n` mp_tac abi_builtin_word_size_capacity >>
  simp[word_size_def] >> decide_tac
QED

Theorem abi_decode_body_input_word_bound:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) ==>
  abi_size_bound ce.ce_struct_fields
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < dimword (:256)
Proof
  strip_tac >> drule_all abi_decode_body_input_bound >>
  simp[dimword_def] >> decide_tac
QED

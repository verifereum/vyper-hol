Theory bodyFullAbiDecodeSemantic
Ancestors
  exprSimAbiDecodeBodySuccess

Theorem abi_decode_body_caller_success_horizons:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  (!H. V H ==> expr_post H ctx func ce cx e es sa start s0 es1 (BytesV bs) data s) /\
  (?H. V H) /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  abi_decode_immutable_success ce (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)
    bs out d start final ctx func cx es1 s t ==>
  ?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
    (!H. V H ==> vv_post H ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e])
      es sa final s0 es1 (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> rename1 `V H0` >>
  `expr_post H0 ctx func ce cx e es sa start s0 es1 (BytesV bs) data s` by
    metis_tac[] >>
  drule_all abi_decode_body_caller_success >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  qx_gen_tac `H1` >> strip_tac >>
  `expr_post H1 ctx func ce cx e es sa start s0 es1 (BytesV bs) data s` by
    metis_tac[] >>
  drule_all abi_decode_body_caller_success >>
  strip_tac >> gvs[]
QED

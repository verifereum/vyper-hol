(* Result boundary for the single-argument pointer encoder. *)
Theory abiEncodeSinglePtrResult
Ancestors
  abiEncodePtrPhases exprPtrCleanBufferPost
  exprSimAbiEncodeNonwordResult exprLoweringProps valueEncodingProps
  bodyPtrDefs compileEnv venomState valueEncodingDefs

Theorem abi_encode_clean_bytes_memory:
  mload p actual = n2w (LENGTH payload) /\
  mem_bytes_at (p+32) (LENGTH payload) actual.vs_memory = payload /\
  (!i. p <= i /\ i < p+32+LENGTH payload ==> i NOTIN tn.t_mem) ==>
  !mem. mem_agree_outside tn.t_mem actual.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p mem
Proof
  rpt strip_tac >>
  `mem_bytes_at p 32 mem = mem_bytes_at p 32 actual.vs_memory` by
    (sym_tac >> irule clean_window_memory_agree >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     qpat_x_assum `!i. p <= i /\ i < p+32+LENGTH payload ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `mem_bytes_at (p+32) (LENGTH payload) mem = payload` by
    (irule EQ_TRANS >>
     qexists `mem_bytes_at (p+32) (LENGTH payload) actual.vs_memory` >>
     reverse conj_tac >- simp[] >>
     sym_tac >> irule clean_window_memory_agree >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     qpat_x_assum `!i. p <= i /\ i < p+32+LENGTH payload ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  fs[val_in_memory_def, mem_word_at_def, mload_def, mem_bytes_at_def]
QED

Theorem abi_encode_bytes_pointer_posts:
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic N))) /\
  LENGTH payload <= N /\ p < dimword (:256) /\
  eval_operand (Var x) actual = SOME (n2w p) /\
  ptr_covers G tn x actual cap /\
  mload p actual = n2w (LENGTH payload) /\
  mem_bytes_at (p+32) (LENGTH payload) actual.vs_memory = payload /\
  (!i. p <= i /\ i < p+32+LENGTH payload ==> i NOTIN tn.t_mem) /\
  val_store_size (BaseTV (BytesT (Dynamic N))) (BytesV payload) <= cap /\
  type_memory_bytes cenv (lowered_value_type cenv eout) <= cap ==>
  ptr_vv_ok cx ty (Value (BytesV payload))
    (LocatedValue ty (mk_ptr (Var x) LocMemory)) es G tn actual /\
  ptr_buf_ok cenv eout (Var x) G actual
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem actual.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p mem` by
    metis_tac[abi_encode_clean_bytes_memory] >>
  gvs[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, ptr_covers_def,
      contextTheory.mk_ptr_def, vyperStateTheory.read_result_def,
      vyperStateTheory.return_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED

(* Pointer result boundary for the tuple encoder.  No cleanliness is
   required of unused capacity or word padding.  Ordinary vv_post and the
   ghost frame remain separate obligations of the caller. *)
Theory abiEncTuplePtrResult
Ancestors
  abiDecodePtrResultPost abiDecodePtrFlatValue exprSimAbiEncodeTupleResult
  abiBuiltinAllocation exprSimProps exprSimHyps bodyPtrDefs loweringPosts
  valueEncodingDefs valueEncoding valueEncodingProps vyperValue vyperAST
  vyperInterpreter vyperTypeSystem compileEnv context words list arithmetic

Theorem abi_encode_tuple_result_robust:
  well_typed_type_builtin_args (AbiEncode ensure mid0) target tys /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  m = (case mid of NONE => 0 | SOME _ => 4) /\
  mload p actual = n2w (LENGTH bytes + m) /\
  mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
  (case mid of NONE => T | SOME selector =>
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
  LENGTH (abi_encode_method_id_bytes mid0 ++ bytes) <= N /\
  (!i. p <= i /\ i < p+32+m+LENGTH bytes ==> i NOTIN tn.t_mem) ==>
  !mem. mem_agree_outside tn.t_mem actual.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic N)))
      (BytesV (abi_encode_method_id_bytes mid0 ++ bytes)) p mem
Proof
  strip_tac >> match_mp_tac clean_footprint_value_robust >>
  conj_tac >- (irule abi_encode_tuple_result_memory >>
    metis_tac[]) >>
  conj_tac
  >- (simp[val_wf_def, type_memory_size_def] >>
      mp_tac (Q.SPEC `N` abi_builtin_word_size_capacity) >>
      gvs[LENGTH_APPEND] >> decide_tac) >>
  Cases_on `mid0` >>
  gvs[abi_encode_method_id_bytes_def, val_footprint_def,
      well_typed_type_builtin_args_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem abi_encode_bytes_pointer_posts_agree:
  evaluate_type (get_tenv cx) t = SOME (BaseTV (BytesT (Dynamic N))) /\
  lookup_var x s = SOME w /\ ptr_covers G tn x s outsz /\
  32+32*word_size (LENGTH payload) <= outsz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= outsz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) (w2n w) mem) ==>
  ptr_vv_ok cx t (Value (BytesV payload))
    (LocatedValue t' (mk_ptr (Var x) LocMemory)) es G tn s /\
  ptr_buf_ok cenv e (Var x) G s
Proof
  strip_tac >> irule memory_located_pointer_posts >>
  qexistsl [`outsz`, `BaseTV (BytesT (Dynamic N))`, `w`] >>
  simp[val_store_size_def]
QED

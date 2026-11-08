Theory exprSimAbiEncodeBytesOwnership
Ancestors
  loweringPosts valueEncoding vyperValue vyperContext compileEnv
  venomState words finite_map arithmetic abiBuiltinAllocation

Theorem abi_encode_bytes_vv_holds:
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  val_in_memory (BaseTV (BytesT (Dynamic N))) (BytesV payload) p actual.vs_memory ==>
  vv_holds ce cx (BaseT (BytesT (Dynamic N))) result
    (LocatedValue (BaseT (BytesT (Dynamic N)))
      <|ptr_operand := out; ptr_location := LocMemory|>) es' actual
Proof
  rpt strip_tac >> simp[vv_holds_def, evaluate_type_def, is_word_type_def] >>
  qexists_tac `n2w p` >> simp[w2n_n2w] >>
  qexists_tac `BytesV payload` >> simp[]
QED

Theorem abi_encode_bytes_vv_at:
  read_result cx result es' = (INL (BytesV payload),es') /\
  eval_operand out actual = SOME (n2w p) /\ p < dimword (:256) /\
  LENGTH payload <= N /\
  FLOOKUP actual.vs_allocas aid = SOME(p,sz) /\
  origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  32+LENGTH payload <= sz /\
  (!name b n. local_region ce es'.scopes actual name b n ==> p+sz <= b \/ b+n <= p) ==>
  vv_at ce cx (BaseT (BytesT (Dynamic N))) origin sb es' result
    (LocatedValue (BaseT (BytesT (Dynamic N)))
      <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  rpt strip_tac >> simp[vv_at_def, evaluate_type_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[] >> conj_tac
  >- (simp[val_wf_def, type_memory_size_def] >>
      qspec_then `N` mp_tac abi_builtin_word_size_capacity >> decide_tac) >>
  disj1_tac >> qexistsl_tac [`aid`, `p`, `sz`] >> simp[val_footprint_def] >> metis_tac[]
QED

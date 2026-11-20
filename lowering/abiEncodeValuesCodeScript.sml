(* Exact instruction boundaries for the direct tuple encoder. *)
Theory abiEncodeValuesCode
Ancestors
  abiEncoderChildCode abiEncoder exprLowering exprLoweringProps context compileEnv
  emitHelper venomInst list words
Libs monadsyntax

Theorem abi_encode_value_rows_cons:
  compile_abi_encode_value_rows ce dst cursor off ((vv,ty)::rows) =
    comp_ignore_bind (compile_abi_encode_value_rows ce dst cursor off [(vv,ty)])
      (compile_abi_encode_value_rows ce dst cursor
        (off + abi_embedded_static_size ce.ce_struct_fields ty) rows)
Proof
  simp[compile_abi_encode_value_rows_def, LET_THM, comp_ignore_bind_def,
       comp_bind_def, comp_return_def, FUN_EQ_THM] >>
  gen_tac >> rpt (pairarg_tac >> gvs[])
QED

(* Induct over the actual compiler cuts while threading the caller's row
   invariant. The invariant can include the source rows still to unwrap. *)
Theorem abi_encode_value_rows_ind:
  !rows off st en x.
    P off rows st x /\
    compile_abi_encode_value_rows ce dst cursor off rows st = ((),en) /\
    (!vv ty rest h a b last u.
      P h ((vv,ty)::rest) a u /\
      compile_abi_encode_value_rows ce dst cursor h [(vv,ty)] a = ((),b) /\
      compile_abi_encode_value_rows ce dst cursor
        (h + abi_embedded_static_size ce.ce_struct_fields ty) rest b = ((),last) ==>
      ?v. row_step a b u v /\
          P (h + abi_embedded_static_size ce.ce_struct_fields ty) rest b v) /\
    (!a u. row_step a a u u) /\
    (!a b c u v z. row_step a b u v /\ row_step b c v z ==> row_step a c u z) ==>
    ?y. row_step st en x y /\
        P (off + SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) rows))
          [] en y
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_abi_encode_value_rows_def, comp_return_def] >> metis_tac[]) >>
  PairCases_on `h` >>
  PURE_REWRITE_TAC[Once abi_encode_value_rows_cons, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_abi_encode_value_rows ce dst cursor off [(h0,h1)] st` >>
  rename1 `compile_abi_encode_value_rows _ _ _ _ [(_, _)] st = (u,mid)` >>
  Cases_on `u` >> simp[LET_THM] >> strip_tac >>
  qpat_assum `!vv ty rest h a b last u. _` (drule_all_then strip_assume_tac) >>
  qpat_assum `!off st en x. P off rows st x /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  qexists_tac `y` >> conj_tac >- metis_tac[] >>
  qpat_assum `P _ [] en y` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_COMM arithmeticTheory.ADD_ASSOC]
QED

Theorem abi_encode_value_rows_static_trace:
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  compile_abi_encode_value_rows ce dst cursor static_ofst ((vv,ty)::rows) st = ((),en) ==>
  ?head prepared src ready stored.
    emit_op ADD [dst;Lit (n2w static_ofst)] st = (head,prepared) /\
    unwrap_value ce vv prepared = (src,ready) /\
    compile_store_memory ce src head ty ty ready = ((),stored) /\
    compile_abi_encode_value_rows ce dst cursor
      (static_ofst + abi_embedded_static_size ce.ce_struct_fields ty) rows stored = ((),en)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_encode_value_rows _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [Once compile_abi_encode_value_rows_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem abi_encode_value_rows_dynamic_trace:
  is_abi_dynamic ce.ce_struct_fields ty /\
  compile_abi_encode_value_rows ce dst cursor static_ofst ((vv,ty)::rows) st = ((),en) ==>
  ?head tail_ofst tail_ptr prepared src ready len encoded advanced.
    abi_encode_child_prefix dst static_ofst cursor st =
      ((head,tail_ofst,tail_ptr),prepared) /\
    unwrap_value ce vv prepared = (src,ready) /\
    compile_abi_encode_to_buf tail_ptr src
      (type_to_abi_enc_info ce.ce_struct_fields ce ty) ready = (len,encoded) /\
    abi_encode_child_suffix head cursor tail_ofst len encoded = (len,advanced) /\
    compile_abi_encode_value_rows ce dst cursor
      (static_ofst + abi_embedded_static_size ce.ce_struct_fields ty) rows advanced = ((),en)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_encode_value_rows _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [Once compile_abi_encode_value_rows_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  simp[abi_encode_child_prefix_def, abi_encode_child_suffix_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> metis_tac[]
QED

Theorem abi_encode_values_to_buf_trace:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) ==>
  ?cursor allocated ready stored.
    emit_op ALLOCA [Lit 32w] st = (cursor,allocated) /\
    emit_void MSTORE [cursor;Lit (n2w (abi_static_size ce.ce_struct_fields
      (TupleT (MAP SND rows))))] allocated = ((),ready) /\
    compile_abi_encode_value_rows ce dst cursor 0 rows ready = ((),stored) /\
    emit_op MLOAD [cursor] stored = (out,en)
Proof
  simp_tac bool_ss [compile_abi_encode_values_to_buf_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem abi_static_value_not_bytestring[local]:
  ~is_abi_dynamic sfields ty ==> ~is_bytestring_type ty
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def, is_abi_dynamic_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_bytestring_type_def, is_abi_dynamic_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[is_bytestring_type_def, is_abi_dynamic_def]
QED

Theorem abi_encode_static_value_empty:
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  type_memory_bytes ce ty = 0 ==>
  compile_store_memory ce src dst ty ty = comp_return ()
Proof
  strip_tac >> drule abi_static_value_not_bytestring >>
  simp[compile_store_memory_def, compile_copy_memory_def]
QED

(* A static aggregate with a nonempty memory layout emits the same copy as
   the recursive encoder's AbiCopy case. *)
Theorem abi_encode_static_value_copy:
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  0 < type_memory_bytes ce ty ==>
  compile_store_memory ce src dst ty ty =
    comp_ignore_bind
      (compile_abi_encode_to_buf dst src (AbiCopy (type_memory_bytes ce ty)))
      (comp_return ())
Proof
  strip_tac >> drule abi_static_value_not_bytestring >> strip_tac >>
  Cases_on `type_memory_bytes ce ty` >>
  gvs[compile_store_memory_def, compile_copy_memory_def,
      Once compile_abi_encode_child_def, FUN_EQ_THM,
      comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  gen_tac >> Cases_on `emit_void MCOPY [dst; src; Lit (n2w (SUC n))] x` >> simp[]
QED

Theorem abi_encode_static_copy_trace:
  ~is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  0 < type_memory_bytes ce ty /\
  compile_store_memory ce src dst ty ty st = ((),en) ==>
  compile_abi_encode_to_buf dst src (AbiCopy (type_memory_bytes ce ty)) st =
    (Lit (n2w (type_memory_bytes ce ty)),en)
Proof
  strip_tac >> drule_all abi_encode_static_value_copy >>
  disch_then (qspecl_then [`src`,`dst`] (assume_tac o C AP_THM ``st:compile_state``)) >>
  Cases_on `compile_abi_encode_to_buf dst src (AbiCopy (type_memory_bytes ce ty)) st` >>
  rename1 `compile_abi_encode_to_buf _ _ _ _ = (out,next)` >>
  `out = Lit (n2w (type_memory_bytes ce ty))` by
    (qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     PURE_REWRITE_TAC [compile_abi_encode_child_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
     Cases_on `emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))] st` >>
     simp[comp_return_def]) >>
  fs[comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

(* Run the cursor lifetime around the row induction. P carries the written
   prefixes and the caller's saved operands. Each step keeps the same
   materialization policy and the same cursor through the loop. *)
Theorem abi_encode_values_to_buf_ind:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) /\
  (!cursor a b last.
    emit_op ALLOCA [Lit 32w] st = (cursor,a) /\
    emit_void MSTORE [cursor;Lit (n2w (abi_static_size ce.ce_struct_fields
      (TupleT (MAP SND rows))))] a = ((),b) /\
    compile_abi_encode_value_rows ce dst cursor 0 rows b = ((),last) /\
    emit_op MLOAD [cursor] last = (out,en) ==>
    ?u. row_step st b x u /\ P cursor 0 rows b u) /\
  (!cursor vv ty rest h a b last u.
    P cursor h ((vv,ty)::rest) a u /\
    compile_abi_encode_value_rows ce dst cursor h [(vv,ty)] a = ((),b) /\
    compile_abi_encode_value_rows ce dst cursor
      (h + abi_embedded_static_size ce.ce_struct_fields ty) rest b = ((),last) /\
    emit_op MLOAD [cursor] last = (out,en) ==>
    ?v. row_step a b u v /\
        P cursor (h + abi_embedded_static_size ce.ce_struct_fields ty) rest b v) /\
  (!cursor a u.
    P cursor (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) rows)) [] a u /\
    emit_op MLOAD [cursor] a = (out,en) ==>
    ?v. row_step a en u v /\ Q out v) /\
  (!a u. row_step a a u u) /\
  (!a b c u v z. row_step a b u v /\ row_step b c v z ==> row_step a c u z) ==>
  ?y. row_step st en x y /\ Q out y
Proof
  strip_tac >> drule abi_encode_values_to_buf_trace >> strip_tac >>
  rename1 `emit_op MLOAD [cursor] last = (out,en)` >>
  qpat_assum `!cursor a b last. emit_op ALLOCA _ _ = _ /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  mp_tac (Q.SPECL [`rows`,`0`,`ready`,`last`,`u`]
    (INST [``P:num -> (vyper_value # type) list -> compile_state -> 'a -> bool`` |->
       ``\h rest a (u:'a).
         (P:operand -> num -> (vyper_value # type) list -> compile_state -> 'a -> bool)
           cursor h rest a u /\
         compile_abi_encode_value_rows ce dst cursor h rest a = ((),last)``]
         abi_encode_value_rows_ind)) >>
  BETA_TAC >> impl_tac
  >- (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      `last' = last` by
        (qpat_assum `compile_abi_encode_value_rows _ _ _ _ ((_,_)::rest) a = _` mp_tac >>
         PURE_REWRITE_TAC [Once abi_encode_value_rows_cons, comp_ignore_bind_def, comp_bind_def] >>
         simp[]) >>
      qpat_assum `!cursor vv ty rest h a b last u. _`
        (qspecl_then [`cursor`,`vv`,`ty`,`rest`,`h`,`a`,`b`,`last`,`u'`] mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >>
      strip_tac >> qexists_tac `v` >> simp[]) >>
  simp[compile_abi_encode_value_rows_def, comp_return_def] >> strip_tac >>
  qpat_assum `!cursor a u. P cursor _ [] a u /\ _ ==> _`
    (drule_all_then strip_assume_tac) >>
  metis_tac[]
QED

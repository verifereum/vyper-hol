(* TOP-LEVEL: a dynamic-element array uses 32-byte heads and the existing
   field head/tail layout. A completed layout is the source ABI encoding. *)
Theory abiDynamicArrayLayout
Ancestors
  abiFieldLayoutDefs abiFieldSource abiFieldMemory memoryReadProps
  compileEnv venomState contractABI list rich_list pair words arithmetic

Definition abi_dynamic_array_fields_def:
  abi_dynamic_array_fields elem_ty vs = MAP (\v. (T,enc elem_ty v)) vs
End

Theorem abi_dynamic_array_fields_head_size:
  !vs elem_ty. abi_field_head_size (abi_dynamic_array_fields elem_ty vs) = 32 * LENGTH vs
Proof
  Induct_on `vs` >> fs[abi_dynamic_array_fields_def, abi_field_head_size_def, MULT_CLAUSES]
QED

Theorem abi_dynamic_array_fields_map:
  !vs elem_ty.
    is_dynamic elem_ty ==>
    MAP2 (\ty v. (is_dynamic ty, enc ty v)) (REPLICATE (LENGTH vs) elem_ty) vs =
      abi_dynamic_array_fields elem_ty vs
Proof
  Induct_on `vs` >> fs[abi_dynamic_array_fields_def, REPLICATE]
QED

Theorem abi_dynamic_array_encoding:
  !elem_ty vs.
    is_dynamic elem_ty ==>
    enc (Array NONE elem_ty) (ListV vs) =
      word_to_bytes (n2w (LENGTH vs):bytes32) T ++
      abi_field_bytes (32 * LENGTH vs) (abi_dynamic_array_fields elem_ty vs)
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`REPLICATE (LENGTH (vs:abi_value list)) elem_ty`, `0`, `LENGTH (vs:abi_value list)`, `elem_ty`]
    head_lengths_REPLICATE) >> asm_simp_tac bool_ss [ADD_CLAUSES, MULT_COMM] >> DISCH_TAC >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
  simp_tac bool_ss [LET_THM] >>
  mp_tac (Q.SPECL [`REPLICATE (LENGTH (vs:abi_value list)) elem_ty`, `vs`, `32 * LENGTH (vs:abi_value list)`, `0`,
    `[word_to_bytes (n2w (LENGTH (vs:abi_value list)):bytes32) T]`, `[]`] enc_tuple_field_parts) >>
  asm_simp_tac list_ss [abi_dynamic_array_fields_map, abi_field_bytes_def, enc_number_def, LENGTH_REPLICATE]
QED

Theorem abi_dynamic_array_encoded_size:
  !elem_ty vs.
    is_dynamic elem_ty ==>
    LENGTH (enc (Array NONE elem_ty) (ListV vs)) =
      32 + (32 * LENGTH vs + abi_field_tail_size (abi_dynamic_array_fields elem_ty vs))
Proof
  rpt gen_tac >> DISCH_TAC >>
  `LENGTH (word_to_bytes (n2w (LENGTH vs):bytes32) T) = 32` by simp[] >>
  mp_tac (Q.SPECL [`elem_ty`, `vs`] abi_dynamic_array_encoding) >> impl_tac >- simp[] >>
  disch_then (mp_tac o AP_TERM ``LENGTH : byte list -> num``) >>
  asm_simp_tac bool_ss [LENGTH_APPEND, abi_field_bytes_length, abi_dynamic_array_fields_head_size]
QED

Theorem abi_dynamic_array_layout_source:
  !elem_ty vs arena ss.
    is_dynamic elem_ty /\
    mload arena ss = n2w (LENGTH vs) /\
    abi_fields_layout (abi_dynamic_array_fields elem_ty vs) (arena + 32) 0 (32 * LENGTH vs) ss ==>
    read_memory arena (LENGTH (enc (Array NONE elem_ty) (ListV vs))) ss =
      enc (Array NONE elem_ty) (ListV vs)
Proof
  rpt gen_tac >> strip_tac >>
  `read_memory (arena + 32)
    (LENGTH (abi_field_bytes (32 * LENGTH vs) (abi_dynamic_array_fields elem_ty vs))) ss =
    abi_field_bytes (32 * LENGTH vs) (abi_dynamic_array_fields elem_ty vs)` by
    (mp_tac (Q.SPECL [`abi_dynamic_array_fields elem_ty vs`, `arena + 32`, `ss`] abi_fields_layout_contiguous) >>
     simp[abi_dynamic_array_fields_head_size]) >>
  `LENGTH (word_to_bytes (n2w (LENGTH vs):bytes32) T) = 32` by simp[] >>
  asm_simp_tac bool_ss [abi_dynamic_array_encoding, LENGTH_APPEND] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [read_memory_split])) >>
  asm_simp_tac bool_ss [read_memory_word]
QED

Theorem abi_dynamic_array_layout_result:
  !elem_ty vs arena dyn_addr before out op.
    is_dynamic elem_ty /\ mload arena before = n2w (LENGTH vs) /\
    abi_fields_layout (abi_dynamic_array_fields elem_ty vs) (arena + 32) 0 (32 * LENGTH vs) before /\
    mload (w2n dyn_addr) before =
      n2w (32 * LENGTH vs + abi_field_tail_size (abi_dynamic_array_fields elem_ty vs)) /\
    out.vs_memory = before.vs_memory /\ eval_operand op out = SOME (32w + mload (w2n dyn_addr) before) ==>
    read_memory arena (LENGTH (enc (Array NONE elem_ty) (ListV vs))) out = enc (Array NONE elem_ty) (ListV vs) /\
    eval_operand op out = SOME (n2w (LENGTH (enc (Array NONE elem_ty) (ListV vs))))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`elem_ty`, `vs`, `arena`, `before`] abi_dynamic_array_layout_source) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `read_memory arena (LENGTH (enc (Array NONE elem_ty) (ListV vs))) out =
    read_memory arena (LENGTH (enc (Array NONE elem_ty) (ListV vs))) before` by
    (PURE_REWRITE_TAC [read_memory_def] >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`elem_ty`, `vs`] abi_dynamic_array_encoded_size) >> impl_tac >- simp[] >> DISCH_TAC >>
  asm_simp_tac bool_ss [word_add_n2w]
QED

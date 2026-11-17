(* Constructor staging's source-window and encoder-resource boundary.
   The representative ABI type need not be the literal source ABI type:
   in particular, source-typed fixed Bytes[0] is retained. *)
Theory createCtorTupleWindow
Ancestors
  exprSimAbiEncodeSourceTranslation abiEncoderWindow abiEncoderWindowContract

Theorem ctor_tuple_representative_window:
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t v. evaluate_type (get_tenv cx) t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv (ArrayV (TupleV values)) /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV values)) = SOME av /\
  val_in_memory tv (ArrayV (TupleV values)) source_base mem /\
  source_cap = type_memory_size tv ==>
  ?ct rv.
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys))
      ct rv source_base source_cap mem /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    source_rep (get_tenv cx) (TupleT tys)
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys)) ct
Proof
  strip_tac >>
  `?ct rv.
    source_rep (get_tenv cx) (TupleT tys)
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys)) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    abi_encoder_open_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys))
      ct rv source_base (type_memory_size tv) mem` by
    (irule abi_encode_translated_source_window >> simp[] >>
     conj_tac
     >- (qexists `get_tenv cx` >> simp[]) >>
     qexists `ArrayV (TupleV values)` >> simp[]) >>
  drule_all abi_encoder_open_input_window >> strip_tac >>
  qexistsl_tac [`ct`, `rv`] >> simp[]
QED

(* Encoding equality lets the destination and scratch geometry be stated
   with the canonical encoding. None of these facts follows from the source
   window alone. *)
Theorem ctor_tuple_encoder_pre_resources:
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei ct rv source_base source_cap s.vs_memory /\
  enc ct rv = enc at av /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w dest_base) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  source_base + source_cap <= s.vs_alloca_next /\
  dest_base + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint
    (source_base,source_cap) (dest_base,LENGTH (enc at av)) /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    venomMemDefs$regions_disjoint (source_base,source_cap) (b,sz) /\
    venomMemDefs$regions_disjoint (dest_base,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_window_pre ctx func st en dst src ei ct rv
    source_base source_cap dest_base s
Proof
  strip_tac >> pure_rewrite_tac[abi_encoder_window_pre_def] >>
  asm_rewrite_tac[]
QED

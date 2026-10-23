(* Structural metadata contract for static ABI layout.  This relation contains
   no values, encoded bytes, or memory predicates.  Size and environment
   consistency are explicit obligations, not consequences of no-clamp. *)
Theory abiStaticLayoutProps
Ancestors
  exprLowering vyperTyping compileEnv valueEncoding vyperABI contractABI

Theorem static_layout_dimindex_256[local,simp]:
  dimindex(:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Definition static_layout_header_def:
  static_layout_header cenv tenv ty tv <=>
    evaluate_type tenv ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    ~is_abi_dynamic cenv.ce_struct_fields ty /\
    static_length (vyper_to_abi_type tenv ty) = type_memory_size tv /\
    type_memory_size tv = type_memory_bytes cenv ty
End

Inductive static_layout_compatible:
[base:]
  (!cenv tenv bt.
    is_word_type (BaseT bt) /\
    static_layout_header cenv tenv (BaseT bt) (BaseTV bt) ==>
    static_layout_compatible cenv tenv (BaseT bt) (BaseTV bt))
[flag:]
  (!cenv tenv nsid m.
    FLOOKUP tenv nsid = SOME (FlagArgs m) /\
    cenv.ce_flag_n_members (nsid_to_string nsid) = m /\
    static_layout_header cenv tenv (FlagT nsid) (FlagTV m) ==>
    static_layout_compatible cenv tenv (FlagT nsid) (FlagTV m))
[array:]
  (!cenv tenv ty tv n.
    static_layout_compatible cenv tenv ty tv /\
    static_layout_header cenv tenv (ArrayT ty (Fixed n))
      (ArrayTV tv (Fixed n)) ==>
    static_layout_compatible cenv tenv (ArrayT ty (Fixed n))
      (ArrayTV tv (Fixed n)))
[tuple:]
  (!cenv tenv tys tvs.
    LIST_REL (static_layout_compatible cenv tenv) tys tvs /\
    static_layout_header cenv tenv (TupleT tys) (TupleTV tvs) ==>
    static_layout_compatible cenv tenv (TupleT tys) (TupleTV tvs))
[struct_case:]
  (!cenv tenv nsid args tvs.
    FLOOKUP tenv nsid = SOME (StructArgs args) /\
    LIST_REL (static_layout_compatible cenv (tenv \\ nsid))
      (MAP SND args) tvs /\
    static_layout_header cenv tenv (StructT nsid)
      (StructTV (ZIP (MAP FST args,tvs))) ==>
    static_layout_compatible cenv tenv (StructT nsid)
      (StructTV (ZIP (MAP FST args,tvs))))
End

Theorem static_layout_compatible_header:
  static_layout_compatible cenv tenv ty tv ==>
  static_layout_header cenv tenv ty tv
Proof
  simp[Once static_layout_compatible_cases] >> metis_tac[]
QED

Theorem static_layout_compatible_properties:
  static_layout_compatible cenv tenv ty tv ==>
  evaluate_type tenv ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type tenv ty) /\
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  static_length (vyper_to_abi_type tenv ty) = type_memory_size tv /\
  type_memory_size tv = type_memory_bytes cenv ty
Proof
  simp[GSYM static_layout_header_def, static_layout_compatible_header]
QED

Theorem static_layout_dynamic_bytes_excluded:
  ~static_layout_compatible cenv tenv (BaseT (BytesT (Dynamic n))) tv
Proof
  simp[Once static_layout_compatible_cases, is_word_type_def]
QED

Theorem static_layout_dynamic_array_excluded:
  ~static_layout_compatible cenv tenv (ArrayT ty (Dynamic n)) tv
Proof
  simp[Once static_layout_compatible_cases]
QED

(* Constructor inversions expose children without opening layout metadata. *)
Theorem static_layout_base_iff:
  static_layout_compatible cenv tenv (BaseT bt) tv <=>
  tv = BaseTV bt /\ is_word_type (BaseT bt) /\
  static_layout_header cenv tenv (BaseT bt) (BaseTV bt)
Proof
  simp[Once static_layout_compatible_cases] >> metis_tac[]
QED

Theorem static_layout_array_iff:
  static_layout_compatible cenv tenv (ArrayT ty (Fixed n)) atv <=>
  ?tv. atv = ArrayTV tv (Fixed n) /\
       static_layout_compatible cenv tenv ty tv /\
       static_layout_header cenv tenv (ArrayT ty (Fixed n)) atv
Proof
  simp[Once static_layout_compatible_cases] >> metis_tac[]
QED

Theorem static_layout_tuple_iff:
  static_layout_compatible cenv tenv (TupleT tys) atv <=>
  ?tvs. atv = TupleTV tvs /\
        LIST_REL (static_layout_compatible cenv tenv) tys tvs /\
        static_layout_header cenv tenv (TupleT tys) atv
Proof
  simp[Once static_layout_compatible_cases] >> metis_tac[]
QED

Theorem static_layout_struct_iff:
  static_layout_compatible cenv tenv (StructT nsid) atv <=>
  ?args tvs.
    FLOOKUP tenv nsid = SOME (StructArgs args) /\
    LIST_REL (static_layout_compatible cenv (tenv \\ nsid))
      (MAP SND args) tvs /\
    atv = StructTV (ZIP (MAP FST args,tvs)) /\
    static_layout_header cenv tenv (StructT nsid) atv
Proof
  simp[Once static_layout_compatible_cases] >> metis_tac[]
QED

Theorem static_layout_uint256_probe:
  static_layout_compatible cenv tenv (BaseT (UintT 256))
    (BaseTV (UintT 256))
Proof
  simp[static_layout_base_iff, static_layout_header_def,
       is_word_type_def, vyperValueTheory.evaluate_type_def,
       type_memory_size_def, type_memory_bytes_def,
       is_abi_dynamic_def, is_dynamic_def, static_length_def,
       wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem static_layout_uint256_pair_probe:
  static_layout_compatible cenv tenv
    (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
Proof
  simp[static_layout_array_iff, static_layout_uint256_probe,
       static_layout_header_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def,
       type_memory_size_def, type_memory_bytes_def,
       is_abi_dynamic_def, is_dynamic_def, static_length_def,
       wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem static_layout_flag_iff:
  static_layout_compatible cenv tenv (FlagT nsid) tv <=>
  ?m. tv = FlagTV m /\
      FLOOKUP tenv nsid = SOME (FlagArgs m) /\
      cenv.ce_flag_n_members (nsid_to_string nsid) = m /\
      static_layout_header cenv tenv (FlagT nsid) tv
Proof
  simp[Once static_layout_compatible_cases] >> metis_tac[]
QED

Theorem static_layout_flag256_probe:
  FLOOKUP tenv nsid = SOME (FlagArgs 256) /\
  cenv.ce_flag_n_members (nsid_to_string nsid) = 256 ==>
  static_layout_compatible cenv tenv (FlagT nsid) (FlagTV 256) /\
  type_to_abi_dec_info cenv.ce_struct_fields cenv (FlagT nsid) =
    DecPrimWord NoClamp
Proof
  simp[static_layout_flag_iff, static_layout_header_def,
       vyperValueTheory.evaluate_type_def,
       type_memory_size_def, type_memory_bytes_def,
       is_abi_dynamic_def, is_dynamic_def, static_length_def,
       type_to_abi_dec_info_def]
QED

Theorem static_layout_two_field_struct_probe:
  FLOOKUP tenv nsid = SOME (StructArgs
    [("a",BaseT (UintT 256)); ("b",BaseT (UintT 256))]) /\
  FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME
    [("a",BaseT (UintT 256),32); ("b",BaseT (UintT 256),32)] ==>
  static_layout_compatible cenv tenv (StructT nsid)
    (StructTV [("a",BaseTV (UintT 256)); ("b",BaseTV (UintT 256))])
Proof
  strip_tac >> simp[static_layout_struct_iff] >>
  qexists_tac `[BaseTV (UintT 256); BaseTV (UintT 256)]` >>
  simp[static_layout_uint256_probe, static_layout_header_def,
       vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def,
       type_memory_size_def, type_memory_bytes_def,
       get_struct_fields_def, is_abi_dynamic_def,
       is_dynamic_def, static_length_def, wordsTheory.dimword_def]
QED

(* In particular, sparse-array supplied elements may themselves be arrays;
   their compatibility is independent of which keys are present. *)
Theorem static_layout_nested_array_probe:
  static_layout_compatible cenv tenv
    (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Fixed 3))
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (Fixed 3))
Proof
  simp[static_layout_array_iff, static_layout_uint256_pair_probe,
       static_layout_uint256_probe,
       static_layout_header_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def,
       type_memory_size_def, type_memory_bytes_def,
       is_abi_dynamic_def, is_dynamic_def, static_length_def,
       wordsTheory.dimword_def]
QED

Theorem static_layout_string_excluded:
  ~static_layout_compatible cenv tenv (BaseT (StringT n)) tv
Proof
  simp[static_layout_base_iff, is_word_type_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_STATIC_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static layout not kernel closed: " ^ n)
  end) (DB.thms "abiStaticLayoutProps");

(* Recursive pure translation contract. The descending compiler map is not
   the full map used by layout computations. No execution facts occur here. *)
Theory abiDecoderCoherence
Ancestors
  abiDecoderTypedContract abiDecodeRanges abiStaticLayoutProps exprLowering vyperTyping
  compileEnv valueEncoding vyperABI contractABI

Definition abi_decoder_header_def:
  abi_decoder_header ce env ty tv <=>
    evaluate_type env ty = SOME tv /\
    type_memory_size tv = type_memory_bytes ce ty /\
    is_dynamic (vyper_to_abi_type env ty) = is_abi_dynamic ce.ce_struct_fields ty /\
    abi_embedded_static_size ce.ce_struct_fields ty =
      abi_member_head_size (vyper_to_abi_type env ty) /\
    (~is_dynamic (vyper_to_abi_type env ty) ==>
      static_length (vyper_to_abi_type env ty) = type_memory_size tv)
End

Definition abi_decoder_scalar_valid_def:
  abi_decoder_scalar_valid (UintT n) = (0 < n /\ n <= 256) /\
  abi_decoder_scalar_valid (IntT n) = (0 < n /\ n <= 256) /\
  abi_decoder_scalar_valid (BytesT (Fixed n)) = (0 < n /\ n <= 32) /\
  abi_decoder_scalar_valid _ = T
End

Inductive abi_decoder_coherent:
[base:]
  (!ce env sf bt.
    abi_decoder_scalar_valid bt /\
    abi_decoder_header ce env (BaseT bt) (BaseTV bt) ==>
    abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt))
[flag:]
  (!ce env sf nsid n.
    FLOOKUP env nsid = SOME (FlagArgs n) /\ n <= 256 /\
    ce.ce_flag_n_members (nsid_to_string nsid) = n /\
    abi_decoder_header ce env (FlagT nsid) (FlagTV n) ==>
    abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n))
[array:]
  (!ce env sf ty tv bound.
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_header ce env (ArrayT ty bound) (ArrayTV tv bound) ==>
    abi_decoder_coherent ce env sf (ArrayT ty bound) (ArrayTV tv bound))
[tuple:]
  (!ce env sf tys tvs.
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    abi_decoder_header ce env (TupleT tys) (TupleTV tvs) ==>
    abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs))
[struct_case:]
  (!ce env sf nsid args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
    LIST_REL (abi_decoder_coherent ce (env \\ nsid)
       (sf \\ nsid_to_string nsid)) (MAP SND args) tvs /\
    abi_decoder_header ce env (StructT nsid)
      (StructTV (ZIP (MAP FST args,tvs))) ==>
    abi_decoder_coherent ce env sf (StructT nsid)
      (StructTV (ZIP (MAP FST args,tvs))))
End

Theorem abi_decoder_coherent_header:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_header ce env ty tv
Proof
  simp[Once abi_decoder_coherent_cases] >> metis_tac[]
QED

Theorem abi_decoder_coherent_base_iff:
  abi_decoder_coherent ce env sf (BaseT bt) tv <=>
  tv = BaseTV bt /\ abi_decoder_scalar_valid bt /\
  abi_decoder_header ce env (BaseT bt) (BaseTV bt)
Proof
  simp[Once abi_decoder_coherent_cases] >> metis_tac[]
QED

Theorem abi_decoder_coherent_flag_iff:
  abi_decoder_coherent ce env sf (FlagT nsid) tv <=>
  ?n. tv = FlagTV n /\ FLOOKUP env nsid = SOME (FlagArgs n) /\
      n <= 256 /\ ce.ce_flag_n_members (nsid_to_string nsid) = n /\
      abi_decoder_header ce env (FlagT nsid) (FlagTV n)
Proof
  simp[Once abi_decoder_coherent_cases] >> metis_tac[]
QED

Theorem abi_decoder_coherent_array_iff:
  abi_decoder_coherent ce env sf (ArrayT ty bound) atv <=>
  ?tv. atv = ArrayTV tv bound /\ abi_decoder_coherent ce env sf ty tv /\
       abi_decoder_header ce env (ArrayT ty bound) atv
Proof
  simp[Once abi_decoder_coherent_cases] >> metis_tac[]
QED

Theorem abi_decoder_coherent_tuple_iff:
  abi_decoder_coherent ce env sf (TupleT tys) atv <=>
  ?tvs. atv = TupleTV tvs /\
        LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
        abi_decoder_header ce env (TupleT tys) atv
Proof
  simp[Once abi_decoder_coherent_cases] >> metis_tac[]
QED

Theorem abi_decoder_coherent_struct_iff:
  abi_decoder_coherent ce env sf (StructT nsid) atv <=>
  ?args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (\(name,ty,sz). (name,ty)) fields = args /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
    LIST_REL (abi_decoder_coherent ce (env \\ nsid)
       (sf \\ nsid_to_string nsid)) (MAP SND args) tvs /\
    atv = StructTV (ZIP (MAP FST args,tvs)) /\
    abi_decoder_header ce env (StructT nsid) atv
Proof
  simp[Once abi_decoder_coherent_cases] >> metis_tac[]
QED

(* Strong recursive precondition; the older candidate remains unchanged. *)
Definition abi_decoder_recursive_pre_def:
  abi_decoder_recursive_pre ce env sf ty tv di av v st last
      src dst opc hi sb d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    di = type_to_abi_dec_info sf ce ty /\
    abi_decoder_pre ce env ty tv
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v st last
      src dst opc hi sb d b cap s
End

Theorem abi_decoder_recursive_pre_root:
  abi_decoder_recursive_pre ce env ce.ce_struct_fields ty tv di av v
    st last src dst opc hi sb d b cap s ==>
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s
Proof
  simp[abi_decoder_recursive_pre_def]
QED

Theorem abi_decoder_coherent_root_metadata:
  abi_decoder_coherent ce env sf ty tv /\ value_has_type tv v /\
  has_type (vyper_to_abi_type env ty) av /\ abi_to_vyper env ty av = SOME v ==>
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v
Proof
  metis_tac[abi_decoder_metadata_def, abi_decoder_coherent_header,
            abi_decoder_header_def]
QED

Theorem abi_decoder_flag_inconsistent_excluded:
  FLOOKUP env nsid = SOME (FlagArgs 256) /\
  ce.ce_flag_n_members (nsid_to_string nsid) = 0 ==>
  ~abi_decoder_coherent ce env sf (FlagT nsid) tv
Proof
  simp[abi_decoder_coherent_flag_iff]
QED

Theorem abi_decoder_flag256_probe:
  FLOOKUP env nsid = SOME (FlagArgs 256) /\
  ce.ce_flag_n_members (nsid_to_string nsid) = 256 ==>
  abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV 256) /\
  type_to_abi_dec_info sf ce (FlagT nsid) = DecPrimWord NoClamp
Proof
  simp[abi_decoder_coherent_flag_iff, abi_decoder_header_def,
       vyperValueTheory.evaluate_type_def, type_memory_size_def,
       type_memory_bytes_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       abi_member_head_size_def, is_dynamic_def, static_length_def,
       type_to_abi_dec_info_def]
QED

Theorem abi_decoder_coherent_bytes_iff:
  abi_decoder_coherent ce env sf (BaseT (BytesT (Dynamic n))) tv <=>
  tv = BaseTV (BytesT (Dynamic n)) /\
  abi_decoder_header ce env (BaseT (BytesT (Dynamic n))) tv
Proof
  simp[abi_decoder_coherent_base_iff, abi_decoder_scalar_valid_def] >> metis_tac[]
QED

Theorem abi_decoder_coherent_string_iff:
  abi_decoder_coherent ce env sf (BaseT (StringT n)) tv <=>
  tv = BaseTV (StringT n) /\
  abi_decoder_header ce env (BaseT (StringT n)) tv
Proof
  simp[abi_decoder_coherent_base_iff, abi_decoder_scalar_valid_def] >> metis_tac[]
QED

Theorem abi_decoder_uint256_probe:
  abi_decoder_coherent ce env sf (BaseT (UintT 256)) (BaseTV (UintT 256))
Proof
  simp[abi_decoder_coherent_base_iff, abi_decoder_scalar_valid_def,
       abi_decoder_header_def, vyperValueTheory.evaluate_type_def,
       type_memory_size_def, type_memory_bytes_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       abi_member_head_size_def, is_dynamic_def, static_length_def]
QED

(* A single concrete field is translated with BOTH maps deleted, while ce
   stays fixed. This remains valid when sf is not ce.ce_struct_fields. *)
Theorem abi_decoder_one_field_struct_probe:
  FLOOKUP env nsid = SOME (StructArgs [("a",BaseT (UintT 256))]) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME [("a",BaseT (UintT 256),32)] /\
  abi_decoder_header ce env (StructT nsid)
    (StructTV [("a",BaseTV (UintT 256))]) ==>
  abi_decoder_coherent ce env sf (StructT nsid)
    (StructTV [("a",BaseTV (UintT 256))]) /\
  type_to_abi_dec_info sf ce (StructT nsid) =
    DecComplex (is_abi_dynamic ce.ce_struct_fields (BaseT (UintT 256)))
      [(type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce (BaseT (UintT 256)),
        abi_embedded_static_size ce.ce_struct_fields (BaseT (UintT 256)),
        type_memory_bytes ce (BaseT (UintT 256)))] /\
  abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid)
    (BaseT (UintT 256)) (BaseTV (UintT 256))
Proof
  strip_tac >> conj_tac
  >- (simp[abi_decoder_coherent_struct_iff] >>
      qexists_tac `[BaseTV (UintT 256)]` >>
      simp[abi_decoder_uint256_probe, type_memory_bytes_def]) >>
  simp[Once type_to_abi_dec_info_def, abi_decoder_uint256_probe]
QED

Theorem abi_decoder_one_field_struct_realizable:
  FLOOKUP env nsid = SOME (StructArgs [("a",BaseT (UintT 256))]) /\
  FLOOKUP ce.ce_struct_fields (nsid_to_string nsid) =
    SOME [("a",BaseT (UintT 256),32)] ==>
  abi_decoder_coherent ce env ce.ce_struct_fields (StructT nsid)
    (StructTV [("a",BaseTV (UintT 256))])
Proof
  strip_tac >> irule (cj 1 abi_decoder_one_field_struct_probe) >>
  simp[abi_decoder_header_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def, type_memory_size_def,
       type_memory_bytes_def, get_struct_fields_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       abi_member_head_size_def, is_dynamic_def, static_length_def,
       wordsTheory.dimword_def]
QED

Theorem abi_decoder_coherent_tuple_child:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  i < LENGTH tys ==>
  abi_decoder_coherent ce env sf (EL i tys) (EL i tvs)
Proof
  simp[abi_decoder_coherent_tuple_iff] >> rpt strip_tac >>
  metis_tac[listTheory.LIST_REL_EL_EQN]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_COHERENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder coherence not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCoherence");

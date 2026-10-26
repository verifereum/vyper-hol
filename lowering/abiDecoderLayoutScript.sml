(* Pure consequences of coherent recursive decoder metadata. *)
Theory abiDecoderLayout
Ancestors
  abiDecoderCoherence abiBulkLayoutProps abiStaticLayoutProps
  abiStaticReverseProps vyperABI vyperABIRoundtrip valueEncoding exprLowering compileEnv contractABI

Theorem abi_decoder_static_header:
  abi_decoder_header ce env ty tv /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  static_layout_header ce env ty tv
Proof
  rw[abi_decoder_header_def, static_layout_header_def] >> gvs[]
QED

Theorem abi_decoder_static_children[local]:
  !tys tvs. LIST_REL (\ty tv. ~is_dynamic (vyper_to_abi_type env ty) ==>
      static_layout_compatible ce env ty tv) tys tvs /\
    ~EXISTS is_dynamic (vyper_to_abi_types env tys) ==>
    LIST_REL (static_layout_compatible ce env) tys tvs
Proof
  Induct >> Cases_on `tvs` >> simp[vyper_to_abi_type_def] >> metis_tac[]
QED

Theorem abi_decoder_coherent_static:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  static_layout_compatible ce env ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple"
  >> suspend "struct"
QED

Resume abi_decoder_coherent_static[base]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[static_layout_base_iff] >> conj_tac
  >- (Cases_on `bt` >> gvs[is_word_type_def, abi_decoder_scalar_valid_def,
         is_dynamic_def] >> Cases_on `b` >> gvs[is_word_type_def,
         abi_decoder_scalar_valid_def, is_dynamic_def]) >>
  irule abi_decoder_static_header >> simp[]
QED

Resume abi_decoder_coherent_static[flag]:
  rpt strip_tac >> simp[static_layout_flag_iff] >>
  irule abi_decoder_static_header >> simp[]
QED

Resume abi_decoder_coherent_static[array]:
  rpt gen_tac >> strip_tac >> Cases_on `bound` >>
  simp[is_dynamic_def] >> strip_tac >>
  simp[static_layout_array_iff] >>
  irule abi_decoder_static_header >> simp[is_dynamic_def]
QED

Resume abi_decoder_coherent_static[tuple]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  `LIST_REL (static_layout_compatible ce env) tys tvs` by
    (irule abi_decoder_static_children >> gvs[is_dynamic_def, any_dynamic_EXISTS]) >>
  simp[static_layout_tuple_iff] >>
  irule abi_decoder_static_header >> simp[]
QED

Resume abi_decoder_coherent_static[struct]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  `LIST_REL (static_layout_compatible ce (env \\ nsid)) (MAP SND args) tvs` by
    (irule abi_decoder_static_children >>
     gvs[vyper_to_abi_type_def, is_dynamic_def, any_dynamic_EXISTS]) >>
  simp[static_layout_struct_iff] >> qexists_tac `tvs` >> simp[] >>
  irule abi_decoder_static_header >> simp[]
QED

Finalise abi_decoder_coherent_static

(* The static consequence is stronger than needed: no-clamp is a branch
   selection test, not a premise of structural static compatibility. sf is
   deliberately kept distinct from ce.ce_struct_fields. *)
Theorem abi_decoder_unclamped_static_layout:
  abi_decoder_coherent ce env sf ty tv /\
  di = type_to_abi_dec_info sf ce ty /\ ~dec_info_needs_clamp di /\
  ~is_abi_dynamic ce.ce_struct_fields ty ==>
  static_layout_compatible ce env ty tv
Proof
  metis_tac[abi_decoder_coherent_static, abi_decoder_coherent_header,
            abi_decoder_header_def]
QED

(* This existing semantic roundtrip is unconditional on compiler maps. Its
   checked reuse avoids introducing a conversion conclusion into coherence. *)
Theorem abi_decoder_typed_conversion:
  abi_decoder_coherent ce env sf ty tv /\
  has_type (vyper_to_abi_type env ty) av /\ value_has_type tv v /\
  abi_to_vyper env ty av = SOME v ==>
  vyper_to_abi env ty v = SOME av
Proof
  metis_tac[abi_to_vyper_vyper_to_abi]
QED

Theorem abi_decoder_descended_bulk_layout:
  abi_decoder_coherent ce env sf ty tv /\
  di = type_to_abi_dec_info sf ce ty /\ ~dec_info_needs_clamp di /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  has_type (vyper_to_abi_type env ty) av /\ value_has_type tv v /\
  abi_to_vyper env ty av = SOME v /\
  mem_bytes_at dst (type_memory_bytes ce ty) mem =
    enc (vyper_to_abi_type env ty) av ==>
  val_in_memory tv v dst mem
Proof
  rpt strip_tac >>
  drule_all abi_decoder_unclamped_static_layout >> strip_tac >>
  drule_all abi_decoder_typed_conversion >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  irule static_canonical_memory_layout >> metis_tac[]
QED

Theorem abi_decoder_descended_encoding_length:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  value_has_type tv v /\ abi_to_vyper env ty av = SOME v ==>
  LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_bytes ce ty
Proof
  rpt strip_tac >>
  `static_layout_compatible ce env ty tv` by
    (metis_tac[abi_decoder_coherent_static, abi_decoder_coherent_header,
                abi_decoder_header_def]) >>
  irule abi_bulk_encoding_length >> metis_tac[abi_to_vyper_vyper_to_abi]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder layout not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderLayout");


(* Arbitrary-byte source and layout boundaries for the static bulk branch. *)
Theory exprSimAbiDecodeArrayBulk
Ancestors
  abiDecoderScalarOutcome abiDecoderLayout abiValidStatic
  abiDecoderPrimitiveSource abiDecoderClamp
  vyperABI contractABI valueEncoding valueEncodingProps vyperTypeSystem
  abiDecoderCoherence compileEnv vyperValue valueEncodingTyping
  finite_map arithmetic rich_list list

Theorem abi_decoder_unclamped_word_window:
  abi_decoder_coherent ce env sf ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord NoClamp /\
  32 <= LENGTH (bs:byte list) /\
  mem_word_at d mem = word_of_bytes T (0w:bytes32) (TAKE 32 bs) ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 bs) /\
  ?v. abi_to_vyper env ty
        (dec (vyper_to_abi_type env ty) (TAKE 32 bs)) = SOME v /\
      val_in_memory tv v d mem
Proof
  strip_tac >>
  `LENGTH (TAKE 32 bs) = 32` by simp[LENGTH_TAKE_EQ] >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) (TAKE 32 bs) /\
   ?v. abi_to_vyper env ty
     (dec (vyper_to_abi_type env ty) (TAKE 32 bs)) = SOME v` by
    (drule_all abi_decoder_primitive_source_acceptance >>
     simp[abi_decoder_clamp_valid_def]) >>
  simp[] >>
  irule abi_decoder_primitive_memory_intro >> metis_tac[]
QED

Theorem abi_decode_static_window_width:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_abi_dynamic ce.ce_struct_fields ty ==>
  static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> metis_tac[]
QED

Theorem abi_decode_coherent_memory_positive:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  0 < type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `0 < type_slot_size tv` by metis_tac[assignable_type_slot_size_pos] >>
  metis_tac[type_memory_size_pos]
QED

Theorem abi_decode_fixed_bulk_shape:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed n)) atv /\
  assignable_type env (ArrayT ty (Fixed n)) /\
  type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256) ==>
  n < dimword (:256) /\
  (0 < n ==> type_memory_bytes ce ty <=
      type_memory_bytes ce (ArrayT ty (Fixed n)))
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_array_iff] >> strip_tac >> gvs[] >>
  `assignable_type env ty` by fs[assignable_type_def] >>
  `0 < type_memory_bytes ce ty` by
    (irule abi_decode_coherent_memory_positive >> metis_tac[]) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  fs[abi_decoder_header_def, type_memory_size_def] >>
  `n <= n * type_memory_bytes ce ty` by simp[] >>
  conj_tac >- decide_tac >> strip_tac >>
  `type_memory_bytes ce ty <= n * type_memory_bytes ce ty` by simp[] >>
  decide_tac
QED

Theorem abi_decode_member_list_shape:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    EVERY (assignable_type env) tys ==>
    LENGTH tys <= type_memory_size_list tvs /\
    (!ty. MEM ty tys ==> type_memory_bytes ce ty <= type_memory_size_list tvs)
Proof
  Induct >- (Cases >> simp[type_memory_size_def]) >>
  qx_gen_tac `ty` >> Cases_on `tvs` >>
  simp_tac (srw_ss()) [LIST_REL_def, EVERY_DEF] >> strip_tac >>
  `0 < type_memory_bytes ce ty` by
    (irule abi_decode_coherent_memory_positive >> metis_tac[]) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `LENGTH tys <= type_memory_size_list t /\
   (!ty. MEM ty tys ==> type_memory_bytes ce ty <= type_memory_size_list t)`
    by metis_tac[] >>
  simp[type_memory_size_def] >> gen_tac >> strip_tac
  >- (asm_rewrite_tac[] >> decide_tac) >>
  qpat_x_assum `!ty. MEM ty tys ==> _` drule >> decide_tac
QED

Theorem abi_decode_tuple_bulk_shape:
  abi_decoder_coherent ce env sf (TupleT tys) atv /\
  assignable_type env (TupleT tys) /\
  type_memory_bytes ce (TupleT tys) < dimword (:256) ==>
  LENGTH tys < dimword (:256) /\
  (!ty. MEM ty tys ==> type_memory_bytes ce ty <= type_memory_bytes ce (TupleT tys))
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_tuple_iff] >> strip_tac >> gvs[] >>
  `EVERY (assignable_type env) tys` by
    (qpat_x_assum `assignable_type env (TupleT tys)` mp_tac >>
     simp_tac bool_ss [Once assignable_type_def] >> metis_tac[]) >>
  drule_all abi_decode_member_list_shape >> strip_tac >>
  fs[abi_decoder_header_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem abi_decode_struct_bulk_shape:
  abi_decoder_coherent ce env sf (StructT nsid) atv /\
  assignable_type env (StructT nsid) /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  type_memory_bytes ce (StructT nsid) < dimword (:256) ==>
  LENGTH args < dimword (:256) /\
  (!ty. MEM ty (MAP SND args) ==>
     type_memory_bytes ce ty <= type_memory_bytes ce (StructT nsid))
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [abi_decoder_coherent_struct_iff] >> strip_tac >>
  qpat_x_assum `MAP _ fields = _` kall_tac >> gvs[] >>
  `EVERY (assignable_type (env \\ nsid)) (MAP SND args)` by
    (qpat_x_assum `assignable_type env (StructT nsid)` mp_tac >>
     asm_simp_tac (srw_ss()) [Once assignable_type_def, EVERY_MAP,
       combinTheory.o_DEF]) >>
  drule_all abi_decode_member_list_shape >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by fs[LIST_REL_EL_EQN] >>
  fs[abi_decoder_header_def, type_memory_size_def, type_memory_size_fields_zip] >>
  metis_tac[]
QED

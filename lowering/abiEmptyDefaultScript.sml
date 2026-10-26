(* Actual default ABI bytes for statically laid out source values.
   These are byte equalities, independent of sparse val_in_memory predicates. *)
Theory abiEmptyDefault
Ancestors
  abiStaticLayoutProps abiStaticAggregateProps abiDecoderStructInputs abiEncoderMemory
  abiEmptyMemory abiEncoderInput exprLowering compileEnv valueEncoding vyperABI
  contractABI integer_word words list rich_list arithmetic

Theorem abi_empty_fixed_bytes_default:
  enc (Bytes (SOME n)) (BytesV (REPLICATE n 0w)) = REPLICATE 32 0w
Proof
  `TAKE 32 (REPLICATE n (0w:word8)) = REPLICATE (MIN 32 n) 0w` by
    simp[REPLICATE_GENLIST, TAKE_GENLIST] >>
  simp_tac bool_ss [enc_def] >> asm_rewrite_tac[] >>
  rewrite_tac[REPLICATE_APPEND] >> AP_THM_TAC >> AP_TERM_TAC >>
  rw[MIN_DEF] >> decide_tac
QED

Theorem abi_empty_bytes_default:
  enc (vyper_base_to_abi_type (BytesT bd)) (default_to_abi (BaseTV (BytesT bd))) =
    REPLICATE 32 0w
Proof
  Cases_on `bd` >> simp[default_to_abi_def, abi_empty_fixed_bytes_default,
    abi_encoder_zero_word, enc_def, enc_number_def, ceil32_def]
QED

Theorem abi_empty_base_default:
  enc (vyper_base_to_abi_type bt) (default_to_abi (BaseTV bt)) = REPLICATE 32 0w
Proof
  Cases_on `bt` >> simp[default_to_abi_def, abi_empty_bytes_default,
    abi_encoder_zero_word, enc_def, enc_number_def, ceil32_def, i2w_0]
QED

Theorem abi_empty_flat_zero:
  !n. FLAT (REPLICATE n (REPLICATE m (0w:word8))) = REPLICATE (n*m) 0w
Proof
  Induct >> simp[REPLICATE_APPEND, MULT_CLAUSES]
QED

Theorem abi_empty_default_list:
  !tys tvs. LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    enc (vyper_to_abi_type tenv ty) (default_to_abi tv) =
      REPLICATE (type_memory_size tv) 0w) tys tvs ==>
  ~any_dynamic (vyper_to_abi_types tenv tys) /\
  LENGTH (vyper_to_abi_types tenv tys) = LENGTH (default_to_abi_list tvs) /\
  FLAT (MAP2 enc (vyper_to_abi_types tenv tys) (default_to_abi_list tvs)) =
    REPLICATE (type_memory_size_list tvs) 0w
Proof
  Induct >> Cases_on `tvs` >>
  simp[default_to_abi_def, type_memory_size_def, is_dynamic_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[REPLICATE_APPEND]
QED

Theorem abi_empty_default_tuple:
  LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    enc (vyper_to_abi_type tenv ty) (default_to_abi tv) =
      REPLICATE (type_memory_size tv) 0w) tys tvs ==>
  enc (Tuple (vyper_to_abi_types tenv tys)) (ListV (default_to_abi_list tvs)) =
    REPLICATE (type_memory_size_list tvs) 0w
Proof
  strip_tac >> drule abi_empty_default_list >> strip_tac >>
  drule_all enc_static_tuple >> simp[]
QED

Theorem abi_empty_static_default:
  !cenv tenv ty tv. static_layout_compatible cenv tenv ty tv ==>
  enc (vyper_to_abi_type tenv ty) (default_to_abi tv) = REPLICATE (type_memory_size tv) 0w
Proof
  ho_match_mp_tac static_layout_compatible_strongind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (simp_tac bool_ss [vyper_to_abi_type_def, abi_empty_base_default] >>
      Cases_on `bt` >> gvs[is_word_type_def, type_memory_size_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, type_memory_size_def])
  >- simp[default_to_abi_def, enc_def, enc_number_def,
    type_memory_size_def, abi_encoder_zero_word]
  >- (drule static_layout_compatible_properties >> strip_tac >>
      simp[default_to_abi_def, enc_static_array, map_replicate,
        abi_empty_flat_zero, type_memory_size_def])
  >- (pure_rewrite_tac[default_to_abi_def, type_memory_size_def, vyper_to_abi_type_def] >>
      irule abi_empty_default_tuple >> qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac >>
      drule static_layout_compatible_properties >> simp[])
  >> `LENGTH (MAP FST args) = LENGTH tvs` by
       (imp_res_tac LIST_REL_LENGTH >> gvs[])
  >> drule type_memory_size_fields_zip >> strip_tac
  >> asm_simp_tac bool_ss [default_to_abi_def, type_memory_size_def, vyper_to_abi_type_def]
  >> asm_simp_tac (srw_ss()) [default_to_abi_fields_MAP, default_to_abi_list_MAP,
       MAP_ZIP, Excl "enc_def"]
  >> irule (REWRITE_RULE [default_to_abi_list_MAP] abi_empty_default_tuple)
  >> qpat_x_assum `LIST_REL _ _ _` mp_tac
  >> match_mp_tac LIST_REL_mono >> simp[] >> rpt strip_tac
  >> drule static_layout_compatible_properties >> simp[]
QED

Theorem abi_empty_static_descriptor:
  static_layout_compatible ce tenv ty tv ==>
  type_to_abi_enc_info sf ce ty = AbiCopy (type_memory_bytes ce ty)
Proof
  strip_tac >>
  `ty <> NoneT` by (strip_tac >> gvs[Once static_layout_compatible_cases]) >>
  drule static_layout_compatible_properties >> strip_tac >>
  Cases_on `ty` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def] >>
  FIRST [rename1 `BaseT bt` >> Cases_on `bt`, ALL_TAC] >>
  FIRST [rename1 `BytesT bd` >> Cases_on `bd`, ALL_TAC] >>
  FIRST [rename1 `ArrayT elem bd` >> Cases_on `bd`, ALL_TAC] >>
  gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]
QED

Theorem abi_empty_static_input:
  static_layout_compatible ce tenv ty tv /\
  has_type (vyper_to_abi_type tenv ty) (default_to_abi tv) /\
  mem_bytes_at p (type_memory_bytes ce ty) mem = REPLICATE (type_memory_bytes ce ty) 0w /\
  type_memory_bytes ce ty <= cap ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type tenv ty)
    (default_to_abi tv) p cap mem
Proof
  strip_tac >> drule abi_empty_static_descriptor >> strip_tac >>
  drule abi_empty_static_default >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  asm_rewrite_tac[] >> irule abi_empty_zero_copy_input >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_DEFAULT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty default bytes not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyDefault");

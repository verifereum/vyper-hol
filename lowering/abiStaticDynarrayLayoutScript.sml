(* Canonical static element payloads in a dynamic array's memory layout. *)
Theory abiStaticDynarrayLayout
Ancestors
  abiStaticReverseProps abiStaticAggregateProps abiStaticLayoutProps
  abiDecoderTypedContract valueEncoding vyperABI vyperTyping contractABI
  list rich_list arithmetic

Theorem mem_bytes_at_append_parts:
  !off prefix suffix mem.
  mem_bytes_at off (LENGTH (prefix ++ suffix)) mem = prefix ++ suffix ==>
  mem_bytes_at off (LENGTH prefix) mem = prefix /\
  mem_bytes_at (off + LENGTH prefix) (LENGTH suffix) mem = suffix
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qspecl_then [`off`, `[]`, `prefix`, `suffix`, `mem`]
        mp_tac abi_decoder_source_subwindow >> gvs[]) >>
  drule abi_decoder_source_prefix >> simp[]
QED

Theorem static_same_canonical_layout:
  !ce env ty tv. static_layout_compatible ce env ty tv ==>
  !vs avs. all_have_type tv vs /\ vyper_to_abi_same env ty vs = SOME avs ==>
  LENGTH avs = LENGTH vs /\
  LENGTH (FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)) =
    LENGTH vs * type_memory_size tv /\
  !off mem.
    mem_bytes_at off (LENGTH vs * type_memory_size tv) mem =
      FLAT (MAP (enc (vyper_to_abi_type env ty)) avs) ==>
    elems_in_memory vs off tv mem
Proof
  rpt gen_tac >> strip_tac >> Induct_on `vs`
  >- simp[vyper_to_abi_def, value_has_type_def, val_in_memory_def] >>
  qx_gen_tac `v` >> rpt gen_tac >> strip_tac >>
  gvs[Once vyper_to_abi_def, value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  rename1 `vyper_to_abi env ty v = SOME av` >>
  rename1 `vyper_to_abi_same env ty vs = SOME rest_avs` >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv` by
    (drule static_typed_encoding_length >>
     disch_then (qspecl_then [`v`, `av`] mp_tac) >> asm_simp_tac bool_ss []) >>
  simp[Excl "enc_def", MULT_CLAUSES] >> rpt gen_tac >> strip_tac >>
  `mem_bytes_at off
      (LENGTH (enc (vyper_to_abi_type env ty) av ++
        FLAT (MAP (enc (vyper_to_abi_type env ty)) rest_avs))) mem =
    enc (vyper_to_abi_type env ty) av ++
        FLAT (MAP (enc (vyper_to_abi_type env ty)) rest_avs)` by
    (asm_simp_tac arith_ss [LENGTH_APPEND]) >>
  drule mem_bytes_at_append_parts >> strip_tac >>
  qpat_assum `LENGTH (enc (vyper_to_abi_type env ty) av) = _` (fn head_th =>
    qpat_assum `LENGTH (FLAT (MAP (enc (vyper_to_abi_type env ty)) rest_avs)) = _`
      (fn tail_th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [head_th, tail_th]))) >>
  CONV_TAC (ONCE_REWRITE_CONV [val_in_memory_def]) >> conj_tac
  >- (drule static_canonical_memory_layout >>
      disch_then (qspecl_then [`v`, `av`, `off`, `mem`] mp_tac) >>
      asm_simp_tac bool_ss []) >>
  first_x_assum irule >> asm_simp_tac arith_ss []
QED

Theorem static_dynarray_canonical_layout:
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  mem_word_at d mem = n2w (LENGTH vs) /\
  mem_bytes_at (d + 32) (LENGTH vs * type_memory_size tv) mem =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs) ==>
  val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) d mem
Proof
  strip_tac >> simp[val_in_memory_def] >>
  drule_all static_same_canonical_layout >> simp[]
QED

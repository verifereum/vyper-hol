(* Typed source slices and output cells for arbitrary dynamic-array children. *)
Theory abiDecoderArrayChildSource
Ancestors
  abiDecoderArraySlice abiDecoderArrayChild abiDecoderArrayInvariant
  abiDecoderHeadAdequacy abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecodeRanges abiDecoderContract abiDecoderFrame vyperABI vyperValue vyperTyping
  compileEnv valueEncoding contractABI venomState words list rich_list arithmetic
Libs
  Omega

Theorem abi_decoder_slice_source_arithmetic:
  !sb off len total limit:num. off + len <= total /\ sb + total < limit ==>
  sb + off < limit /\ sb + off + len <= sb + total
Proof
  Omega.OMEGA_TAC
QED

Theorem abi_decoder_subwindow_ranges:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s /\
  sb <= childsb /\ childsb + childlen <= sb + len /\
  d <= childd /\ childd + childsz <= d + outsz /\
  eval_operand childsrc s = SOME (n2w childsb) /\
  eval_operand childdst s = SOME (n2w childd) ==>
  abi_decoder_ranges opc hi childsrc childdst childsb childlen childd childsz b cap s
Proof
  rw[abi_decoder_ranges_def] >>
  gvs[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (disj2_tac >> qexists_tac `h` >> simp[] >> decide_tac) >>
  TRY (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  decide_tac
QED

Theorem abi_decoder_dynarray_child_layout:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  has_type (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH (enc (vyper_to_abi_type env ty) av) /\
  abi_decoder_dynamic (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_size tv = type_memory_bytes ce ty /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * type_memory_bytes ce ty /\
  LENGTH pre < maxn
Proof
  strip_tac >> drule_all abi_decoder_dynarray_metadata_child >> strip_tac >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `has_type (vyper_to_abi_type env ty) av /\ type_memory_size tv = type_memory_bytes ce ty`
    by fs[abi_decoder_metadata_def] >>
  drule_all abi_decoder_array_child_head_adequate >> strip_tac >>
  drule_all abi_decoder_coherent_dynamic >> strip_tac >>
  `LENGTH pre < maxn` by fs[Excl "enc_def"] >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def]
QED

Theorem abi_decoder_dynarray_child_source:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  let off = abi_array_child_offset NONE (vyper_to_abi_type env ty)
      (pre ++ av::post) (LENGTH pre);
      cell = d + 32 + LENGTH pre * type_memory_bytes ce ty in
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  mem_bytes_at (sb + off) (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av /\
  sb + off < dimword (:256) /\
  sb + off + LENGTH (enc (vyper_to_abi_type env ty) av) <= sb +
    LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))) /\
  cell < dimword (:256) /\
  cell + type_memory_bytes ce ty <= d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH (enc (vyper_to_abi_type env ty) av)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decoder_dynarray_child_layout >> strip_tac >>
  drule_all abi_array_child_offset_source >> strip_tac >>
  drule abi_array_child_offset_ranges >> strip_tac >>
  `sb + abi_array_child_offset NONE (vyper_to_abi_type env ty)
      (pre ++ av::post) (LENGTH pre) < dimword (:256) /\
   sb + abi_array_child_offset NONE (vyper_to_abi_type env ty)
      (pre ++ av::post) (LENGTH pre) + LENGTH (enc (vyper_to_abi_type env ty) av) <=
     sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)))`
    by (irule abi_decoder_slice_source_arithmetic >> asm_simp_tac bool_ss []) >>
  `d + (32 + maxn * type_memory_bytes ce ty) < dimword (:256)`
    by (qpat_x_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < _` mp_tac >>
        asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_array_cell_window >> strip_tac >>
  gvs[Excl "enc_def"]
QED

Theorem abi_decoder_dynarray_child_pre:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  fresh_vars_wrt child_st s /\ abi_decoder_reservation child_st.cs_next_id last b cap s /\
  eval_operand childsrc s = SOME (n2w (sb + abi_array_child_offset NONE
    (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
  eval_operand childdst s = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    child_st last childsrc childdst opc hi
    (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
    (d + 32 + LENGTH pre * type_memory_bytes ce ty) b cap s
Proof
  strip_tac >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
       (ListV (pre ++ av::post))) < dimword (:256) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)`
    by (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
          (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
        asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_dynarray_child_source >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `sb <= sb + abi_array_child_offset NONE (vyper_to_abi_type env ty)
      (pre ++ av::post) (LENGTH pre)` by simp[] >>
  `d <= d + 32 + LENGTH pre * type_memory_bytes ce ty` by
    (pure_rewrite_tac [GSYM ADD_ASSOC] >> irule LESS_EQ_ADD) >>
  asm_simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def] >>
  irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`,
    `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)))`,
    `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `sb`, `src`] >>
  gvs[Excl "enc_def"]
QED

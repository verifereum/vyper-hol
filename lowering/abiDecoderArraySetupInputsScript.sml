Theory abiDecoderArraySetupInputs
Ancestors
  abiDecoderArraySlice abiDecoderArrayAdvance abiDecoderArrayInvariant abiDecoderHeadAdequacy
  abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract abiDecodeRanges
  abiDecoderContract abiDecoderFrame vyperABI vyperValue vyperTyping compileEnv valueEncoding
  contractABI venomState words list rich_list arithmetic abiDecoderDynamicLoopSetup
  abiCanonicalHeadSize abiDecoderOffset abiDecoderLoopSetup abiDecoderReentry
  abiDecoderReservation abiDecoderStaticLoopSetup venomExecSemantics emitHelperProps
Libs
  Omega

(* Typed source slices and output cells for arbitrary dynamic-array children. *)
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

(* Canonical parent bytes justify the actual dynamic-child setup guards. *)
Theorem abi_decoder_canonical_dynamic_setup_inputs:
  has_type (Array NONE aty) (ListV (pre ++ av::post)) /\ is_dynamic aty /\
  asz = abi_member_head_size aty /\ asz <= LENGTH (enc aty av) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV (pre ++ av::post))))
    (abi_decode_source opc s) = enc (Array NONE aty) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE aty) (ListV (pre ++ av::post))) < dimword (:256) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    sb + LENGTH (enc (Array NONE aty) (ListV (pre ++ av::post))) <= hb /\ hb < dimword (:256)) ==>
  abi_decode_load opc (n2w (sb + 32 + LENGTH pre * asz) : bytes32) s =
    n2w (LENGTH (pre ++ av::post) * abi_member_head_size aty +
      SUM (MAP (abi_member_tail_size aty) pre)) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    sb + 32 + (LENGTH (pre ++ av::post) * abi_member_head_size aty +
      SUM (MAP (abi_member_tail_size aty) pre)) + asz <= hb /\ hb < dimword (:256))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bound` |-> `NONE`] canonical_array_offset_load)) >> strip_tac >>
  drule (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`bound` |-> `NONE`] canonical_array_member_ranges)) >> strip_tac >>
  conj_tac >- gvs[Excl "enc_def"] >>
  Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem abi_decoder_dynarray_dynamic_setup:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand (SND (SND ops)) t =
      SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_dynarray_child_layout >> strip_tac >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)`
    by fs[abi_decoder_header_def] >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by
    (drule abi_decoder_array_child_offset >> simp[]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_decoder_canonical_dynamic_setup_inputs >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
  qexists_tac `t` >> gvs[abi_array_child_offset_append, Excl "enc_def"]
QED

Theorem abi_decoder_address_frame_source:
  abi_decoder_address_frame next s t ==> abi_decode_source opc t = abi_decode_source opc s
Proof
  rw[abi_decoder_address_frame_def] >> simp[abi_decode_source_def]
QED

Theorem abi_decoder_address_frame_ranges:
  abi_decoder_address_frame next s t /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s ==>
  abi_decoder_ranges opc hi src dst sb len d outsz b cap t
Proof
  rw[abi_decoder_ranges_def, abi_decoder_address_frame_def] >> metis_tac[]
QED

Theorem abi_decoder_address_frame_reservation:
  abi_decoder_address_frame next s t /\ abi_decoder_reservation first last b cap s ==>
  abi_decoder_reservation first last b cap t
Proof
  rw[abi_decoder_address_frame_def, abi_decoder_reservation_def]
QED

Theorem abi_decoder_array_setup_child_pre:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap before /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc before) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  abi_decoder_address_frame first before after /\ first <= child_st.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first dst /\
  abi_decoder_operand_live first hi /\
  abi_decoder_reservation child_st.cs_next_id last b cap before /\
  abi_decoder_operand_live child_st.cs_next_var childsrc /\
  abi_decoder_operand_live child_st.cs_next_var childdst /\
  eval_operand childsrc after = SOME (n2w (sb + abi_array_child_offset NONE
    (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
  eval_operand childdst after = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    child_st last childsrc childdst opc hi
    (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
    (d + 32 + LENGTH pre * type_memory_bytes ce ty) b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live child_st.cs_next_var src /\
   abi_decoder_operand_live child_st.cs_next_var dst /\
   abi_decoder_operand_live child_st.cs_next_var hi` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_reservation >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `fresh_vars_wrt child_st (abi_decoder_prune_vars child_st.cs_next_var after)`
    by irule abi_decoder_prune_fresh >>
  `abi_decoder_reservation child_st.cs_next_id last b cap
      (abi_decoder_prune_vars child_st.cs_next_var after)` by simp[] >>
  `abi_decoder_ranges opc hi src dst sb
      (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap
      (abi_decoder_prune_vars child_st.cs_next_var after)`
    by gvs[abi_decoder_prune_ranges, Excl "enc_def"] >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
      (abi_decode_source opc (abi_decoder_prune_vars child_st.cs_next_var after)) =
      enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))`
    by gvs[Excl "enc_def"] >>
  `eval_operand childsrc (abi_decoder_prune_vars child_st.cs_next_var after) =
      SOME (n2w (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty)
        (pre ++ av::post) (LENGTH pre))) /\
   eval_operand childdst (abi_decoder_prune_vars child_st.cs_next_var after) =
      SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty))`
    by gvs[abi_decoder_prune_eval, Excl "enc_def"] >>
  drule_all (Q.INST [`s` |-> `abi_decoder_prune_vars child_st.cs_next_var after`]
    abi_decoder_dynarray_child_pre) >> simp[]
QED

Theorem abi_decoder_dynarray_dynamic_child_inputs:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_reservation st'.cs_next_id last b cap s /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      st' last (FST (SND ops)) (SND (SND ops)) opc hi
      (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
      (d + 32 + LENGTH pre * type_memory_bytes ce ty) b cap
      (abi_decoder_prune_vars st'.cs_next_var t) /\
    eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_dynarray_dynamic_setup >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_decoder_coherent_array_iff, Excl "enc_def"] >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by
    (drule abi_decoder_array_child_offset >> simp[]) >>
  drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
  `st.cs_next_var <= st'.cs_next_var` by
    (Cases_on `hi = Lit 0w` >> gvs[Excl "enc_def"]) >>
  drule_all abi_decoder_array_setup_child_pre >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

Theorem abi_decode_array_element_setup_operands:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') ==>
  st.cs_next_var <= st'.cs_next_var /\
  abi_decoder_operand_live st'.cs_next_var (FST ops) /\
  abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live st'.cs_next_var (SND (SND ops))
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >- (drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
      Cases_on `hi = Lit 0w` >> gvs[]) >>
  drule_all abi_decode_static_element_setup_operands >> strip_tac >> gvs[]
QED

Theorem abi_decode_array_element_setup_shape:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di` >>
  FIRST [drule_all abi_decode_dynamic_element_setup_shape >> simp[],
         drule_all abi_decode_static_element_setup_shape >> simp[]]
QED

Theorem abi_decoder_dynarray_setup:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
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
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand (SND (SND ops)) t =
      SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (strip_tac >> drule_all abi_decoder_dynarray_dynamic_setup >> simp[]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_decoder_coherent_array_iff, Excl "enc_def"] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `~dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by
    (drule abi_decoder_array_child_offset >> simp[]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_array_child_offset_append, abi_decoder_header_def, abi_decoder_address_frame_def,
      Excl "enc_def"] >> metis_tac[]
QED

Theorem abi_decoder_dynarray_child_inputs:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
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
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_reservation st'.cs_next_id last b cap s /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      st' last (FST (SND ops)) (SND (SND ops)) opc hi
      (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
      (d + 32 + LENGTH pre * type_memory_bytes ce ty) b cap
      (abi_decoder_prune_vars st'.cs_next_var t) /\
    eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_dynarray_setup >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  drule_all abi_decoder_array_setup_child_pre >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

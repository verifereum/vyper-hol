Theory entryReachBodySourceMemberEntry
Ancestors
  entryReachBodyMemberInputs entryReachBodySourceMemory entryReachBodySourceLayout
  entryReachBodyMemberSetup abiDecoderCoherence abiDecoderMembers
  entryReachBodyOwnedRegion abiDecoderArraySetupInputs
  abiCanonicalHeadSize abiDecoderMemberBody abiDecoderMemberSlice entryReachBodyLayoutWindows
  abiDecodeRanges contractABI list rich_list arithmetic words byte
  valueEncodingProps valueEncodingProofs valueEncoding

Definition entry_source_metadata_def:
  entry_source_metadata ce env sf ty tv di av v <=>
    entry_abi_support env ty /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    di = type_to_abi_dec_info sf ce ty /\
    type_memory_size tv = type_memory_bytes ce ty
End

Definition entry_source_members_def:
  entry_source_members ce env sf [] [] [] [] = T /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) =
    (abi_decoder_coherent ce env sf ty tv /\
     entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v /\
     entry_source_members ce env sf tys tvs avs vs) /\
  entry_source_members ce env sf _ _ _ _ = F
End

Theorem entry_source_members_layout[local]:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  LIST_REL abi_encoder_layout_valid (MAP (vyper_to_abi_type env) tys) avs /\
  LENGTH tys = LENGTH avs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def, entry_source_metadata_def] >>
  rpt strip_tac >> simp[] >>
  metis_tac[entry_source_conversion_layout]
QED

Theorem entry_layout_member_offset_load[local]:
  LIST_REL abi_encoder_layout_valid (pre ++ aty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic aty /\
  E = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at sb (LENGTH E) (abi_decode_source opc s) = E /\
  sb + LENGTH E < dimword (:256) ==>
  abi_decode_load opc
    (n2w (sb + SUM (MAP abi_member_head_size pre)) : 256 word) s =
    n2w (head_lengths (pre ++ aty::post) 0 +
         SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all entry_layout_member_head_window >>
  simp_tac bool_ss [LET_THM] >>
  asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >>
  `SUM (MAP abi_member_head_size pre) + 32 <= LENGTH E` by
    (qpat_x_assum `TAKE 32 _ = _` (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
     pure_rewrite_tac [LENGTH_TAKE_EQ, LENGTH_DROP] >>
     asm_simp_tac (srw_ss()) [Excl "enc_def"] >> decide_tac) >>
  `sb + SUM (MAP abi_member_head_size pre) < dimword (:256)` by decide_tac >>
  drule_all abi_decode_load_window >>
  disch_then (qspecl_then [`s`, `opc`] SUBST1_TAC) >>
  asm_rewrite_tac[] >>
  asm_simp_tac bool_ss [enc_number_def] >>
  irule word_of_bytes_word_to_bytes >> simp[dividesTheory.divides_def]
QED

Theorem entry_layout_member_inputs[local]:
  LIST_REL abi_encoder_layout_valid (pre ++ aty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest))))
    (abi_decode_source CALLDATALOAD s) = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) /\
  sb + LENGTH (enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest))) < dimword (:256) /\
  off = abi_tuple_child_offset (pre ++ aty::post) (pvs ++ av::rest) (LENGTH pre) /\
  ao = SUM (MAP abi_member_head_size pre) ==>
  (is_dynamic aty ==>
    abi_decode_load CALLDATALOAD (n2w (sb+ao) : bytes32) s = n2w off /\
    sb+off < dimword (:256)) /\
  off = (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs)
         else ao) /\
  mem_bytes_at (sb+off) (LENGTH (enc aty av)) (abi_decode_source CALLDATALOAD s) =
    enc aty av /\
  sb+off+LENGTH (enc aty av) < dimword (:256)
Proof
  strip_tac >>
  `TAKE (LENGTH pre) (pvs ++ av::rest) = pvs` by
    metis_tac[TAKE_LENGTH_APPEND] >>
  `off = (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
            SUM (MAP2 abi_member_tail_size pre pvs) else ao)` by
    asm_simp_tac bool_ss [abi_tuple_child_offset_append] >>
  `mem_bytes_at (sb+off) (LENGTH (enc aty av)) (abi_decode_source CALLDATALOAD s) =
     enc aty av /\ sb+off+LENGTH (enc aty av) < dimword (:256)` by
    metis_tac[entry_layout_member_source] >>
  `sb+off < dimword (:256)` by decide_tac >>
  conj_tac
  >- (strip_tac >> metis_tac[entry_layout_member_offset_load]) >>
  asm_rewrite_tac[]
QED

Theorem entry_source_members_child_facts[local]:
  entry_source_members ce env sf pretys pretvs preavs prevs /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  ats = MAP (vyper_to_abi_type env) (pretys ++ ty::tys) /\
  vals = preavs ++ av::avs /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  outsz = SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) /\
  ei = type_to_abi_dec_info sf ce ty ==>
  LIST_REL abi_encoder_layout_valid ats vals /\
  LENGTH pretys = LENGTH preavs /\
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv ei av v /\
  vo + type_memory_size tv <= outsz
Proof
  strip_tac >>
  drule_all entry_source_members_layout >> strip_tac >>
  qpat_assum `entry_source_members _ _ _ (ty::tys) _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_source_members_def]) >>
  drule_all entry_source_members_layout >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid
      (MAP (vyper_to_abi_type env) pretys) preavs` by
    metis_tac[entry_source_members_layout] >>
  `LIST_REL abi_encoder_layout_valid
      (MAP (vyper_to_abi_type env) tys) avs` by
    metis_tac[entry_source_members_layout] >>
  `abi_encoder_layout_valid (vyper_to_abi_type env ty) av` by
    (fs[entry_source_metadata_def] >> metis_tac[entry_source_conversion_layout]) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    fs[entry_source_metadata_def] >>
  `LENGTH pretys = LENGTH preavs` by metis_tac[entry_source_members_layout] >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, LIST_REL_def] >>
  simp[SUM_APPEND, MAP_APPEND] >>
  simp[LIST_REL_APPEND_EQ, LIST_REL_def]
QED

Theorem entry_source_member_owned_entry:
  !ats vals off ao vo outsz ei.
  entry_source_members ce env sf pretys pretvs preavs prevs /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  ats = MAP (vyper_to_abi_type env) (pretys ++ ty::tys) /\ vals = preavs ++ av::avs /\
  off = abi_tuple_child_offset ats vals (LENGTH pretys) /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  outsz = SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) /\
  ei = type_to_abi_dec_info sf ce ty /\
  dec_info_needs_offset ei = is_dynamic (vyper_to_abi_type env ty) /\
  mem_bytes_at sb (LENGTH (enc (Tuple ats) (ListV vals)))
    (abi_decode_source CALLDATALOAD s) = enc (Tuple ats) (ListV vals) /\
  sb + LENGTH (enc (Tuple ats) (ListV vals)) < dimword (:256) /\
  d + outsz < dimword (:256) /\ entry_owned_region oid root extent d outsz s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (dec_info_needs_offset ei) ao vo st = (ops,mid) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w (sb+off)) /\
    eval_operand (SND ops) u = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) av))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ty) av /\
    sb+off+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    d+vo+type_memory_size tv < dimword (:256) /\
    abi_decoder_coherent ce env sf ty tv /\
    entry_source_metadata ce env sf ty tv ei av v /\
    entry_owned_region oid root extent (d+vo) (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_source_members_child_facts >> strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [MAP_APPEND, MAP, LENGTH_MAP]) >>
  qpat_x_assum `ats = _` SUBST_ALL_TAC >>
  qpat_x_assum `vals = _` SUBST_ALL_TAC >>
  drule_all (PURE_REWRITE_RULE [LENGTH_MAP]
    (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`] entry_layout_member_inputs)) >>
  strip_tac >>
  qpat_x_assum `entry_source_members _ _ _ pretys _ _ _` kall_tac >>
  qpat_x_assum `entry_source_members _ _ _ (ty::tys) _ _ _` kall_tac >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  qpat_x_assum `off = abi_tuple_child_offset _ _ _` kall_tac >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` kall_tac >>
  qpat_x_assum `sb + LENGTH _ < _` kall_tac >>
  qpat_x_assum `dec_info_needs_offset ei = _` SUBST_ALL_TAC >>
  drule_all entry_member_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `entry_scratch_ready sites b cap u /\
   entry_owned_region oid root extent d outsz u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists_tac `s` >> simp[]) >>
  `abi_decode_source CALLDATALOAD u = abi_decode_source CALLDATALOAD s` by
    (irule abi_decoder_address_frame_source >> goal_assum (drule_at Any)) >>
  `eval_operand (FST ops) u = SOME (n2w (sb+off))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >> gvs[]) >>
  `d+vo+type_memory_size tv < dimword (:256)` by decide_tac >>
  `entry_owned_region oid root extent (d+vo) (type_memory_size tv) u` by
    (qpat_x_assum `entry_owned_region oid root extent d outsz u` mp_tac >>
     simp_tac bool_ss [entry_owned_region_def] >> strip_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  qexists_tac `u` >> asm_rewrite_tac[] >>
  qpat_x_assum `mem_bytes_at (sb+off) _ _ = _` mp_tac >> asm_rewrite_tac[]
QED

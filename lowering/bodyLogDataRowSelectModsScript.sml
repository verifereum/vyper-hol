(* The Log tuple's index is the rank among non-indexed arguments. *)
Theory bodyLogDataRowSelectMods
Ancestors
  bodyAbiEncodePackedPostMods abiEncodeValuesMetadata abiDecoderMembers
  eventLogSplitProps typedLogSplitComplete abiLogSourceEncoding
  vyperABIRoundtrip exprLowering compileEnv vyperContext
  contractABI list rich_list pair arithmetic

Theorem log_select_length[local]:
  !flags xs. LENGTH flags = LENGTH xs ==>
    LENGTH (select_log_args F flags xs) = LENGTH (FILTER ($= F) flags)
Proof
  Induct >- (Cases_on `xs` >> simp[select_log_args_def]) >>
  qx_gen_tac `flag` >> Cases_on `flag` >> Cases_on `xs` >>
  simp[select_log_args_def]
QED

Theorem log_select_rank[local]:
  !flags i. i < LENGTH (FILTER ($= F) flags) ==>
    ?j. j < LENGTH flags /\ EL j flags = F /\
      LENGTH (FILTER ($= F) (TAKE j flags)) = i
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[]
  >- (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
      qexists `SUC j` >> simp[rich_listTheory.TAKE]) >>
  Cases_on `i` >- (simp[] >> qexists `0` >> simp[]) >>
  simp[] >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
  qexists `SUC j` >> simp[rich_listTheory.TAKE]
QED

Theorem log_select_rank_el[local]:
  !flags xs j. LENGTH flags = LENGTH xs /\ j < LENGTH flags /\ EL j flags = F ==>
    EL (LENGTH (FILTER ($= F) (TAKE j flags))) (select_log_args F flags xs) = EL j xs
Proof
  Induct >> simp[] >> qx_gen_tac `flag` >> Cases_on `flag` >> Cases_on `xs` >>
  Cases_on `j` >> simp[select_log_args_def, rich_listTheory.TAKE]
QED

Theorem log_data_row_select_mods:
  rows = SND (split_log_ops (ZIP (saved,atys)) flags) /\
  atys = MAP (lowered_value_type ce) args /\
  LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\
  LENGTH flags = LENGTH vs /\ i < LENGTH rows /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    LIST_REL (\(e,sv) v. ?si sm ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa sb e sv v si sm ss vv copy H ee G tn t)
      (select_log_args F flags (ZIP (args,saved))) (select_log_args F flags vs)) /\
  ats = vyper_to_abi_types (get_tenv cx) (log_non_indexed_types flags atys) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags atys)
    (log_non_indexed_values flags vs) = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)) /\
  hl = head_lengths ats 0 /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= capacity ==>
  ?j e sv ty v at av.
    j < LENGTH flags /\ EL j flags = F /\
    LENGTH (FILTER ($= F) (TAKE j flags)) = i /\
    e = EL j args /\ sv = EL j saved /\ ty = EL j atys /\ v = EL j vs /\
    ty = lowered_value_type ce e /\ EL i rows = (sv,ty) /\
    EL i (select_log_args F flags vs) = v /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> ?si sm ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa sb e sv v si sm ss vv copy H ee G tn t) /\
    i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
    at = EL i ats /\ av = EL i avs /\
    at = vyper_to_abi_type (get_tenv cx) ty /\
    vyper_to_abi (get_tenv cx) ty v = SOME av /\
    h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
    hl <= off /\ off <= capacity /\ h + abi_member_head_size at <= hl /\
    (is_dynamic at ==> off + LENGTH (enc at av) <= capacity) /\
    (~is_dynamic at ==> LENGTH (enc at av) = abi_member_head_size at) /\
    abi_encoder_layout_valid at av /\
    LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH flags = LENGTH atys` by simp[] >>
  `LENGTH flags = LENGTH (ZIP (saved,atys))` by simp[LENGTH_ZIP] >>
  `rows = select_log_args F flags (ZIP (saved,atys))` by
    (drule split_log_ops_select >> simp[]) >>
  `LENGTH rows = LENGTH (FILTER ($= F) flags)` by simp[log_select_length] >>
  `i < LENGTH (FILTER ($= F) flags)` by decide_tac >>
  drule log_select_rank >> strip_tac >>
  `EL i rows = (EL j saved,EL j atys)` by
    (qspecl_then [`flags`,`ZIP (saved,atys)`,`j`] mp_tac log_select_rank_el >>
     simp[EL_ZIP]) >>
  `LENGTH flags = LENGTH (ZIP (args,saved))` by simp[LENGTH_ZIP] >>
  `EL i (select_log_args F flags (ZIP (args,saved))) = (EL j args,EL j saved)` by
    (qspecl_then [`flags`,`ZIP (args,saved)`,`j`] mp_tac log_select_rank_el >>
     simp[EL_ZIP]) >>
  `EL i (select_log_args F flags atys) = EL j atys` by
    (qspecl_then [`flags`,`atys`,`j`] mp_tac log_select_rank_el >> simp[]) >>
  `EL i (select_log_args F flags vs) = EL j vs` by
    (qspecl_then [`flags`,`vs`,`j`] mp_tac log_select_rank_el >> simp[]) >>
  `i < LENGTH (select_log_args F flags (ZIP (args,saved))) /\
   i < LENGTH (select_log_args F flags vs)` by simp[log_select_length] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ?si sm ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa sb (EL j args) (EL j saved) (EL j vs)
        si sm ss vv copy H ee G tn t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> LIST_REL _ _ _`
       (drule_then (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN])) >>
     disch_then (qspec_then `i` mp_tac o cj 2) >> simp[]) >>
  `LENGTH rows = LENGTH ats /\ LENGTH ats = LENGTH avs` by
    metis_tac[LIST_REL_LENGTH] >>
  `i < LENGTH ats` by decide_tac >>
  `i < LENGTH (select_log_args F flags atys)` by simp[log_select_length] >>
  `EL j atys = lowered_value_type ce (EL j args)` by simp[EL_MAP] >>
  qpat_x_assum `atys = MAP _ _` kall_tac >>
  `EL i ats = vyper_to_abi_type (get_tenv cx) (EL j atys)` by
    simp[log_non_indexed_types_select, vyper_to_abi_types_MAP, EL_MAP] >>
  `vyper_to_abi (get_tenv cx) (EL j atys) (EL j vs) = SOME (EL i avs)` by
    (drule vyper_to_abi_list_EL >>
     disch_then (qspec_then `i` mp_tac o cj 3) >>
     simp[log_non_indexed_types_select, log_non_indexed_values_select]) >>
  `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
   hl <= off /\ off <= LENGTH (enc (Tuple ats) (ListV avs)) /\
   h + abi_member_head_size (EL i ats) <= hl /\
   (is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <=
     LENGTH (enc (Tuple ats) (ListV avs))) /\
   (~is_dynamic (EL i ats) ==> LENGTH (enc (EL i ats) (EL i avs)) =
     abi_member_head_size (EL i ats)) /\
   abi_encoder_layout_valid (EL i ats) (EL i avs) /\
   LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abi_encode_values_index_bounds) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
     qexistsl [`rows`,`ce.ce_struct_fields`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum strip_assume_tac >>
  qexistsl [`j`,`EL j args`,`EL j saved`,`EL j atys`,`EL j vs`,`EL i ats`,`EL i avs`] >>
  rpt conj_tac >> TRY REFL_TAC >> TRY (first_assum ACCEPT_TAC)
  >- decide_tac >>
  disch_tac >>
  qpat_assum `is_dynamic _ ==> _` (drule_then assume_tac) >> decide_tac
QED

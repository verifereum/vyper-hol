(* With no unwrap instructions, the saved operand keeps its original interval. *)
Theory bodyAbiTupleIdentityRestoreMods
Ancestors
  bodyAbiTupleCaptureMods bodyAbiTupleUnwrapLiftMods bodyAbiEncodeSavedMemoryMods
  abiEncodeValuesPrefixFrame exprSafeOperand exprLowering compileEnv
  bodyAbiEncodePackedPostMods bodyAbiTupleBufferStateMods


Theorem abi_tuple_identity_restore_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin se e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s) /\
  valid_horizon cx st0 H ee.storage_trace /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl dest cursor cursor_site slot i a u Gu tu /\
  (!l. vv_operand saved <> Label l) /\
  unwrap_value ce saved a = (src,r) /\ fn_has_code a r func /\
  ty = lowered_value_type ce e /\
  ((?tag op. saved = StackValue tag op) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) ==>
  r = a /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix r u Gu tu /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu r u Gu tu /\
  abi_encode_values_prefix_at ats avs hl dest cursor cursor_site slot i r u Gu tu /\
  ss.cs_next_id <= shared /\
  expr_val_at ce cx ty si ss ee v src u /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\
  expr_store_bound cx ty v src u /\
  (!x. src = Var x ==> not_fresh_at r x) /\
  !D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK u,Gu,tu)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) abi_tuple_saved_capture_transport_mods >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy h ee Gu tu u /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `r = a` by
    (qpat_x_assum `ty = lowered_value_type ce e` kall_tac >>
     qpat_x_assum `unwrap_value ce saved a = (src,r)` mp_tac >>
     qpat_assum `(?tag op. saved = StackValue tag op) \/ _`
       (DISJ_CASES_THEN strip_assume_tac) >>
     simp[unwrap_value_def, comp_return_def]) >>
  qpat_x_assum `r = a` SUBST_ALL_TAC >>
  qpat_assum `safe_operand a src` (strip_assume_tac o REWRITE_RULE [safe_operand_def]) >>
  `ss.cs_next_id <= shared` by
    (qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==>
        abi_encode_saved_row_mods lo ce cx origin se e saved v si sm ss vv copy h ee G tn s /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def])) >>
     qhdtm_assum `abi_tuple_buffer_state_mods`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
     irule arithmeticTheory.LESS_EQ_TRANS >> qexists `se.cs_next_id` >> asm_rewrite_tac[]) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `?raw. read_result _ raw _ = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `ty = lowered_value_type ce e` SUBST_ALL_TAC >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    (SIMP_RULE bool_ss []
      (Q.INST [`ty` |-> `lowered_value_type ce e`] abi_encode_saved_memory_restore_mods)) >>
  conj_tac >- REFL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qhdtm_assum `abi_tuple_buffer_state_mods`
       (mp_then Any
          (qspec_then `cursor_site` (map_every assume_tac o CONJUNCTS))
          abi_tuple_unwrap_identity_mods) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  (simp[])
QED

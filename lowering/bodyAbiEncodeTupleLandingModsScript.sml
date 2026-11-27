(* Execute the wrapped encoder once at the linked ABI setup landing. *)
Theory bodyAbiEncodeTupleLandingMods
Ancestors
  bodyAbiEncodeTupleExitLandingMods bodyAbiEncodeTupleLayoutMods
  bodyAbiEncodeTupleRowStepMods bodyAbiTupleLinkedLoopMods
  bodyAbiEncodePackedPostMods bodyAbiTupleBufferStateMods
  exprBodyPreProps exprSimHypsDefs exprLowering exprSimProps typedMemoryCopy
  vyperStorageFootprint venomInst loweringStateRelDefs freshWrites
  finite_map list arithmetic pair
Libs horizonTypeLib

Theorem abi_encode_tuple_landing_mods:
  ~(LENGTH args = 1 /\ ~ensure) /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
      args svs sa st es s0 G0 tn0 H (INL vs : value list + 'err) ee G tn s) /\
  compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) svs
    (MAP (lowered_value_type ce) args) (Var dp) ready = (len,body_end) /\
  fn_has_code ready body_end func /\ fn_inst_ids_distinct func /\
  prefix = abi_encode_method_id_bytes mid /\ k = LENGTH prefix /\
  cap = 32 + 32 * word_size (abi_size_bound ce.ce_struct_fields
    (TupleT (MAP (lowered_value_type ce) args)) + k) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
  st.cs_next_id < ready.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  lo <= p /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  wb_frame ce es ee sa s0 pre /\
  (~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre) /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p cap root dp (32+k) prefix ready pre Gpre tnpre ==>
  ?bytes limit q Gq tq.
    abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
      ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
      (body_end,st.cs_next_id,p,cap,root,len) (bytes,limit,q,Gq,tq)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _` (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_packed_post_mods mods DF lo d ctx func ce cx env args svs sa st es s0 G0 tn0 H _ ee G tn s`
    (drule_then (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_packed_post_mods_def])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_packed_post_mods mods DF lo d ctx func ce cx env args svs sa st es s0 G0 tn0 H _ ee G tn s`
       (drule_then (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_packed_post_mods_def])) >>
     first_assum ACCEPT_TAC) >>
  drule_all abi_encode_tuple_layout_mods >> pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`avs`,`ats`,`bytes`,`limit`] (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `compile_abi_encode_values_to_buf ce (Var dp) (ZIP (svs,MAP (lowered_value_type ce) args))
    ready = (len,body_end)` by
    (qpat_assum `compile_abi_encode_payload _ _ _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac [compile_abi_encode_payload_def] >>
     qpat_assum `~(LENGTH args = 1 /\ ~ensure)`
       (fn th => simp_tac bool_ss [th])) >>
  qabbrev_tac `tys = MAP (lowered_value_type ce) args` >>
  qabbrev_tac `rows = ZIP (svs,tys)` >>
  qabbrev_tac `hl = head_lengths ats 0` >>
  qabbrev_tac `owner = mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)] [root]` >>
  `MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
   owner.inst_id = st.cs_next_id /\ owner.inst_outputs = [root]` by
    (simp[Abbr `owner`,mk_inst_def]) >>
  pop_assum (MAP_EVERY assume_tac o CONJUNCTS) >>
  suspend "setup"
QED

Resume abi_encode_tuple_landing_mods[setup]:
  `LENGTH (abi_encode_method_id_bytes mid ++ bytes) = k + LENGTH bytes` by
    (qpat_assum `prefix = _` (mp_tac o SYM) >>
     simp_tac bool_ss [LENGTH_APPEND] >> disch_then SUBST1_TAC >> decide_tac) >>
  `32 + LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= cap` by
    (qspec_then `abi_size_bound ce.ce_struct_fields (TupleT tys) + k` mp_tac le_word_size_mul >>
     decide_tac) >>
  `LENGTH (enc (Tuple ats) (ListV avs)) <= cap - (32+k)` by
    (qpat_assum `bytes = _` (SUBST1_TAC o SYM) >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `!j. j < LENGTH tys ==> ?tv. evaluate_type (get_tenv cx) (EL j tys) = SOME tv /\
    value_has_type tv (EL j vs) /\ type_memory_bytes ce (EL j tys) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH tys ==> ?tv ftv. _` (drule_then strip_assume_tac) >>
     qexists `tv` >> asm_rewrite_tac[]) >>
  `?E0. get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
    (!t rt. evaluate_type E0 t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt)` by
    (qexists `get_tenv cx` >> simp_tac (srw_ss()) [] >>
     drule_then assume_tac expr_body_pre_mods_inv >>
     qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
     conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
     irule typed_copy_memory_size >> qexists `get_tenv cx` >> asm_rewrite_tac[] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  suspend "loop"
QED

Resume abi_encode_tuple_landing_mods[loop]:
  `hl = head_lengths ats 0` by simp_tac bool_ss [Abbr `hl`] >>
  drule_at (Pat `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_tuple_linked_loop_with_cursor_mods >>
  disch_then (drule_at (Pat `compile_abi_encode_values_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `LIST_REL abi_encoder_layout_valid _ _`)) >>
  disch_then (drule_at (Pat `hl = head_lengths _ 0`)) >>
  disch_then (drule_at (Pat `_ = enc (Tuple _) (ListV _)`)) >>
  disch_then (drule_at (Pat `_.inst_outputs = [_]`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- suspend "callback") >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`bytes`,`limit`,`q`,`Gq`,`tq`] >>
  irule (horizonTypeLib.at_horizon_named "H0" abi_encode_tuple_exit_landing_mods) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists `owner` >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qexists `H0` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`dp`,`k`,`prefix`,`ready`,`s`,`tn`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_tuple_landing_mods[callback]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`ci`,`cursor_var`] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qx_genl_tac [`i`,`a`,`c`,`u`,`Gu`,`tu`,`cursor`,`slot`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`se` |-> `st`, `pbase` |-> `p`, `capacity` |-> `cap`,
    `dst` |-> `dp`] (INST_TYPE [alpha |-> ``:'err``] abi_encode_tuple_row_step_mods)) >>
  (impl_tac >-
     (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [markerTheory.Abbrev_def])) >>
      qexists `E0` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise abi_encode_tuple_landing_mods

Theory createCtorEncoderLength
Ancestors
  bodyFullExtCallDirectEncode bodyFullExtCallDirectRow bodyFullExtCallPosList
  bodyFullExtCallDirectState abiEncodeSnapshotOperandProps abiEncodeValuesMetadata abiEncodeValuesRun
  exprSimHyps assignPlaceOperandFacts exprSafeOperand abiBuiltinAllocation
  abiEncodeArgsCase entryDecodeStaticProps abiDecoderMembers vyperABIRoundtrip
  exprBodyPreProps context emitHelper loweringShapeRules aggregateEvaluatedLayout
  vyperTypeArgFits emitHelperProps exprLowering loweringPosts exprSimWordArgs
  compileEnv contractABI vyperABI vyperValue fragGasOriginPtr
  vyperStorageTrace venomState venomInst list rich_list pair arithmetic
Libs pairLib horizonTypeLib

Theorem ctor_encoder_physical_size[local]:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ann ==>
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  (~is_word_type (lowered_value_type ce e) ==> ~is_word_type (expr_type e))
Proof
  strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size, exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `is_word_type (lowered_value_type ce e) = is_word_type (expr_type e)` by
    metis_tac[arg_type_fits_word_type] >>
  asm_rewrite_tac[] >> Cases_on `is_word_type (expr_type e)` >> gvs[]
  >- (`type_memory_bytes ce (lowered_value_type ce e) = 32` by
        metis_tac[word_type_dec_sizes] >> gvs[] >> decide_tac) >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  drule (cj 1 abi_args_fits_memory_bytes) >>
  disch_then (qspec_then `ce` mp_tac) >> simp[] >>
  qpat_x_assum `type_memory_size ann < _` mp_tac >> simp[] >> decide_tac
QED

Theorem ctor_positional_row_at[local]:
  extcall_positional_post keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
    H (INL vs) ee G tn s ==>
  !i e sv v. i < LENGTH args /\ e = EL i args /\ sv = EL i svs /\ v = EL i vs ==>
  stmt_state_rel H ctx func ce cx ee s /\
  expr_sim_inv ce cx env ee /\
  vv_storage_live H cx sv ee s /\
  ?si sm ss vv raw copy.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
    local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\
    sm.cs_next_id <= se.cs_next_id /\ ss.cs_next_var <= se.cs_next_var /\
    ss.cs_next_id <= se.cs_next_id /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    ((?tag op. sv = StackValue tag op) \/
     (?p. sv = LocatedValue (lowered_value_type ce e) p /\
          ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
     (?p. sv = LocatedValue (lowered_value_type ce e) p /\
          ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
          lowered_value_type ce e = expr_type e /\ sv = vv)) /\
    read_result cx raw ee = (INL v,ee) /\
    vv_holds ce cx (lowered_value_type ce e) raw sv ee s /\
    vv_at ce cx (lowered_value_type ce e) si ss ee raw sv s /\
    ptr_vv_ok cx (lowered_value_type ce e) raw sv ee G tn s /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv s /\
    ((case sv of StackValue tag op => ~is_word_type (lowered_value_type ce e)
               | LocatedValue tag p => p.ptr_location = LocMemory) ==>
     ptr_buf_ok ce e (vv_operand sv) G s)
Proof
  simp_tac bool_ss [extcall_positional_post_def, sumTheory.INL_11] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `LIST_REL _ (ZIP (args,svs)) vs`
    (qspec_then `i` mp_tac o cj 2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  simp[LENGTH_ZIP, EL_ZIP] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`]
       (MAP_EVERY assume_tac o CONJUNCTS))
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`raw`,`copy`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `EL i svs` >> gvs[vv_operand_def]
QED

(* The row and fold laws carry a client fact on their own return witness. *)
Definition ctor_saved_row_law_def:
  ctor_saved_row_law ctx func ce cx DF lo explicit PG RowSide <=>
  !ty e si vv sm copy saved ss se raw ee v tv s G tn st0 tops env su en dst
   cursor h d shared pbase capacity root dst_offset prefix u Gu tu ats avs
   hl loc slot i inst cursor_inst cursor_var at av off.
    ty = lowered_value_type ce e /\
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
    ((?tag op0. saved = StackValue tag op0) \/
     (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
     (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
          ty = expr_type e /\ saved = vv)) /\
    local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
    ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
    local_ptrs_reserved ce se /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
    (!l. vv_operand saved <> Label l) /\
    read_result cx raw ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
    type_memory_size tv < 2**64 /\ value_has_type tv v /\
    vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
    ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
    ((case saved of StackValue tag op0 => ~is_word_type ty
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
      ptr_buf_ok ce e (vv_operand saved) G s) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
    storage_trace_domain cx st0 ee.storage_trace /\
    fn_inst_ids_distinct func /\ fn_has_code su en func /\
    compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix su u Gu tu /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
    inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
    cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
    cursor_inst.inst_opcode = ALLOCA /\ shared < loc /\
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
    at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
    abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
    h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
    off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
    h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
    (is_dynamic at ==> off + LENGTH (enc at av) <= capacity-dst_offset) ==>
    ?z Gz tz.
      (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
      abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix en z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
      RowSide su en u z
End

Definition ctor_saved_fold_law_def:
  ctor_saved_fold_law ctx func ce cx DF lo explicit PG RowSide EncoderSide <=>
  !st0 ee d se s G tn shared pbase capacity root dst dst_offset prefix st u Gu tu
   inst rows alen en ats avs hl bytes.
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix st u Gu tu /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
    inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\ fn_has_code st en func /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
    hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
    (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
       ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
       !i a c v Gv tv cursor slot.
       i < LENGTH rows /\
       abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
         shared pbase capacity root dst dst_offset prefix a v Gv tv /\
       abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot i a v Gv tv /\
       compile_abi_encode_value_rows ce (Var dst) cursor
         (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
         [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
       ?z Gz tz.
         (pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
         abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
           shared pbase capacity root dst dst_offset prefix c z Gz tz /\
         abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
         (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) /\
         RowSide a c v z) ==>
    ?z Gz tz.
      (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
      abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix en z Gz tz /\
      eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
      (!x. alen = Var x ==> not_fresh_at en x) /\
      mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
      (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
      EncoderSide st en u z
End
(* The saved list is evaluated in s; the encoder cursor and destination
   evolve from u. The destination may be anywhere in the output allocation. *)
Theorem ctor_encoder_length_witness_from_saved_laws:
  ctor_saved_row_law ctx func ce cx DF lo explicit PG RowSide /\
  ctor_saved_fold_law ctx func ce cx DF lo explicit PG RowSide EncoderSide /\
  body_inv tops ctx ce cx /\
  (!e. MEM e args ==> ?es'. expr_body_pre ce cx env e es') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
      H (INL vs) ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ann.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
    value_has_type tv (EL i vs)) /\
  rows = ZIP (svs,MAP (lowered_value_type ce) args) /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= capacity-dst_offset /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix st u Gu tu /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    EncoderSide st en u z
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_def, sumTheory.INL_11])) >>
     first_assum ACCEPT_TAC) >>
  qhdtm_assum `ctor_saved_fold_law`
    (irule o REWRITE_RULE [ctor_saved_fold_law_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `inst` >> simp[]) >>
  qexistsl_tac [`ats`,`avs`,`head_lengths ats 0`,`rows`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
  suspend "row"
QED

Resume ctor_encoder_length_witness_from_saved_laws[row]:
  qx_genl_tac [`ci`,`cr`] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qx_genl_tac [`i`,`a`,`c`,`r`,`Gr`,`tr`,`cursor`,`slot`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH svs = LENGTH args` by
    (qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
       (qx_choose_then `H0` assume_tac) >>
     qpat_assum `!H. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_def, sumTheory.INL_11])) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH rows = LENGTH args /\ LENGTH ats = LENGTH avs /\ LENGTH vs = LENGTH args` by
    (conj_tac >- simp[LENGTH_ZIP] >>
     drule vyper_to_abi_list_EL >> simp[] >> metis_tac[LIST_REL_LENGTH]) >>
  `i < LENGTH args /\ i < LENGTH ats /\ i < LENGTH vs` by
    metis_tac[LIST_REL_LENGTH] >>
  qabbrev_tac `e = EL i args` >>
  qabbrev_tac `sv = EL i svs` >>
  qabbrev_tac `v = EL i vs` >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = head_lengths ats 0 + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `EL i rows = (sv,lowered_value_type ce e) /\
   EL i ats = vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    simp[Abbr `sv`, Abbr `e`, EL_ZIP, EL_MAP, vyper_to_abi_types_MAP] >>
  `vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME (EL i avs)` by
    (drule vyper_to_abi_list_EL >> simp[Abbr `v`, Abbr `e`, EL_MAP]) >>
  `h = LENGTH (FLAT (abi_tuple_heads (head_lengths ats 0) 0 (TAKE i ats) (TAKE i avs))) /\
   head_lengths ats 0 <= off /\ off <= LENGTH bytes /\
   h + abi_member_head_size (EL i ats) <= head_lengths ats 0 /\
   (is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <= LENGTH bytes) /\
   (~is_dynamic (EL i ats) ==> LENGTH (enc (EL i ats) (EL i avs)) = abi_member_head_size (EL i ats)) /\
   abi_encoder_layout_valid (EL i ats) (EL i avs) /\
   LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abi_encode_values_index_bounds) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (simp_tac bool_ss [Abbr `off`] >> NO_TAC) >>
     TRY (simp[] >> NO_TAC) >>
     qexistsl_tac [`rows`,`ce.ce_struct_fields`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp_tac bool_ss [Abbr `h`]) >>
  `off <= capacity-dst_offset /\
   (is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <= capacity-dst_offset)` by
    (conj_tac >- decide_tac >> strip_tac >>
     qpat_assum `is_dynamic _ ==> off + _ <= LENGTH bytes` (drule_then assume_tac) >>
     decide_tac) >>
  `compile_abi_encode_value_rows ce (Var dst) cursor h [(sv,lowered_value_type ce e)] a = ((),c)` by
    (qpat_assum `EL i rows = _` (fn th => rewrite_tac [GSYM th]) >>
     simp_tac bool_ss [Abbr `h`] >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx sv ee s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_then (qspecl_then [`i`,`e`,`sv`,`v`] mp_tac) ctor_positional_row_at >>
     (impl_tac >- simp[Abbr `e`, Abbr `sv`, Abbr `v`]) >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "execute_row"
QED

Resume ctor_encoder_length_witness_from_saved_laws[execute_row]:
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `H0` (drule_then assume_tac)) >>
  drule_then (qspecl_then [`i`,`e`,`sv`,`v`] mp_tac) ctor_positional_row_at >>
  (impl_tac >- simp[Abbr `e`, Abbr `sv`, Abbr `v`]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 kall_tac (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`]
      (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `MEM e args` by simp[Abbr `e`, EL_MEM] >>
  qpat_assum `!e. MEM e args ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!i. i < LENGTH args ==> ?tv ann. _`
    (qspec_then `i` (drule_then mp_tac)) >>
  qpat_assum `Abbrev (e = _)`
    (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (v = _)`
    (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then (qx_choosel_then [`tv`,`ann`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_encoder_physical_size >> strip_tac >>
  `!l. vv_operand sv <> Label l` by
    (drule_all assign_place_operand_not_label >> strip_tac >>
     drule_all abi_snapshot_operand_not_label >> simp[]) >>
  `shared < st.cs_next_id` by
    (qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
     first_assum ACCEPT_TAC) >>
  qhdtm_assum `ctor_saved_row_law`
    (irule o REWRITE_RULE [ctor_saved_row_law_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `inst` >> asm_rewrite_tac[])
  >- (qexistsl_tac [`ci`,`cr`] >> asm_rewrite_tac[])
  >- (qexists_tac `tops` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `compile_abi_encode_value_rows _ _ _ _ [EL i rows] _ = _` kall_tac >>
  goal_assum (drule_at (Pat `compile_abi_encode_value_rows _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `read_result _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  qexistsl_tac [`EL i ats`,`EL i avs`,`off`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp_tac bool_ss [Abbr `off`] >> NO_TAC) >> REFL_TAC
QED

Finalise ctor_encoder_length_witness_from_saved_laws

Theorem ctor_encoder_length_witness:
  body_inv tops ctx ce cx /\
  (!e. MEM e args ==> ?es'. expr_body_pre ce cx env e es') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
      H (INL vs) ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ann.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
    value_has_type tv (EL i vs)) /\
  rows = ZIP (svs,MAP (lowered_value_type ce) args) /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= capacity-dst_offset /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix st u Gu tu /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  strip_tac >>
  mp_tac (PURE_REWRITE_RULE [AND_CLAUSES] (BETA_RULE (Q.INST
    [`RowSide` |-> `\a b r z. T`, `EncoderSide` |-> `\a b r z. T`]
    ctor_encoder_length_witness_from_saved_laws))) >>
  (impl_tac >-
    (conj_tac >- (pure_rewrite_tac[ctor_saved_row_law_def] >> BETA_TAC >>
                  pure_rewrite_tac[AND_CLAUSES] >> rpt gen_tac >>
                  MATCH_ACCEPT_TAC abi_encode_saved_row_open_pure) >>
     conj_tac >- (pure_rewrite_tac[ctor_saved_fold_law_def] >> BETA_TAC >>
                  pure_rewrite_tac[AND_CLAUSES] >> rpt gen_tac >>
                  MATCH_ACCEPT_TAC abi_encode_saved_values_execute_pure) >>
     asm_rewrite_tac[] >> qexists_tac `H` >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

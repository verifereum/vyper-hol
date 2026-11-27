(* A selected Create constructor row, at the cursor emitted by the loop. *)
Theory bodyCreateEncodedRowCallbackMods
Ancestors
  bodyCreateEncodedRowInputMods bodyAbiTupleReachedRowMods
  bodyAbiTupleBufferStateMods bodyAbiEncodePackedPostMods abiEncodeValuesRun
  abiEncodeValuesMetadata exprLoweringProps compileEnv loweringStateRelDefs
  vyperStorageFootprint contractABI venomInst venomState finite_map pair list

Theorem create_encoded_row_callback_mods:
  LENGTH args = LENGTH vals /\
  (!j. j < LENGTH args ==>
    ?si sm ss vv copy tv.
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL j args)) = SOME tv /\
      value_has_type tv (EL j vs) /\
      type_memory_bytes ce (lowered_value_type ce (EL j args)) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\
      (!l. vv_operand (EL j vals) <> Label l) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        abi_encode_saved_row_mods lo ce cx sa se (EL j args) (EL j vals)
          (EL j vs) si sm ss vv copy H ee G tn s)) /\
  rows = ZIP (vals,MAP (lowered_value_type ce) args) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  bytes = contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs) /\
  LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
  LENGTH prefix + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) <= capacity /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root dst (LENGTH prefix) prefix st initial Gi ti /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = shared /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (?E0. get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
    (!t rt. evaluate_type E0 t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt)) ==>
  !ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\
    not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
      i < LENGTH rows /\
      abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
        shared pbase capacity root dst (LENGTH prefix) prefix a v Gv tv /\
      abi_encode_values_prefix_at ats avs hl
        (pbase + LENGTH prefix) cursor st.cs_next_id slot i a v Gv tv /\
      compile_abi_encode_value_rows ce (Var dst) cursor
        (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND)
          (TAKE i rows))) [EL i rows] a = ((),c) /\
      fn_has_code a c func /\ cursor = Var r ==>
      ?z Gz tz.
        abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
          shared pbase capacity root dst (LENGTH prefix) prefix c z Gz tz /\
        abi_tuple_row_effects_mods ce ee func shared pbase capacity (LENGTH prefix) st.cs_next_id
          a v Gv tv c z Gz tz /\
        abi_encode_values_prefix_at ats avs hl
          (pbase + LENGTH prefix) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
        !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (v,Gv,tv) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?H. valid_horizon cx st0 H ee.storage_trace` by
    (qexists_tac `storage_trace_horizon ee.storage_trace` >>
     qhdtm_assum `storage_trace_domain`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  `shared < st.cs_next_id` by
    (qhdtm_assum `abi_tuple_buffer_state_mods`
       (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` by
    simp[Abbr `h`] >>
  `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` by
    simp[Abbr `off`] >>
  mp_tac (Q.INST [`at` |-> `EL i ats`, `av` |-> `EL i avs`]
    (INST_TYPE [alpha |-> ``:word8``] create_encoded_row_input_mods)) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC])) >>
  disch_then (MAP_EVERY (fn th =>
    if is_exists (concl th) then
      qx_choosel_then [`e`,`saved`,`ty`,`value`,`si`,`sm`,`ss`,`vv`,`copy`,`rt`]
        (MAP_EVERY assume_tac o CONJUNCTS) th
    else assume_tac th) o CONJUNCTS) >>
  `compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] a = ((),c)` by
    (qpat_assum `EL i rows = (saved,ty)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  irule abi_tuple_reached_row_mods >>
  qpat_assum `compile_abi_encode_value_rows _ _ _ h [(saved,ty)] _ = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ ty = SOME rt` (irule_at Any) >>
  qpat_assum `ci.inst_outputs = [r]` (irule_at Any) >>
  qpat_assum `owner.inst_outputs = [root]` (irule_at Any) >>
  (* Reuse the selected saved observation and its ABI member witnesses. *)
  qexistsl [`vv`,`value`,`ss`,`sm`,`si`,`sa`,`off`,`e`,`copy`,
            `EL i avs`,`EL i ats`,`H`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC,
    strip_tac >> FIRST [first_assum ACCEPT_TAC, first_assum (drule_then ACCEPT_TAC)]]
QED

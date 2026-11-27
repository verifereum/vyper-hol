(* The constructor rows encode immediately after the preserved Create prefix. *)
Theory bodyCreateEncodedRowsWindowMods
Ancestors
  bodyCreateEncodedRowsLayoutMods bodyCreateEncodedRowCallbackMods
  bodyCreateEncodedExitWindowMods bodyAbiTupleLinkedLoopMods
  bodyAbiTupleBufferStateMods bodyAbiEncodePackedPostMods
  abiEncodeValuesMetadata exprLoweringProps compileEnv loweringStateRelDefs
  vyperCreate vyperStorageFootprint contractABI venomInst venomState
  finite_map pred_set pair list arithmetic

Theorem create_encoded_rows_window_mods:
  LENGTH args = LENGTH vs /\ LENGTH args = LENGTH vals /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (?E0. get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
    (!t rt. evaluate_type E0 t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt)) /\
  (!i. i < LENGTH args ==> ?tv ftv.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ftv /\
    arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
    value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs)) /\
  (!i. i < LENGTH args ==> ?si sm ss vv copy tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    value_has_type tv (EL i vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size tv /\
    type_memory_size tv < 2**64 /\ (!l. vv_operand (EL i vals) <> Label l) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx sa se (EL i args) (EL i vals)
        (EL i vs) si sm ss vv copy H ee G tn s)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = shared /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  LENGTH prefix + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) <= capacity /\
  compile_abi_encode_values_to_buf ce (Var dst) (ZIP (vals,MAP (lowered_value_type ce) args)) st =
    (alen,fin) /\ fn_has_code st fin func /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root dst (LENGTH prefix) prefix st initial Gi ti ==>
  ?bytes z Gz tz.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root dst (LENGTH prefix) prefix fin z Gz tz /\
    abi_tuple_row_effects_mods ce ee func shared pbase capacity (LENGTH prefix) st.cs_next_id
      st initial Gi ti fin z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at fin x) /\
    LENGTH prefix + LENGTH bytes <= capacity /\ pbase + capacity <= z.vs_alloca_next /\
    mem_bytes_at (pbase + LENGTH prefix) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase + LENGTH prefix <= j /\ j < pbase + LENGTH prefix + LENGTH bytes ==>
      j NOTIN tz.t_mem) /\
    read_memory pbase (LENGTH (prefix ++ bytes)) z = prefix ++ bytes /\
    (!j. pbase <= j /\ j < pbase + LENGTH (prefix ++ bytes) ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (initial,Gi,ti) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac create_encoded_rows_layout_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`ats`,`avs`,`bytes`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  Q.SUBGOAL_THEN `?H. valid_horizon cx st0 H ee.storage_trace` assume_tac
  >- (qexists `storage_trace_horizon ee.storage_trace` >>
      qhdtm_assum `storage_trace_domain` (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  `LENGTH prefix + LENGTH bytes <= capacity` by decide_tac >>
  qabbrev_tac `rows = ZIP (vals,MAP (lowered_value_type ce) args)` >>
  qabbrev_tac `hl = head_lengths ats 0` >>
  `hl = head_lengths ats 0` by simp[Abbr `hl`] >>
  `rows = ZIP (vals,MAP (lowered_value_type ce) args)` by simp[Abbr `rows`] >>
  mp_tac (Q.INST [`payload_var` |-> `dst`, `dst_offset` |-> `LENGTH prefix`,
    `inst` |-> `owner`, `en` |-> `fin`, `u` |-> `initial`, `Gu` |-> `Gi`, `tu` |-> `ti`]
    abi_tuple_linked_loop_with_cursor_mods) >>
  impl_tac >-
    (reverse (rpt conj_tac)
     >- (mp_tac create_encoded_row_callback_mods >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (mk_asm "row_step") >>
         qx_genl_tac [`ci`,`r`] >> disch_tac >>
         asm_x "row_step" (qspecl_then [`ci`,`r`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         (* The two callback contracts order the cursor equality differently. *)
         simp_tac bool_ss [AC CONJ_ASSOC CONJ_COMM]) >>
     first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all_then (MAP_EVERY assume_tac o CONJUNCTS) create_encoded_exit_window_mods >>
  qexistsl [`bytes`,`z`,`Gz`,`tz`] >>
  pure_rewrite_tac[LENGTH_APPEND, ADD_ASSOC] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The saved row's exit state already carries the restore's end PC.
   Pair that PC with the confined path on the very same row witnesses. *)
Theory entryCreateExtRowRestore
Ancestors
  entryCreateAbiRestoreScope entryCreateCompletedCut bodyFullExtCallDirectState

Theorem abi_encode_saved_restore_row_scoped:
  (!bb j. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb (LENGTH sb.cs_current_insts) = SOME j ==>
       j.inst_id NOTIN frag_ids su sb) /\
  unwrap_exit_phi_free func sb /\
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
  unwrap_value ce saved su = (src,sb) /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ci_mono su sb /\ ~is_word_type ty /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  pbase+dst_offset+LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  pbase+dst_offset+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity ==>
  ?z Gz tz.
    (pure_frame ce func ee su u z /\ wb_frame ce ee ee su u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix sb z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i sb z Gz tz /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at su x ==>
      lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)) /\
    z.vs_labels = u.vs_labels /\
    (?first last. expr_val_at ce cx ty first last ee v src z /\
       last.cs_next_id <= sb.cs_next_id /\
       (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    create_operand_full_scope su sb explicit ctx func u [] (OK z)
Proof
  disch_tac >>
  mp_tac (SPEC_ALL create_abi_saved_restore_confined) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`z`,`Gz`,`tz`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sb z _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  simp[create_operand_full_scope_def]
QED

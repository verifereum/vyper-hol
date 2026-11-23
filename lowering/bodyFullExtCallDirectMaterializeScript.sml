Theory bodyFullExtCallDirectMaterialize
Ancestors
  abiEncodeValuesPrefixFrame
  bodyFullExtCallDirectState bodyFullExtCallDirectSaved bodyFullExtCallDirectUnwrap
  localPtrsProps
  abiEncodeValuesRun abiEncodeValuesSource abiEncodeValuesPhases abiEncodeValuesMetadata
  abiEncoderWindowPhase abiEncoderWindowContract exprSimAbiEncodeExecFrame
  gasOriginPtrLabels exprLoweringProps stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs fragGasOriginPtr fragExec
  compileEnv exprLowering context contractABI
  vyperValue vyperTyping vyperABI venomState venomInst venomMemDefs
  finite_map pred_set list arithmetic pair words
Libs pureFrameLib

(* The cursor and payload remain owned throughout the per-row unwrap.
   The saved operand itself still uses its original compiler interval. *)
Theorem abi_encode_saved_materialized_frame:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  pbase+dst_offset+LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  pbase+dst_offset+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  ci_mono a c /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee v /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gv tv v) /\
  wb_frame ce ee ee a u v /\ ghost_kept_at lo ce ee a Gu tu u Gv tv /\
  (!x. not_fresh_at a x ==>
    lookup_var x v = lookup_var x u /\ FLOOKUP Gv x = FLOOKUP Gu x /\
    op_taint tv (Var x) = op_taint tu (Var x)) /\
  alloca_history func v /\ u.vs_alloca_next <= v.vs_alloca_next /\
  ~v.vs_halted /\ v.vs_current_bb = c.cs_current_bb /\
  v.vs_inst_idx = LENGTH c.cs_current_insts ==>
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c v Gv tv /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca o cj 1)) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ v /\ _`
    (drule_then (assume_tac o cj 2 o MATCH_MP stmt_state_rel_local_ptrs_alloca o cj 1)) >>
  `!name local_base k. local_region ce ee.scopes u name local_base k ==>
    (pbase+capacity <= local_base \/ local_base+k <= pbase) /\ (slot+32 <= local_base \/ local_base+k <= slot)` by
    (rpt gen_tac >> disch_tac >>
     let
       val separation = REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]
         local_ptrs_rel_alloca_disjoint
     in
       conj_tac
       >- (MATCH_MP_TAC (Q.SPECL
             [`func`,`ce`,`ee.scopes`,`u`,`inst`,`root`,`pbase`,`capacity`,`name`,`local_base`,`k`]
             separation) >>
           rpt conj_tac >> asm_rewrite_tac[])
       >> MATCH_MP_TAC (Q.SPECL
            [`func`,`ce`,`ee.scopes`,`u`,`cursor_inst`,`cursor_var`,`slot`,`32`,`name`,`local_base`,`k`]
            separation) >>
       rpt conj_tac >> asm_rewrite_tac[]
     end) >>
  conj_tac
  >- (mp_tac abi_encode_saved_state_unwrap >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`s` |-> `u`,`t` |-> `v`,`G` |-> `Gu`,`G'` |-> `Gv`,
    `tn` |-> `tu`,`tn'` |-> `tv`,`st` |-> `a`,`en` |-> `c`,
    `d` |-> `pbase+dst_offset`,`b` |-> `pbase`,`cap` |-> `capacity`,`owner` |-> `shared`]
    abi_encode_values_prefix_after_unwrap) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then ACCEPT_TAC
QED

Theorem extcall_direct_materialized_frame:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  pbase+32+LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  pbase+32+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  ci_mono a c /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee v /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gv tv v) /\
  wb_frame ce ee ee a u v /\ ghost_kept_at lo ce ee a Gu tu u Gv tv /\
  (!x. not_fresh_at a x ==>
    lookup_var x v = lookup_var x u /\ FLOOKUP Gv x = FLOOKUP Gu x /\
    op_taint tv (Var x) = op_taint tu (Var x)) /\
  alloca_history func v /\ u.vs_alloca_next <= v.vs_alloca_next /\
  ~v.vs_halted /\ v.vs_current_bb = c.cs_current_bb /\
  v.vs_inst_idx = LENGTH c.cs_current_insts ==>
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector c v Gv tv /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`]
    abi_encode_saved_materialized_frame) >>
  drule_then (fn th => asm_rewrite_tac[MATCH_MP abi_encode_saved_state_extcall th])
    extcall_direct_state_selector_length
QED


Theorem abi_encode_saved_restore_row_side_core:
  saved_restore_copy_laws ctx func explicit su sb P /\
  (!a u. ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==> P a a u u) /\
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
    P su sb u z /\
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
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`front` |-> `se`] extcall_direct_restore_saved_from_side) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  `abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix sb z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i sb z Gz tz` by
    (mp_tac (Q.INST [`a` |-> `su`,`c` |-> `sb`,
       `v` |-> `z`,`Gv` |-> `Gz`,`tv` |-> `tz`] abi_encode_saved_materialized_frame) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `z.vs_labels = u.vs_labels` by metis_tac[gas_origin_ptr_path_preserves_labels] >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  `su.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  qpat_assum `~is_word_type ty ==> _ \/ _` (drule_then (DISJ_CASES_THEN assume_tac))
  >- (qexistsl_tac [`si`,`ss`] >> rpt conj_tac >> TRY decide_tac >>
      qpat_assum `ty = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
      first_assum ACCEPT_TAC)
  >> qexistsl_tac [`su`,`sb`] >> rpt conj_tac >> TRY decide_tac >>
  qpat_assum `ty = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  first_assum ACCEPT_TAC
QED

local
  val unobserved = PURE_REWRITE_RULE
    [bodyFullExtCallDelayedSlotTheory.saved_restore_copy_laws_true,
     boolTheory.AND_CLAUSES, boolTheory.IMP_CLAUSES, boolTheory.FORALL_SIMP]
    (BETA_RULE (Q.INST [`P` |-> `\a b u z. T`] abi_encode_saved_restore_row_side_core))
in
Theorem abi_encode_saved_restore_row_pure:
  ^(concl unobserved)
Proof
  ACCEPT_TAC unobserved
QED
end

Theorem abi_encode_saved_restore_row =
  pureFrameLib.drop_frame abi_encode_saved_restore_row_pure

Theorem extcall_direct_restore_row:
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
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id pbase capacity root dst selector su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i su u Gu tu /\
  32 <= capacity /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  pbase+32+LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  pbase+32+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst selector sb z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i sb z Gz tz /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at su x ==>
      lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)) /\
    z.vs_labels = u.vs_labels /\
    (?first last. expr_val_at ce cx ty first last ee v src z /\
       last.cs_next_id <= sb.cs_next_id /\
       (se.cs_next_id < first.cs_next_id \/ last.cs_next_id <= se.cs_next_id)) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`,
    `shared` |-> `se.cs_next_id`]
    abi_encode_saved_restore_row) >>
  drule_then (fn th => asm_rewrite_tac[MATCH_MP abi_encode_saved_state_extcall th])
    extcall_direct_state_selector_length
QED

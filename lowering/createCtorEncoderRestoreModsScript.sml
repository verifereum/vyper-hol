Theory createCtorEncoderRestoreMods
Ancestors
  createCtorEncoderSavedAdvanceMods createCtorEncoderDelayedSlotMods
  createCtorEncoderDelayedRuntimeLinkedMods createCtorEncoderDelayedCtorMods
  createCtorUnwrapSlotPostMods abiEncodeValuesPrefixFrame abiEncodeValuesSource
  abiEncodeValuesPhases bodyFullExtCallDirectUnwrap localPtrsProps stateRelProj
  exprSimWordArgs wordArgsPtr memoryReadProps exprOperandVar exprLoweringProps
  createExprSizeExitDefsMods loweringPosts loweringStateRelDefs bodyPtrDefs
  fragGasOriginPtr fragExec exprLowering compileEnv context venomMemDefs
  abiEncodeValuesRun freshWrites contractABI venomState bodyFullPostsMods
  valueEncodingTyping vyperStorageFootprint venomInst exprSimMemDefs valueTypingMemoryProps
  finite_map arithmetic words pred_set list pair
Libs horizonTypeLib

(* Both the encoder allocation and cursor slot predate the unwrap. *)
Theorem ctor_encoder_restore_frame[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  pbase+dst_offset+LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  pbase+dst_offset+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  ci_mono a c /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
  wb_frame ce ee ee a u z /\ ghost_kept_at lo ce ee a Gu tu u Gz tz /\
  (!x. not_fresh_at a x ==>
    lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
    op_taint tz (Var x) = op_taint tu (Var x)) /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ~z.vs_halted /\ z.vs_current_bb = c.cs_current_bb /\
  z.vs_inst_idx = LENGTH c.cs_current_insts ==>
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c z Gz tz /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i c z Gz tz
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qhdtm_assum `abi_encode_saved_state_mods`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  qhdtm_assum `abi_encode_values_prefix_at`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func ce cx ee u /\ stmt_state_rel hz ctx func ce cx ee z /\
   stmt_state_rel hz ctx func ce cx ee s` by simp[] >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ u` (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ z` (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `!name b k. local_region ce ee.scopes u name b k ==>
     (pbase+capacity <= b \/ b+k <= pbase) /\ (slot+32 <= b \/ b+k <= slot)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (irule (REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def] local_ptrs_rel_alloca_disjoint) >>
         qexistsl_tac [`ce`,`func`,`inst`,`name`,`root`,`ee.scopes`,`u`] >> simp[])
     >> irule (REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def] local_ptrs_rel_alloca_disjoint) >>
     qexistsl_tac [`ce`,`func`,`cursor_inst`,`name`,`cursor_var`,`ee.scopes`,`u`] >> simp[]) >>
  reverse conj_tac
  >- (irule abi_encode_values_prefix_after_unwrap >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`Gu`,`pbase`,`capacity`,`ce`,`ee`,`lo`,`shared`,`u`,`a`,`tu`] >>
      asm_rewrite_tac[] >> rpt strip_tac >> decide_tac) >>
  qabbrev_tac `start = pbase+dst_offset-LENGTH prefix` >>
  `pbase <= start /\ start+LENGTH prefix = pbase+dst_offset /\
   start+LENGTH prefix <= pbase+capacity` by (fs[Abbr `start`] >> decide_tac) >>
  `FLOOKUP z.vs_allocas shared = SOME (pbase,capacity) /\
   mem_bytes_at start (LENGTH prefix) z.vs_memory = mem_bytes_at start (LENGTH prefix) u.vs_memory /\
   (!j. start <= j /\ j < start+LENGTH prefix /\ j IN tz.t_mem ==> j IN tu.t_mem)` by
    (irule (INST_TYPE [alpha |-> ``:num # num``] abi_encode_values_unwrap_window) >>
     simp[] >> qexistsl_tac [`Gu`,`Gz`,`ce`,`ee`,`lo`,`a`] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!name b k. local_region _ _ _ name b k ==> _` (drule_then strip_assume_tac) >> decide_tac) >>
  `read_memory start (LENGTH prefix) z = prefix` by
    fs[memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
  `!j. start <= j /\ j < pbase+dst_offset ==> j NOTIN tz.t_mem` by metis_tac[] >>
  `eval_operand (Var root) z = SOME (n2w pbase) /\ ptr_covers Gz tz root z capacity` by
    (irule extcall_direct_unwrap_pointer >> qexistsl_tac [`Gu`,`u`,`a`,`tu`] >> simp[]) >>
  `eval_operand (Var dst) z = SOME (n2w (pbase+dst_offset)) /\
   ptr_covers Gz tz dst z (capacity-dst_offset)` by
    (irule extcall_direct_unwrap_pointer >> qexistsl_tac [`Gu`,`u`,`a`,`tu`] >> simp[]) >>
  `se.cs_next_id <= a.cs_next_id` by decide_tac >>
  `wb_frame ce ee ee se s z` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee a u z` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s Gz tz` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee a Gu tu u Gz tz` (irule_at Any) >> simp[]) >>
  fs[ci_mono_def] >>
  `not_fresh_at c root /\ not_fresh_at c dst` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `Abbrev (start = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[abi_encode_saved_state_mods_def] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Theorem ctor_encoder_restore_identity[local]:
  ((?tag op. saved = StackValue tag op) \/
   (?p. saved = LocatedValue ty p /\ p.ptr_location = LocMemory)) /\
  unwrap_value ce saved su = (src,sb) /\ ~is_word_type ty /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
  vv_holds_mods ce cx ty raw saved ee u /\ vv_at ce cx ty si ss ee raw saved u /\
  ptr_vv_ok cx ty raw saved ee Gu tu u /\ vv_store_bound cx ty ty ee raw saved u ==>
  sb = su /\ src = vv_operand saved /\ expr_val_at ce cx ty si ss ee v src u /\
  expr_val_rel cx ty v src u /\ ptr_val_ok cx ty v src Gu tu u /\
  expr_store_bound cx ty v src u
Proof
  strip_tac >>
  gvs[vv_holds_mods_def,vv_holds_def,unwrap_value_def,comp_return_def,vv_operand_def,
      vv_at_def,expr_val_rel_def,expr_val_at_def,ptr_vv_ok_def,ptr_val_ok_def,
      vv_store_bound_def,expr_store_bound_def] >>
  metis_tac[value_has_type_memory_wf]
QED

Theorem ctor_encoder_restore_row_mods:
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
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ value_has_type rt v /\
  vv_holds_mods ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!j. j < lo /\ j IN tu.t_mem ==> j IN tn.t_mem) /\
    !w. eval_operand (vv_operand saved) s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt v (w2n w) mem)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  unwrap_value ce saved su = (src,sb) /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ci_mono su sb /\ ~is_word_type ty /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
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
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qhdtm_assum `abi_encode_saved_state_mods`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  `vv_holds_mods ce cx ty raw saved ee u /\ vv_at ce cx ty si ss ee raw saved u /\
   ptr_vv_ok cx ty raw saved ee Gu tu u /\ vv_store_bound cx ty ty ee raw saved u /\
   ((case saved of StackValue tag op => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==> ptr_buf_ok ce e (vv_operand saved) Gu u) /\
   (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
     storage_well_formed_on cx ee (FST H) /\ vv_storage_live H cx saved ee u /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
   (!x. vv_operand saved = Var x ==> not_fresh_at su x) /\
   (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) u = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory rt v (w2n w) mem))` by
    suspend "advance" >>
  Cases_on `(?tag op. saved = StackValue tag op) \/
            (?p. saved = LocatedValue ty p /\ p.ptr_location = LocMemory)`
  >- suspend "identity" >>
  `?p. saved = LocatedValue ty p /\ p.ptr_location <> LocMemory /\ ty = expr_type e /\ vv = saved` by
    metis_tac[] >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`si`] mp_tac (CONJUNCT1 compile_expr_ci_mono) >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id` by decide_tac >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (`!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
       metis_tac[CONJUNCT1 compiler_compile_var] >>
     fs[vv_operand_def]) >>
  `?z Gz tz.
    pure_frame ce func ee su u z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    z.vs_labels = u.vs_labels /\
    (!x. not_fresh_at su x ==> lookup_var x z = lookup_var x u /\
       FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
    wb_frame ce ee ee su u z /\ ghost_kept_at lo ce ee su Gu tu u Gz tz /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    expr_val_at ce cx ty su sb ee v src z` by suspend "execute" >>
  `abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
     shared pbase capacity root dst dst_offset prefix sb z Gz tz /\
   abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i sb z Gz tz` by
    suspend "frame" >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> simp[] >> qexistsl_tac [`su`,`sb`] >>
  qpat_assum `ty = expr_type e` (fn th => simp[Once (GSYM th)])
  >> (gvs[])
QED

Resume ctor_encoder_restore_row_mods[advance]:
  irule ctor_encoder_saved_advance_mods >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  simp[] >>
  `!tag p. saved = LocatedValue tag p ==> tag = lowered_value_type ce e` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `(?tag op0. saved = StackValue tag op0) \/ _`
       (DISJ_CASES_THEN strip_assume_tac) >> gvs[]) >> simp[]
QED

Resume ctor_encoder_restore_row_mods[identity]:
  drule_all ctor_encoder_restore_identity >> strip_tac >> gvs[] >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  simp[wb_frame_def, CONJUNCT1 gas_origin_ptr_path_rules] >>
  qexistsl_tac [`si`,`ss`] >> simp[] >> decide_tac
QED

Resume ctor_encoder_restore_row_mods[frame]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by simp[] >>
  irule ctor_encoder_restore_frame >>
  qhdtm_assum `abi_encode_saved_state_mods` (irule_at Any) >>
  simp[] >> qexistsl_tac [`inst`,`cursor_var`,`cursor_inst`] >> simp[]
QED

Resume ctor_encoder_restore_row_mods[execute]:
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `ce.ce_is_ctor`
      >- (`!w. eval_operand p.ptr_operand u = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by
            (qpat_assum `ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==> !w. _` mp_tac >>
             simp[vv_location_def,vv_operand_def]) >>
          suspend "ctor") >>
      suspend "runtime") >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` suffices_by
    (disch_tac >> suspend "slot") >>
  Cases_on `p.ptr_location` >> gvs[] >> fs[vv_holds_mods_def,vv_holds_def]
QED

Resume ctor_encoder_restore_row_mods[ctor]:
  `lowered_value_type ce e = expr_type e` by metis_tac[] >>
  qpat_x_assum `ty = expr_type e` SUBST_ALL_TAC >>
  qpat_x_assum `vv = saved` SUBST_ALL_TAC >>
  qpat_x_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`fn` |-> `func`, `t` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`]
    ctor_encoder_delayed_ctor_mods) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, sym_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_encoder_restore_row_mods[runtime]:
  `compile_expr ce (expr_type e) e si = (saved,sm)` by
    (qpat_assum `vv = saved` (fn th => pure_once_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  mp_tac ctor_encoder_delayed_runtime_linked_callback_mods >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_encoder_restore_row_mods[slot]:
  `lowered_value_type ce e = expr_type e` by metis_tac[] >>
  qpat_x_assum `ty = expr_type e` SUBST_ALL_TAC >>
  qpat_x_assum `vv = saved` SUBST_ALL_TAC >>
  qpat_x_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`fn` |-> `func`, `t` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`]
    ctor_encoder_delayed_slot_mods) >>
  (impl_tac >- (rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC)) >>
    suspend "slot_post")) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_encoder_restore_row_mods[slot_post]:
  map_every qx_gen_tac [`nb`,`n`,`a`,`mid`,`ua`,`r`,`dst_word`,`allocated`,`G0`,`tn0`,`buf`,`z`,`Gf`,`tnf`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  qpat_assum `post_value_type ce e = expr_type e` (fn th =>
    mp_tac (REWRITE_RULE [th] (Q.INST
      [`cenv` |-> `ce`, `ty` |-> `expr_type e`, `t` |-> `expr_type e`,
       `sa` |-> `si`, `sb` |-> `su`, `sc` |-> `sb`,
       `es` |-> `ee`, `s0` |-> `u`, `s` |-> `u`, `u` |-> `ua`,
       `G` |-> `Gu`, `tn` |-> `tu`, `Gi` |-> `Gu`, `ti` |-> `tu`,
       `tv` |-> `Value v`, `rty` |-> `rt`, `op` |-> `src`,
       `root` |-> `r`, `dst` |-> `dst_word`]
      ctor_unwrap_slot_endpoint_post_mods))) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, simp[NoAsms,vyperStateTheory.read_result_def,vyperStateTheory.return_def,ghost_kept_at_def]])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Finalise ctor_encoder_restore_row_mods

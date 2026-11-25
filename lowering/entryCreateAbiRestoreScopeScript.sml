(* Confinement of the saved ABI-row materialization at its restore cut. *)
Theory entryCreateAbiRestoreScope
Ancestors
  entryCreatePathScope createCtorSegmentArrival
  bodyFullExtCallDirectMaterialize bodyFullExtCallDirectState bodyFullUnwrapSlotBand
  abiEncoderProps
  createSizePrefixReplay createMarkedPath fragGasOrigin gasEvents
  createSizeCutRegion createSizeLocationCode entryCreateUnwrapCode entryCreateUnwrapSlot
  loweringShapeDefs bodyFullIfExpReach exprSimAbiGasBridge exprPtrUnwrapEnsureShape
  exprLoweringProps
  abiEncodeValuesSource abiEncodeValuesPrefixFrame
  fragExec compileEnv venomState venomExecSemantics venomExecProofs
  exprLowering context vyperStorageFootprint loweringPosts bodyPtrDefs
  loweringStateRelDefs fragGasOriginPtr finite_map words
  venomInst relation list pred_set arithmetic

Theorem abi_restore_band_prefix:
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
       get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
       i.inst_id NOTIN frag_ids a b) /\
  create_cut_code {} a b /\ fn_has_code a b f /\ unwrap_exit_phi_free f b /\
  (!i. MEM i (frag_code a b) ==> i.inst_opcode <> GAS) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  RTC (\u v. ?i. ctor_segment_fetch f u = SOME i /\
               i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
               ctor_segment_next f u i = SOME v) s t ==>
  create_expr_prefix a b E C f s [] t
Proof
  strip_tac >>
  drule_all create_cut_region_rules >> strip_tac >>
  `!target. lookup_block b.cs_current_bb f.fn_blocks = SOME target ==>
            phi_prefix_length target.bb_instructions <= LENGTH b.cs_current_insts` by
    fs[unwrap_exit_phi_free_def] >>
  `!u v i. ~u.vs_halted /\ create_cut_region a b u /\
      ctor_segment_fetch f u = SOME i /\
      i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
      ctor_segment_next f u i = SOME v ==>
      ~v.vs_halted /\ create_cut_region a b v /\ create_expr_prefix a b E C f u [] v` by
    (rpt gen_tac >> strip_tac >>
     `?bb. lookup_block u.vs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME i` by
       fs[ctor_segment_fetch_def, AllCaseEqs()] >>
     (Q.SUBGOAL_THEN
       `u.vs_current_bb <> b.cs_current_bb \/ u.vs_inst_idx <> LENGTH b.cs_current_insts`
       ASSUME_TAC >- metis_tac[]) >>
     `i.inst_opcode <> GAS` by metis_tac[] >>
     `gas_origin_edge F E C f u [] (OK v) /\ ~v.vs_halted` by
       (qpat_assum `ctor_segment_next _ _ _ = _` mp_tac >>
        qpat_assum `~u.vs_halted` mp_tac >>
        qpat_assum `lookup_block u.vs_current_bb _ = _` mp_tac >>
        qpat_assum `get_instruction bb u.vs_inst_idx = _` mp_tac >>
        qpat_assum `i.inst_opcode <> INVOKE` mp_tac >>
        qpat_assum `i.inst_opcode <> GAS` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> ntac 5 disch_tac >>
        simp[ctor_segment_next_def, ctor_segment_entry_def, AllCaseEqs()] >>
        rpt strip_tac >> gvs[] >>
        imp_res_tac step_inst_base_OK_preserves_halted >>
        TRY (qpat_assum `OK _ = eval_phis _ _` (assume_tac o SYM) >>
             drule eval_phis_preserves_halted >> strip_tac) >>
        gvs[gas_origin_edge_def] >> qexists_tac `0` >>
        simp[step_inst_non_invoke, Once gas_events_step_def] >> metis_tac[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[] >>
     simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
  qabbrev_tac `P = \u. ~u.vs_halted /\ create_cut_region a b u /\
                    create_expr_prefix a b E C f s [] u` >>
  `P t` suffices_by simp[Abbr `P`] >>
  irule RTC_lifts_invariants >> first_assum (irule_at Any) >>
  conj_tac >- simp[Abbr `P`] >>
  simp_tac bool_ss [Abbr `P`, PULL_EXISTS] >> rpt strip_tac >>
  qpat_assum `!u v i. _ ==> ~v.vs_halted /\ _` (drule_all_then strip_assume_tac) >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

Theorem abi_restore_fragment_nogas[local]:
  ((?tag op0. saved = StackValue tag op0) \/ (?p. saved = LocatedValue ty p)) /\
  ~is_word_type ty /\ unwrap_value ce saved a = (src,b) /\
  MEM i (frag_code a b) ==> i.inst_opcode <> GAS
Proof
  strip_tac
  >- gvs[unwrap_value_def,comp_return_def,frag_code_def,emitted_blocks_def,emitted_insts_def] >>
  qpat_x_assum `saved = _` SUBST_ALL_TAC >>
  Cases_on `p.ptr_location = LocMemory`
  >- gvs[unwrap_value_def,comp_return_def,frag_code_def,emitted_blocks_def,emitted_insts_def] >>
  Cases_on `p.ptr_location = LocCode`
  >- (drule_all unwrap_code_copy_layout >>
      simp[same_blocks_def,EVERY_MEM] >> strip_tac >>
      fs[frag_code_def,emitted_blocks_def] >>
      first_x_assum (drule_then mp_tac) >> strip_tac >> simp[]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_value_def,compile_ensure_in_memory_def,compile_alloc_buffer_def,
           emitHelperTheory.emit_op_def,emitHelperTheory.emit_void_def,
           comp_bind_def,comp_return_def,comp_ignore_bind_def,
           fresh_var_def,fresh_id_def,emit_def] >>
      strip_tac >> qpat_x_assum `_ = b` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `MEM i (frag_code _ _)` mp_tac >>
      simp[frag_code_def,emitted_blocks_def,emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
      simp[mk_inst_def] >> strip_tac >> gvs[]) >>
  `?tr. p.ptr_location = slot_loc tr` by
    (Cases_on `p.ptr_location` >> gvs[slot_loc_def] >> metis_tac[]) >>
  drule_all exprPtrUnwrapStorageLayoutTheory.unwrap_slot_ensure_layout >> strip_tac >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  metis_tac[unwrap_slot_ensure_opcodes]
QED

(* Augment the ordinary saved-row packet without choosing a new replay. *)
Theorem create_abi_saved_restore_confined:
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
    create_expr_prefix su sb explicit ctx func u [] z
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL abi_encode_saved_restore_row_band) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`z`,`Gz`,`tz`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  `create_cut_code {} su sb` by
    (mp_tac (Q.INST [`a` |-> `su`, `vv` |-> `saved`] create_unwrap_cut_code) >> simp[]) >>
  `!j. MEM j (frag_code su sb) ==> j.inst_opcode <> GAS` by
    (gen_tac >> disch_tac >>
     qpat_assum `unwrap_value ce saved su = _` mp_tac >>
     qpat_assum `~is_word_type ty` mp_tac >>
     qpat_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
     qpat_assum `MEM j (frag_code su sb)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_restore_fragment_nogas]) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ su u _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  irule abi_restore_band_prefix >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `unwrap_exit_phi_free _ _ ==> unwrap_band _ _ _ _ _` (drule_then mp_tac) >>
  simp_tac bool_ss [unwrap_band_def,frag_ids_def,GSPECIFICATION,pairTheory.PAIR_EQ,
                    UNWIND_THM2,CONJ_ASSOC]
QED

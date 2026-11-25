(* The loaded header at the observed cuts of a successful linked byte read. *)
Theory createSizeRawHeaderSuccessLengthMods
Ancestors
  createSizeSnapshotLengthMods createSizeRawCodeSiteBoundMods
  createSizeRawHeaderGeometryMods createSizeRawHeaderGeometry createBlueprintRawCopyLayoutMods
  createCtorSnapshotTypingMods reasonEndpointResourcesPtr bodyFullPostsMods
  exprSimHypsDefs exprSimSource bodyPtrDefs loweringPosts compileEnv
  vyperState words arithmetic

Theorem create_raw_header_success_length_mods:
  expr_body_pre_mods mods ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  LENGTH code <= n /\ n <= 49152 /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce a /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len,c) /\ fn_has_code a b func /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
                 val_in_memory rt (BytesV code) (w2n w) mem)) /\
  z.vs_current_bb = b.cs_current_bb /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
   run_inst_seq (emitted_insts a c) u = OK (l with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm x exit.
      compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
      fn_has_code a sm func /\ fn_has_code sm b func /\
      lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      x.vs_current_bb = sm.cs_current_bb /\ x.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a sm) u = OK (x with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> b.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func v ms (OK w)) x z) ==>
  eval_operand len l = SOME (n2w (LENGTH code))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `copy_old_operand a (vv_operand vv)` by (drule_all compile_expr_old_operand >> simp[]) >>
  `post_value_type ce e = BaseT (BytesT (Dynamic n))` by
    (irule EQ_TRANS >> qexists_tac `expr_type e` >>
     simp[post_value_type_bytestring,is_bytestring_type_def]) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := obs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL (BytesV code),p)` by
    simp[bind_def] >>
  drule_all create_blueprint_raw_copy_layout_mods >> strip_tac >>
  `LENGTH code + 32 < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  let fun consume 0 th = irule th
        | consume k th = drule_then (consume (k - 1)) th
  in consume 7 create_snapshot_length_word_mods end >>
  reverse conj_tac
  >- (reverse conj_tac >- (conj_tac >- (disch_tac >> first_assum ACCEPT_TAC) >>
                           first_assum ACCEPT_TAC) >>
      disch_tac >> conj_tac >- first_assum ACCEPT_TAC >> conj_tac
      >- (disch_tac >> qx_gen_tac `w` >> disch_tac >>
          qpat_assum `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
          (impl_tac >- simp[]) >>
          disch_then (qspecl_then [`BaseTV (BytesT (Dynamic n))`,`w`] mp_tac) >>
          simp[post_value_type_bytestring,mem_agree_outside_def]) >>
      Cases_on `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a` >>
      drule_all create_raw_snapshot_alloc_interval >> strip_tac >>
      drule_all create_raw_code_snapshot_site_bound_mods >> simp[]) >>
  qexists_tac `explicit` >> rpt gen_tac >> disch_tac >>
  qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx (p with gas_obs := []) u` by fs[vv_post_mods_def] >>
  drule_all create_raw_header_capacity_mods >> strip_tac >>
  qexistsl_tac [`buf`,`sm`,`x`,`z`,`exit`] >>
  `w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
   32 * ((type_memory_bytes ce (lowered_value_type ce e) + 31) DIV 32) < dimword (:256)` by
    (drule_all create_raw_header_slot_nonwrap >> simp[]) >>
  simp[]
QED

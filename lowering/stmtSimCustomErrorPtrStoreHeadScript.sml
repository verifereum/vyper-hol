(* Interior stores into the preallocated custom-error tuple buffer. *)
Theory stmtSimCustomErrorPtrStoreHead
Ancestors
  stmtSimCustomErrorPtrUnwrap stmtSimCustomErrorPtrStoreProbe
  annAssignPtrDestinationFrame annAssignPtrExterior annAssignPtrStore
  bodyPtrDefs freshWrites loweringStateRelDefs venomState finite_map pred_set

Theorem custom_error_slice_store_frame_ptr[local]:
  stmt_state_rel ctx func ce cx ee s /\ ~ce.ce_is_ctor /\
  ghost_inv d ce cx ee G tn s /\
  ghost_kept ce ee sr G0 tn0 sref G tn /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!z. not_fresh_at su z ==> lookup_var z t = lookup_var z s /\
    FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
  (!i. ~(a <= i /\ i < a+k) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!n lo sz i. local_region ce ee.scopes s n lo sz /\ lo <= i /\ i < lo+sz ==>
    ~(a <= i /\ i < a+k)) /\
  (!aid lo sz i. FLOOKUP sref.vs_allocas aid = SOME (lo,sz) /\
    aid < sr.cs_next_id /\ lo <= i /\ i < lo+sz ==> ~(a <= i /\ i < a+k)) /\
  (!n lo sz i. local_region ce ee.scopes sref n lo sz /\ lo <= i /\ i < lo+sz ==>
    ~(a <= i /\ i < a+k)) /\
  (!z. not_fresh_at sr z ==> not_fresh_at su z) /\
  (!name entry z sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
  (!z. ce.ce_imm_alloca = SOME (Var z) ==> not_fresh_at su z) ==>
  stmt_state_rel ctx func ce cx ee t /\ ghost_inv d ce cx ee Gf tf t /\
  ghost_kept ce ee sr G0 tn0 sref Gf tf
Proof
  strip_tac >> conj_tac
  >- (irule annassign_state_vars_exterior_ptr >> simp[] >>
      qexistsl [`s`, `{i | a <= i /\ i < a+k}`] >> simp[] >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!n lo sz i. local_region ce ee.scopes s n lo sz /\ _ ==> _`
          drule_all >> simp[]) >>
      conj_tac >- (rpt strip_tac >>
        `not_fresh_at su p` by (first_x_assum drule_all >> simp[]) >>
        first_x_assum drule >> simp[]) >>
      fs[venom_state_component_equality]) >>
  conj_tac
  >- (irule annassign_ghost_vars_exterior_ptr >>
      qexistsl [`G`, `ctx`, `func`, `s`, `tn`, `{i | a <= i /\ i < a+k}`] >>
      simp[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
  irule annassign_ghost_kept_vars_exterior_ptr >>
  qexistsl [`G`, `tn`, `{i | a <= i /\ i < a+k}`] >> simp[] >> metis_tac[]
QED

Theorem custom_error_mstore_path_ptr[local]:
  emit_void MSTORE [Var p; value] su = ((),st) /\ fn_has_code su st func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
  ptr_covers G tn p s 32 /\ op_taint tn value = {} /\
  lookup_var p s = SOME a /\ eval_operand value s = SOME w /\ val_wf tv v /\
  (!u. val_in_memory tv v (w2n a) (mstore (w2n a) w u).vs_memory) ==>
  !D PG. ?tf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tf (OK t) /\
    t.vs_current_bb = st.cs_current_bb /\ t.vs_inst_idx = LENGTH st.cs_current_insts /\
    ~t.vs_halted /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!z. lookup_var z t = lookup_var z s /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
    (!i. ~(w2n a <= i /\ i < w2n a+32) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v (w2n a) m)
Proof
  strip_tac >> rpt gen_tac >>
  `emit_inst MSTORE [Var p; value] [] su = ((),st)` by
    fs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def] >>
  drule_all annAssignPtrSetupTheory.annassign_emit_instruction_ptr >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst su.cs_next_id MSTORE [Var p; value] [])`
    by simp[] >>
  drule_all annassign_mstore_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] assume_tac) >>
  drule_all exprSimPtrTopLevelImmutableCopyTheory.toplevel_immutable_mstore_ghost_frame >>
  strip_tac >>
  `st.cs_current_bb = su.cs_current_bb /\
   LENGTH st.cs_current_insts = SUC (LENGTH su.cs_current_insts)` by
    gvs[emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  `!i. ~(w2n a <= i /\ i < w2n a+32) ==>
    mem_bytes_at i 1 (mstore (w2n a) w s).vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     decide_tac) >>
  `!m. mem_agree_outside (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})
      (mstore (w2n a) w s).vs_memory m ==> val_in_memory tv v (w2n a) m` by
    (rpt strip_tac >> irule annassign_clean_store_layout_ptr >>
     simp[] >> qexistsl [`s`, `tn.t_mem`, `w`] >> simp[]) >>
  qexistsl [`tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}`,
            `(mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[]) >>
  simp[] >>
  simp[venomStateTheory.mstore_def, venomStateTheory.lookup_var_def,
       ptrDisciplineTheory.op_taint_def, venom_state_component_equality]
QED

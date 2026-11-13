(* Interior stores into the preallocated custom-error tuple buffer. *)
Theory stmtSimCustomErrorPtrStoreHead
Ancestors
  stmtSimCustomErrorPtrUnwrap bodyMemAggregateStore bodyExprPreFacts
  annAssignPtrDestinationFrame annAssignPtrExterior annAssignPtrStore
  annAssignPtrMemorySource bodyImmutableAugAssignStore exprSimBufferStore
  externalReturnBufferlessNormalize
  bodyPtrDefs freshWrites loweringStateRelDefs venomState finite_map pred_set

Theorem custom_error_pure_store_dispatch:
  !ce e env src dst tops.
    supported_pure_expr tops e /\ well_typed_expr env e ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
      (if is_word_type (expr_type e) then emit_void MSTORE [dst; src]
       else if is_bytestring_type (expr_type e) then compile_store_bytestring src dst
       else compile_copy_memory dst src (type_memory_bytes ce (expr_type e)))
Proof
  rpt strip_tac >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
   compile_store_memory ce src dst (expr_type e) (expr_type e)` by
    metis_tac[aggregate_mem_store_lowered_elem] >>
  asm_rewrite_tac[] >> simp[contextTheory.compile_store_memory_def]
QED

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

(* Nonword stores use the run-time bytestring length, not the reserved capacity. *)
Theorem custom_error_nonword_store_path_ptr[local]:
  compile_store_memory ce (Var src) (Var dst) typ typ su = ((),st) /\
  fn_has_code su st func /\ ~is_word_type typ /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
  not_fresh_at su src /\ not_fresh_at su dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  nb = type_memory_bytes ce typ /\ nb = type_memory_size tv /\ nb < dimword (:256) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx typ v (Var src) G tn s /\
  (~is_bytestring_type typ /\ nb <> 0 ==> ptr_covers G tn src s nb) /\
  ptr_covers G tn dst s nb ==>
  !D PG. ?Gf tf t k.
    k <= nb /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK t) /\
    t.vs_current_bb = st.cs_current_bb /\ t.vs_inst_idx = LENGTH st.cs_current_insts /\
    ~t.vs_halted /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!z. not_fresh_at su z ==> lookup_var z t = lookup_var z s /\
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> rpt gen_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def, venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  Cases_on `is_bytestring_type typ`
  >- (`val_in_memory tv v (w2n a) s.vs_memory` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      drule_all exprSimBufferStoreTheory.buffer_typed_bytestring_header >>
      disch_then (qx_choose_then `len` strip_assume_tac) >>
      `val_footprint tv v <> 0` by
        (`(?n. tv = BaseTV (BytesT (Dynamic n))) \/
          (?n. tv = BaseTV (StringT n))` by
           metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
         Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
           loweringPostsTheory.val_footprint_def]) >>
      `ptr_covers G tn src s (32 + 32 * ((len+31) DIV 32))` by
        (gvs[ptr_val_ok_def, ptr_mem_ok_def, ptr_covers_def,
             eval_operand_def, vfmConstantsTheory.word_size_def] >> metis_tac[]) >>
      drule_all annAssignPtrMemorySourceTheory.annassign_bytestring_window_ptr >>
      disch_then (qx_choose_then `otherlen` strip_assume_tac) >>
      qpat_x_assum `mload _ _ = n2w otherlen` kall_tac >>
      `32 + 32 * ((len+31) DIV 32) <= nb` by
        metis_tac[exprSimPropsTheory.val_store_size_le, vfmConstantsTheory.word_size_def] >>
      `val_footprint tv v <= 32 + 32 * ((len+31) DIV 32)` by
        metis_tac[exprSimPropsTheory.val_footprint_le_store_size,
          vfmConstantsTheory.word_size_def] >>
      `ptr_covers G tn src s (32 + 32 * ((len+31) DIV 32)) /\
       ptr_covers G tn dst s (32 + 32 * ((len+31) DIV 32))` by
        (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
          arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
      `32 + 32 * ((len+31) DIV 32) < dimword (:256)` by decide_tac >>
      `if is_bytestring_type typ then
         32 + 32 * ((len+31) DIV 32) = 32 + 32 * ((len+31) DIV 32) /\
         mload (w2n a) s = n2w len /\
         (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)
       else 32 + 32 * ((len+31) DIV 32) = type_memory_bytes ce typ` by simp[] >>
      qpat_x_assum `ptr_covers G tn dst s nb` kall_tac >>
      drule_all (SRULE [] (Q.INST [`sty` |-> `ty`]
        (SPEC_ALL annAssignPtrDestinationTheory.annassign_store_memory_path_ptr))) >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl [`Gf`, `tnf`, `sf`, `32 + 32 * ((len+31) DIV 32)`] >> simp[] >>
      qpat_x_assum `!i. _ ==> mem_bytes_at i 1 sf.vs_memory = _ /\ _` mp_tac >>
      simp[]) >>
  Cases_on `nb = 0` >- suspend "zero" >>
  `ptr_covers G tn src s nb` by simp[] >>
  `val_footprint tv v <= nb` by simp[exprSimPropsTheory.val_footprint_le] >>
  `if is_bytestring_type typ then
     nb = 32 + 32 * ((0+31) DIV 32) /\ mload (w2n a) s = n2w 0 /\
     (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)
   else nb = type_memory_bytes ce typ` by simp[] >>
  drule_all (SRULE [] (Q.INST [`sty` |-> `ty`]
    (SPEC_ALL annAssignPtrDestinationTheory.annassign_store_memory_path_ptr))) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`, `sf`, `nb`] >> simp[] >>
  qpat_x_assum `!i. _ ==> mem_bytes_at i 1 sf.vs_memory = _ /\ _` mp_tac >> simp[]
QED

Resume custom_error_nonword_store_path_ptr[zero]:
  `st = su` by
    gvs[contextTheory.compile_store_memory_def,
        contextPropsTheory.compile_copy_memory_zero] >>
  qexistsl [`G`,`tn`,`s`,`0`] >> simp[] >>
  conj_tac >- metis_tac[cj 1 fragGasPathPtrTheory.gas_path_ptr_rules] >>
  metis_tac[return_zero_wf_memory]
QED
Finalise custom_error_nonword_store_path_ptr

Theorem custom_error_store_head_path_ptr:
  compile_store_memory ce op (Var y) typ typ su = ((),st) /\
  fn_has_code su st func /\ ~ce.ce_is_ctor /\
  stmt_state_rel ctx func ce cx ee s /\
  ghost_inv d ce cx ee G tn s /\
  ghost_kept ce ee sr G0 tn0 sref G tn /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
  expr_val_rel cx typ v op s /\ ptr_val_ok cx typ v op G tn s /\
  nb = type_memory_bytes ce typ /\ nb = type_memory_size tv /\
  nb < dimword (:256) /\ (is_word_type typ ==> nb = 32) /\
  (~is_word_type typ ==> ?z. op = Var z /\ not_fresh_at su z /\
    (~is_bytestring_type typ /\ nb <> 0 ==> ptr_covers G tn z s nb)) /\
  not_fresh_at su y /\ lookup_var y s = SOME (n2w a) /\
  ptr_covers G tn y s nb /\ a+nb < dimword (:256) /\
  (!n lo sz i. local_region ce ee.scopes s n lo sz /\
    lo <= i /\ i < lo+sz ==> ~(a <= i /\ i < a+nb)) /\
  (!aid lo sz i. FLOOKUP sref.vs_allocas aid = SOME (lo,sz) /\
    aid < sr.cs_next_id /\ lo <= i /\ i < lo+sz ==> ~(a <= i /\ i < a+nb)) /\
  (!n lo sz i. local_region ce ee.scopes sref n lo sz /\
    lo <= i /\ i < lo+sz ==> ~(a <= i /\ i < a+nb)) /\
  (!z. not_fresh_at sr z ==> not_fresh_at su z) /\
  (!name entry z sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
  (!z. ce.ce_imm_alloca = SOME (Var z) ==> not_fresh_at su z) ==>
  !D PG. ?Gf tf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK t) /\
    t.vs_current_bb = st.cs_current_bb /\ t.vs_inst_idx = LENGTH st.cs_current_insts /\
    ~t.vs_halted /\ stmt_state_rel ctx func ce cx ee t /\
    ghost_inv d ce cx ee Gf tf t /\ ghost_kept ce ee sr G0 tn0 sref Gf tf /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!z. not_fresh_at su z ==> lookup_var z t = lookup_var z s /\
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
    (!i. ~(a <= i /\ i < a+nb) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v a m)
Proof
  strip_tac >> rpt gen_tac >>
  `a < dimword (:256)` by decide_tac >>
  `w2n (n2w a:256 word) = a` by simp[wordsTheory.w2n_n2w] >>
  Cases_on `is_word_type typ`
  >- suspend "word"
  >> suspend "memory"
QED

Resume custom_error_store_head_path_ptr[word]:
  `nb = 32` by simp[] >>
  `emit_void MSTORE [Var y; op] su = ((),st)` by
    fs[contextTheory.compile_store_memory_def] >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    fs[loweringPostsTheory.expr_val_rel_def] >>
  `val_wf tv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `!u. val_in_memory tv v (w2n (n2w a:256 word))
      (mstore (w2n (n2w a:256 word)) (typed_val_to_w256 tv v) u).vs_memory` by
    (gen_tac >> drule_all immutable_augassign_word_representation >> metis_tac[]) >>
  `ptr_covers G tn y s 32` by metis_tac[] >>
  drule_all custom_error_mstore_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `!z. not_fresh_at su z ==> lookup_var z t = lookup_var z s /\
    FLOOKUP G z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)` by simp[] >>
  `!i. ~(a <= i /\ i < a+nb) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by metis_tac[] >>
  drule_all custom_error_slice_store_frame_ptr >> strip_tac >>
  qexistsl [`G`, `tf`, `t`] >> simp[] >> metis_tac[]
QED

Resume custom_error_store_head_path_ptr[memory]:
  `?z. op = Var z /\ not_fresh_at su z /\
    (~is_bytestring_type typ /\ nb <> 0 ==> ptr_covers G tn z s nb)` by simp[] >>
  qpat_x_assum `op = Var z` SUBST_ALL_TAC >>
  `?w. lookup_var z s = SOME w` by
    gvs[loweringPostsTheory.expr_val_rel_def, eval_operand_def] >>
  drule_all custom_error_nonword_store_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `!i. ~(a <= i /\ i < a+nb) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     `~(w2n (n2w a:256 word) <= i /\ i < w2n (n2w a:256 word)+k)` by
       (simp[] >> decide_tac) >> metis_tac[]) >>
  drule_all custom_error_slice_store_frame_ptr >> strip_tac >>
  qexistsl [`Gf`, `tf`, `t`] >> simp[] >> metis_tac[]
QED
Finalise custom_error_store_head_path_ptr

(* Read-only pointer frames used by log topic consumers. *)
Theory logTopicFramePtr
Ancestors
  logTopicPtr logValueFramePtr logGhostFramePtr bodyPtrDefs stmtFragPtr
  compileEnv exprLoweringProps context venomState ptrDiscipline finite_map words
  stmtSimLogTopics stmtLowering valueEncoding valueEncodingProofs loweringPosts
  vyperTyping vyperValue vyperTypeSystem representationCleanPtr arithmetic list supportedTypes

Theorem ghost_kept_readonly_transport:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ sa.cs_next_var <= sm.cs_next_var /\
  tm.t_mem = tn.t_mem /\
  (!p. not_fresh_at sm p ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) ==>
  ghost_kept cenv es sa G0 tn0 s0 H tm
Proof
  rw[ghost_kept_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem ghost_inv_readonly_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!p. not_fresh_at sm p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d cenv cx es H tm t
Proof
  simp[ghost_inv_def, local_ptrs_reserved_def] >> strip_tac >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >-
    (Cases_on `d` >- simp[return_buf_ptr_def] >>
     PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]) >>
  gvs[stor_taint_ok_def]
QED

Theorem ptr_val_ok_log_bytestring_window:
  ptr_val_ok cx ty v op G tn s /\ supported_scalar_type ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand op s = SOME a /\ mem_word_at (w2n a) s.vs_memory = n2w n /\
  n < dimword(:256) ==>
  ?src. op = Var src /\ ptr_covers G tn src s (32+n) /\
    (!i. w2n a <= i /\ i < w2n a + 32+n ==> i NOTIN tn.t_mem)
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def, is_bytestring_type_def]
  >~ [`BaseT (BytesT bd)`]
  >- (Cases_on `bd` >>
      simp[supported_word_type_def, supported_string_type_def, is_bytestring_type_def] >>
      suspend "bytes") >>
  suspend "string"
QED
Resume ptr_val_ok_log_bytestring_window[bytes]:
  simp[evaluate_type_def] >> strip_tac >> Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `BytesV bs` >> rename1 `Dynamic cap` >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n a) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def, evaluate_type_def] >> metis_tac[]) >>
  `mem_word_at (w2n a) s.vs_memory = n2w (LENGTH bs)` by
    (first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, val_in_memory_def]) >>
  `n = LENGTH bs` by (gvs[n2w_11] >> decide_tac) >> gvs[] >>
  `?p. op = Var p /\ ptr_covers G tn p s (32+LENGTH bs)` by
    (irule ptr_val_ok_read_covers >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`cx`, `BaseTV (BytesT (Dynamic cap))`,
                  `BaseT (BytesT (Dynamic cap))`, `BytesV bs`] >>
     simp[evaluate_type_def, is_word_type_def, val_footprint_def]) >>
  qexists_tac `p` >> simp[] >>
  conj_tac >- metis_tac[ADD_COMM] >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  rpt strip_tac >> Cases_on `i < w2n a + 32` >> metis_tac[LESS_EQ, NOT_LESS]
QED
Resume ptr_val_ok_log_bytestring_window[string]:
  simp[evaluate_type_def] >> strip_tac >> Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `StringV str` >> rename1 `StringT cap` >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory (BaseTV (StringT cap)) (StringV str) (w2n a) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def, evaluate_type_def] >> metis_tac[]) >>
  `mem_word_at (w2n a) s.vs_memory = n2w (LENGTH str)` by
    (first_x_assum (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, val_in_memory_def]) >>
  `n = LENGTH str` by (gvs[n2w_11] >> decide_tac) >> gvs[] >>
  `?p. op = Var p /\ ptr_covers G tn p s (32+LENGTH str)` by
    (irule ptr_val_ok_read_covers >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`cx`, `BaseTV (StringT cap)`,
                  `BaseT (StringT cap)`, `StringV str`] >>
     simp[evaluate_type_def, is_word_type_def, val_footprint_def]) >>
  qexists_tac `p` >> simp[] >> conj_tac >- metis_tac[ADD_COMM] >>
  drule robust_val_in_memory_string_clean >> simp[] >> strip_tac >>
  rpt strip_tac >> Cases_on `i < w2n a + 32` >> metis_tac[LESS_EQ, NOT_LESS]
QED
Finalise ptr_val_ok_log_bytestring_window

Theorem log_bytestring_arg_view_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sb es s (op,ty) v /\
  supported_scalar_type ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx ty v op G tn s ==>
  ?src b bs. op = Var src /\ eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    encode_event_topic ty v = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    ptr_covers G tn src s (32 + LENGTH bs) /\
    (!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all log_bytestring_arg_view >> strip_tac >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  `mem_word_at (w2n (n2w b : bytes32)) s.vs_memory = n2w (LENGTH bs)` by simp[] >>
  drule_all ptr_val_ok_log_bytestring_window >> simp[] >> strip_tac >>
  qexistsl_tac [`src`, `b`, `bs`] >> simp[]
QED

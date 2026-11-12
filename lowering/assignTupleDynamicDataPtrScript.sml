Theory assignTupleDynamicDataPtr
Ancestors
  assignTuplePtrLocalFixedCopy assignTuplePtrLocalBytesCopy augAssignPtrScalarRun
  augAssignPtrScalarSafety augAssignPtrScalarCertificate
  bodyPtrDefs fragExecPtr fragGasSeqPtr ptrDiscipline ptrSafeRun ghostPcTransportPtr
  instIdxIndep
  venomExecSemantics venomInstProofs venomState venomInst
  exprSimBufferStore exprLoweringProps finite_map pred_set list words arithmetic

Triviality dynamic_data_mul:
  lookup_var len s = SOME (n2w n) /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  ~ctx_has_dalloca ctx ==>
  ?H tm.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MUL [Var len; Lit (n2w stride)] [sz]] s H tm /\
    run_inst_seq [mk_inst id MUL [Var len; Lit (n2w stride)] [sz]] s =
      OK (update_var sz (n2w (n * stride)) s) /\
    op_prov H (Var sz) = NONE /\ op_taint tm (Var sz) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> sz ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `scalar_code {len} [mk_inst id MUL [Var len; Lit (n2w stride)] [sz]]` by
    simp[scalar_code_def, scalar_shape_def, scalar_binary_def,
         scalar_available_def, mk_inst_def] >>
  `!v. v IN {len} ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}` by simp[] >>
  `run_inst_seq [mk_inst id MUL [Var len; Lit (n2w stride)] [sz]] s =
    OK (update_var sz (n2w (n * stride)) s)` by
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def, word_mul_n2w] >>
  drule_all scalar_code_inst_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`, `s`] strip_assume_tac) >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  drule scalar_seq_success_clean >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`H`, `tm`] >> gvs[mk_inst_def]
QED

(* The raw sequence leaves its cursor unchanged; inst_seq_ptr advances the
   cursor between instructions. Both claims describe the same concrete copy. *)
Theorem dynamic_data_copy_sequence_ptr:
  lookup_var len s = SOME (n2w n) /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  sz <> src /\ sz <> dst /\ sz <> len /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n * stride < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s (n * stride) /\ ptr_covers G tn dst s (n * stride) ==>
  ?H tm u tf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MUL [Var len; Lit (n2w stride)] [sz];
       mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []] s H tf /\
    run_inst_seq
      [mk_inst id MUL [Var len; Lit (n2w stride)] [sz];
       mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []] s =
      OK (mcopy (w2n b) (w2n a) (n * stride) u) /\
    u = update_var sz (n2w (n * stride)) s /\
    tf = step_taint (mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []) u
      (mcopy (w2n b) (w2n a) (n * stride) u) tm /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. p <> sz ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> mp_tac dynamic_data_mul >>
  (impl_tac >- simp[]) >> strip_tac >>
  qabbrev_tac `u = update_var sz (n2w (n * stride)) s` >>
  `lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
   eval_operand (Var sz) u = SOME (n2w (n * stride))` by
    gvs[Abbr `u`, lookup_var_def, update_var_def, eval_operand_def, FLOOKUP_UPDATE] >>
  `ptr_covers H tm src u (n * stride) /\ ptr_covers H tm dst u (n * stride)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG H tm
      [mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []]
      (u with vs_inst_idx := k) H
      (step_taint (mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []) u
        (mcopy (w2n b) (w2n a) (n * stride) u) tm)` by
    (gen_tac >>
     `mcopy (w2n b) (w2n a) (n * stride) (u with vs_inst_idx := k) =
       mcopy (w2n b) (w2n a) (n * stride) u with vs_inst_idx := k` by
       simp[mcopy_def, write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
     `w2n (n2w (n * stride) : bytes32) = n * stride` by simp[] >>
     qsuff_tac `inst_seq_ptr D 0 ctx fn PG H tm
       [mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []]
       (u with vs_inst_idx := k) H
       (step_taint (mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] [])
         (u with vs_inst_idx := k)
         (mcopy (w2n b) (w2n a) (w2n (n2w (n * stride) : bytes32))
           (u with vs_inst_idx := k)) tm)` >- simp[] >>
     irule (cj 1 mcopy_operand_seq_ptr) >>
     gvs[eval_operand_def, lookup_var_def]) >>
  qexistsl_tac [`H`, `tm`, `u`,
    `step_taint (mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []) u
      (mcopy (w2n b) (w2n a) (n * stride) u) tm`] >>
  conj_tac >-
    (irule (assignTuplePtrLocalBytesCopyTheory.inst_seq_ptr_append_run
       |> Q.SPEC `[mk_inst id MUL [Var len; Lit (n2w stride)] [sz]]`
       |> SRULE []) >>
     gvs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `run_inst_seq [_] s = OK u` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, word_mul_n2w, Abbr `u`,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]
QED

Theorem dynamic_data_copy_frames_ptr:
  lookup_var len s = SOME (n2w n) /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  sz <> src /\ sz <> dst /\ sz <> len /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n * stride < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s (n * stride) /\ ptr_covers G tn dst s (n * stride) ==>
  ?H tf t.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MUL [Var len; Lit (n2w stride)] [sz];
       mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []] s H tf /\
    run_inst_seq
      [mk_inst id MUL [Var len; Lit (n2w stride)] [sz];
       mk_inst (id+1) MCOPY [Var dst; Var src; Var sz] []] s = OK t /\
    t = mcopy (w2n b) (w2n a) (n * stride)
      (update_var sz (n2w (n * stride)) s) /\
    (t with vs_memory := s.vs_memory) = update_var sz (n2w (n * stride)) s /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!off k. off + k <= n * stride ==>
      mem_bytes_at (w2n b + off) k t.vs_memory =
      mem_bytes_at (w2n a + off) k s.vs_memory) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n * stride) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i < n * stride ==>
      (w2n b + i IN tf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n * stride) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!p. p <> sz ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  mp_tac dynamic_data_copy_sequence_ptr >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`H`, `tf`, `mcopy (w2n b) (w2n a) (n * stride) u`] >>
  `eval_operand (Var src) u = SOME a /\ eval_operand (Var dst) u = SOME b /\
   eval_operand (Var sz) u = SOME (n2w (n * stride)) /\
   w2n (n2w (n * stride) : bytes32) = n * stride` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_at (Pat `tn' = step_taint _ _ _ _`) mcopy_operand_taint_frames_ptr >>
  simp[] >> strip_tac >>
  conj_tac >-
    simp[mcopy_def, write_memory_with_expansion_def, write_memory_def,
         expand_memory_def, update_var_def, venom_state_component_equality] >>
  conj_tac >-
    (rpt strip_tac >>
     `s.vs_memory = (update_var sz (n2w (n * stride)) s).vs_memory` by simp[update_var_def] >>
     pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     irule (buffer_mcopy_window |> ONCE_REWRITE_RULE [ADD_COMM]) >> decide_tac) >>
  conj_tac >-
    (rpt strip_tac >>
     `s.vs_memory = (update_var sz (n2w (n * stride)) s).vs_memory` by simp[update_var_def] >>
     pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     irule buffer_mcopy_exterior >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  gvs[mcopy_def, write_memory_with_expansion_def, write_memory_def,
      expand_memory_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]
QED

(* Clean input/output windows for flat decoder members.  This interface does
   not require unused output capacity to be initialized. *)
Theory abiDecodePtrMemberFrame
Ancestors
  assignTuplePtrBytesCopy assignTuplePtrLocalFixedCopy assignTuplePtrStageFrame
  typedCopyPtr bodyPtrDefs ptrDiscipline fragGasSeqPtr emitHelperProps
  exprSimBufferStore bodyPtrHashBuiltinsGhostFrame valueEncodingProps
  venomExecSemantics venomState venomInst compileEnv context
  finite_map pred_set words arithmetic list fragExecPtr decoderGhostFramePtr
  venomInstProofs exprLoweringProps valueCopy assignTuplePtrCopyLen
  immutableMemoryFrame

Definition abi_decode_ptr_window_def:
  abi_decode_ptr_window G tn s p b n <=>
    lookup_var p s = SOME b /\ ptr_covers G tn p s n /\
    (!i. w2n b <= i /\ i < w2n b+n ==> i NOTIN tn.t_mem)
End

(* A window is insensitive to writes outside it, even when taint elsewhere
   changes.  It can be used for the source and for earlier output members. *)
Theorem abi_decode_ptr_window_frame:
  abi_decode_ptr_window G tn s p b n /\
  lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
  op_taint tn' (Var p) = op_taint tn (Var p) /\
  (!i. w2n b <= i /\ i < w2n b+n ==>
    (i IN tn'.t_mem <=> i IN tn.t_mem)) ==>
  abi_decode_ptr_window G' tn' t p b n
Proof
  strip_tac >> gvs[abi_decode_ptr_window_def, ptr_covers_def] >> metis_tac[]
QED

(* The count may be a loaded runtime word, not just a literal. *)
Theorem abi_decode_ptr_copy_windows:
  emit_void MCOPY [Var dst; Var src; count_op] sa = ((),sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s src a h /\ k <= h /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s k /\
  eval_operand count_op s = SOME (n2w k) /\ k < dimword(:256) /\
  op_taint tn count_op = {} /\
  (w2n a+h <= w2n b \/ w2n b+k <= w2n a) ==>
  ?tn' t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    abi_decode_ptr_window G tn' t dst b k /\
    abi_decode_ptr_window G tn' t src a h /\
    (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!p. lookup_var p t = lookup_var p s /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var src s = SOME a /\ ptr_covers G tn src s h /\
   (!i. w2n a <= i /\ i < w2n a+h ==> i NOTIN tn.t_mem)` by
    fs[abi_decode_ptr_window_def] >>
  `ptr_covers G tn src s k` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  drule_all emit_mcopy_frames_normalized_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`tn'`, `t`] >> simp[] >>
  conj_tac >- suspend "destination" >>
  conj_tac >- suspend "source" >>
  rpt strip_tac >> irule buffer_mcopy_exterior >> decide_tac
QED

Resume abi_decode_ptr_copy_windows[destination]:
  simp[abi_decode_ptr_window_def] >> conj_tac
  >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `i - w2n b < k /\ i = w2n b + (i - w2n b)` by decide_tac >>
  qpat_x_assum `!i. i < k ==> _` (qspec_then `i - w2n b` mp_tac) >>
  simp[] >> strip_tac >>
  `w2n a <= w2n a + (i-w2n b) /\ w2n a + (i-w2n b) < w2n a+h` by
    decide_tac >> metis_tac[]
QED

Resume abi_decode_ptr_copy_windows[source]:
  irule abi_decode_ptr_window_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!i. ~(w2n b <= i /\ i < w2n b+k) ==> _` irule >>
  decide_tac
QED

Finalise abi_decode_ptr_copy_windows

(* A store's frame includes the entire exterior, not just covered windows. *)
Definition abi_decode_ptr_write_frame_def:
  abi_decode_ptr_write_frame tn s tn' t off k <=>
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. lookup_var p t = lookup_var p s) /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a n. a+n <= off \/ off+k <= a ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!i. ~(off <= i /\ i < off+k) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem))
End

Theorem abi_decode_ptr_mstore_frame:
  lookup_var dst s = SOME b /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  abi_decode_ptr_write_frame tn s
    (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n b) w s) tn)
    (mstore (w2n b) w s with vs_inst_idx := idx) (w2n b) 32
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  simp[abi_decode_ptr_write_frame_def, step_taint_nonmemory_frame, mk_inst_def] >>
  conj_tac >- simp[mstore_def, venom_state_component_equality] >>
  conj_tac >- simp[mstore_def, lookup_var_def] >>
  conj_tac >- simp[immutable_mstore_capacity, MAX_DEF] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem abi_decode_ptr_store_windows:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  abi_decode_ptr_window G tn s src a h /\
  (w2n a+h <= w2n b \/ w2n b+32 <= w2n a) ==>
  ?tn' t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tn' /\
    abi_decode_ptr_window G tn' t dst b 32 /\
    abi_decode_ptr_window G tn' t src a h /\
    abi_decode_ptr_write_frame tn s tn' t (w2n b) 32 /\
    (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!p. lookup_var p t = lookup_var p s /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var dst) s = SOME b` by simp[eval_operand_def] >>
  drule_all emit_mstore_run >> strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  qexistsl_tac [`step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
    s (mstore (w2n b) w s) tn`,
    `mstore (w2n b) w s with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by
    (drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `((mstore (w2n b) w s with vs_inst_idx := LENGTH sb.cs_current_insts)
      with vs_inst_idx := s.vs_inst_idx) = mstore (w2n b) w s /\
   (mstore (w2n b) w s).vs_current_bb = s.vs_current_bb /\
   (!p. lookup_var p (mstore (w2n b) w s with
     vs_inst_idx := LENGTH sb.cs_current_insts) = lookup_var p s)` by
    simp[mstore_def, lookup_var_def, venom_state_component_equality] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  simp[op_taint_def] >>
  conj_tac >- suspend "store_seq" >>
  conj_tac >- suspend "store_destination" >>
  conj_tac >- suspend "store_source" >>
  conj_tac >- (irule abi_decode_ptr_mstore_frame >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[step_taint_nonmemory_frame, mk_inst_def]
QED

Resume abi_decode_ptr_store_windows[store_seq]:
  drule emitted_insts_emit_void >> strip_tac >>
  simp[inst_seq_ptr_def] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s =
   OK (mstore (w2n b) w s)` by (irule step_MSTORE >> simp[]) >>
  simp[] >> irule ptr_inst_ok_mstore >> simp[]
QED

Resume abi_decode_ptr_store_windows[store_destination]:
  `op_taint tn (Var dst) = {}` by fs[ptr_covers_def] >>
  simp[abi_decode_ptr_window_def, ptr_covers_def, op_taint_def] >>
  simp[lookup_var_def, mstore_def] >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def]
QED

Resume abi_decode_ptr_store_windows[store_source]:
  irule abi_decode_ptr_window_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >>
  simp[lookup_var_def, op_taint_def, mstore_def] >> rpt strip_tac >>
  decide_tac
QED

Finalise abi_decode_ptr_store_windows

(* An uninitialized output allocation is allowed: the frame describes only
   the written interval.  Runtime and ghost fields outside memory are kept. *)

(* No robust observation is reconstructed from an ordinary value assertion:
   the exterior ghost theorem transports the original robust observation. *)
Theorem abi_decode_ptr_write_preserves:
  abi_decode_ptr_write_frame tn s tn' t off k /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!name b n. local_region cenv es.scopes s name b n ==>
    b+n <= off \/ off+k <= b) /\
  (cenv.ce_is_ctor ==> !name tv v b.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc b) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint b (type_memory_size tv) off k) ==>
  stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es G tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decode_ptr_write_frame _ _ _ _ _ _` mp_tac >>
  simp[abi_decode_ptr_write_frame_def] >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx es (t with vs_inst_idx := s.vs_inst_idx)` by
    (irule buffer_store_state_frame >>
     qexistsl_tac [`off`, `k`, `s`, `sa`] >>
     fs[lookup_var_def, ADD_COMM] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[stmt_state_rel_inst_idx] >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient` by
    (qpat_x_assum `(t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>) = s`
      mp_tac >> simp[venom_state_component_equality] >> metis_tac[]) >>
  `stor_taint_ok cx tn' t` by fs[ghost_inv_def, stor_taint_ok_def] >>
  irule hash_ghost_inv_exterior_frame >> simp[] >>
  qexistsl_tac [`G`, `ctx`, `fn`, `s`, `sa`, `tn`,
    `{i | off <= i /\ i < off+k}`] >>
  simp[op_taint_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b n. local_region _ _ _ _ _ _ ==> _` drule >>
      decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED


Theorem abi_decode_ptr_mcopy_frame:
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  eval_operand count_op s = SOME n ==>
  abi_decode_ptr_write_frame tn s
    (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (mcopy (w2n b) (w2n a) (w2n n) s with vs_inst_idx := idx)
    (w2n b) (w2n n)
Proof
  strip_tac >>
  `eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a` by
    simp[eval_operand_def] >>
  `!tn'. tn' = step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn ==>
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i < w2n n ==> (w2n b+i IN tn'.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+w2n n) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem))` by
    (gen_tac >> disch_tac >> irule mcopy_operand_taint_frames_ptr >>
     qexistsl_tac [`count_op`, `Var dst`, `id`, `n`, `s`, `Var src`] >> simp[]) >>
  first_x_assum (qspec_then
    `step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn` mp_tac) >>
  simp[] >> strip_tac >> simp[abi_decode_ptr_write_frame_def] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def,
                  venom_state_component_equality] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac >- simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF] >>
  rpt strip_tac >> simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint]
QED

(* Interface consumer: two disjoint writes retain initialized members and
   transport the original robust local observations through both steps. *)
Theorem abi_decode_ptr_two_writes:
  abi_decode_ptr_write_frame tn s tn1 t off1 k1 /\
  abi_decode_ptr_write_frame tn1 t tn2 u off2 k2 /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!name b n. local_region cenv es.scopes s name b n ==>
    b+n <= off1 \/ off1+k1 <= b) /\
  (!name b n. local_region cenv es.scopes t name b n ==>
    b+n <= off2 \/ off2+k2 <= b) /\
  (cenv.ce_is_ctor ==> !name tv v b.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc b) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint b (type_memory_size tv) off1 k1 /\
    regions_disjoint b (type_memory_size tv) off2 k2) /\
  abi_decode_ptr_window G tn1 t p a n /\
  abi_decode_ptr_window G tn2 u q b m /\
  (w2n a+n <= off2 \/ off2+k2 <= w2n a) ==>
  stmt_state_rel ctx fn cenv cx es u /\ ghost_inv d cenv cx es G tn2 u /\
  abi_decode_ptr_window G tn2 u p a n /\ abi_decode_ptr_window G tn2 u q b m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx fn cenv cx es t /\ ghost_inv d cenv cx es G tn1 t` by
    (irule abi_decode_ptr_write_preserves >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`k1`, `off1`, `s`, `tn`] >> fs[ADD_COMM] >> metis_tac[]) >>
  `stmt_state_rel ctx fn cenv cx es u /\ ghost_inv d cenv cx es G tn2 u` by
    (irule abi_decode_ptr_write_preserves >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`k2`, `off2`, `t`, `tn1`] >> fs[ADD_COMM] >> metis_tac[]) >>
  simp[] >> irule abi_decode_ptr_window_frame >>
  qexistsl_tac [`G`, `t`, `tn1`] >>
  fs[abi_decode_ptr_write_frame_def, op_taint_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

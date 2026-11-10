Theory rawCallBufferPtr
Ancestors
  wordLoadStorePtr bodyPtrDefs representationCleanPtr exprSimProps oracleCallStepPtr typedCopyPtr
  finite_map pred_set exprSimMemoryTransport valueEncodingProps valueEncodingProofs
  venomMemProofs list fragGasSeqPtr fragGasPathPtr fragExec gasCount decoderGhostFramePtr robustCopyTransportPtr

Theorem ptr_mem_ok_site:
  ptr_mem_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ val_footprint tv v <> 0 ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size tv v <= b + sz
Proof
  simp[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_mem_ok_dynamic_bytes_site:
  ptr_mem_ok cx ty (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 + LENGTH bs <= b + sz
Proof
  strip_tac >>
  `val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) <> 0` by
    simp[loweringPostsTheory.val_footprint_def] >>
  drule_all ptr_mem_ok_site >> strip_tac >>
  qexistsl_tac [`x`, `b`, `sz`] >> simp[] >>
  mp_tac (Q.SPECL [`BaseTV (BytesT (Dynamic n))`, `BytesV bs`]
    val_footprint_le_store_size) >>
  simp[loweringPostsTheory.val_footprint_def] >> decide_tac
QED

Theorem ptr_mem_ok_dynamic_bytes_clean:
  ptr_mem_ok cx ty (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  eval_operand op s = SOME w ==>
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n w) mem` by
    metis_tac[ptr_mem_ok_def] >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED


(* Opcode/operand interface, independent of instruction outputs and IDs. *)
Theorem revert_forward_pair_consecutive:
  get_instruction bb i = SOME copy /\
  get_instruction bb (SUC i) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\
  copy.inst_operands = [p; Lit 0w; rds] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [p; rds] ==>
  revert_forward_pair bb i (SUC i)
Proof
  strip_tac >>
  simp[contextCodegenRelTheory.revert_forward_pair_def,
    contextCodegenRelTheory.resolve_block_assigns_def,
    contextCodegenRelPropsTheory.same_after_assigns_refl] >>
  rpt strip_tac >> fs[]
QED

Theorem revert_forward_access_taint:
  in_revert_forward fn s /\ about_to_revert fn inst s /\
  (inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = REVERT) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  fs[ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
    listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_inst_ok_forward_revert:
  inst.inst_opcode = REVERT /\ inst.inst_operands = [p; n] /\
  in_revert_forward fn s /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn inst s
Proof
  strip_tac >>
  `access_ok 0 G fn inst s /\ taint_ok fn tn inst s` by
    (irule revert_forward_access_taint >>
     simp[ptrDisciplineTheory.about_to_revert_def]) >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem ptr_inst_ok_forward_copy:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [p; src; n] /\
  in_revert_forward fn s /\ about_to_revert fn inst s /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn inst s
Proof
  strip_tac >>
  `access_ok 0 G fn inst s /\ taint_ok fn tn inst s` by
    (irule revert_forward_access_taint >> simp[]) >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.allocas_from_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    venomStateTheory.write_memory_with_expansion_def,
    venomStateTheory.write_memory_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Capacity and live-byte representation are independent: padding need not
   be clean. These folds work for output bytes and inline result tuples. *)
Theorem ptr_val_ok_from_covers:
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ptr_covers G tn p s capacity /\ val_store_size tv v <= capacity /\
  (!w mem. lookup_var p s = SOME w /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_val_ok cx ty v (Var p) G tn s
Proof
  simp[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def,
    venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED

Theorem ptr_buf_ok_from_covers:
  ptr_covers G tn p s capacity /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= capacity ==>
  ptr_buf_ok cenv e (Var p) G s
Proof
  simp[ptr_covers_def, ptr_buf_ok_def, venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  qexistsl_tac [`b`, `sz'`] >> simp[] >> decide_tac
QED

Theorem clean_footprint_robust_val_in_memory:
  val_in_memory tv v b mem /\ val_wf tv v /\
  (!i. b <= i /\ i < b + val_footprint tv v ==> i NOTIN dirty) ==>
  !m. mem_agree_outside dirty mem m ==> val_in_memory tv v b m
Proof
  rpt strip_tac >> irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >> qexistsl_tac [`mem`, `b`] >> simp[] >>
  irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < val_footprint tv v` >>
  `b+j NOTIN dirty` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (b+j) 1 mem = mem_bytes_at (b+j) 1 m` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem bytes_length_store_representation:
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) b
    (mstore b (n2w (LENGTH bs)) s).vs_memory
Proof
  strip_tac >>
  `mem_bytes_at (b+32) (LENGTH bs)
    (mstore b (n2w (LENGTH bs)) s).vs_memory = bs` by
    (rewrite_tac[mstore_mem_bytes_at_disjoint
       |> Q.SPECL [`b+32`, `LENGTH bs`, `b`]
       |> SIMP_RULE (srw_ss()) []] >> simp[]) >>
  simp[valueEncodingDefsTheory.val_in_memory_def, mstore_mem_word_at_same]
QED

Theorem bytes_length_store_robust:
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  LENGTH bs <= cap /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN dirty) ==>
  !m. mem_agree_outside (dirty DIFF {i | b <= i /\ i < b+32})
    (mstore b (n2w (LENGTH bs)) s).vs_memory m ==>
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) b m
Proof
  rpt strip_tac >> irule clean_footprint_robust_val_in_memory >>
  conj_tac >-
    (simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def] >>
     mp_tac (Q.SPEC `cap` valueTypingMemoryPropsTheory.word_size_capacity) >>
     decide_tac) >>
  qexistsl_tac [`dirty DIFF {i | b <= i /\ i < b+32}`,
    `(mstore b (n2w (LENGTH bs)) s).vs_memory`] >>
  simp[bytes_length_store_representation, valueEncodingDefsTheory.val_wf_def,
    loweringPostsTheory.val_footprint_def] >>
  rpt strip_tac >> Cases_on `i < b+32` >> simp[] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

(* Unlike gas_path_ptr_abort, this boundary also accepts terminators. *)
Theorem gas_path_ptr_abort_instruction:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ptr_inst_ok D lo 0 ctx fn G tn inst s /\
  step_inst_base inst s = Abort a t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >> irule (cj 3 gas_path_ptr_rules) >>
  simp[exit_result_def] >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    gas_count_step_def, exit_result_def,
    ptrSafeRunTheory.ptr_safe_step_def]
QED

Theorem forwarding_pair_active:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb i = SOME copy /\
  get_instruction bb (SUC i) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\
  copy.inst_operands = [p; Lit 0w; rds] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [p; rds] /\
  (s.vs_inst_idx = i \/ s.vs_inst_idx = SUC i) ==>
  in_revert_forward fn s
Proof
  strip_tac >>
  `revert_forward_pair bb i (SUC i)` by
    (irule revert_forward_pair_consecutive >> metis_tac[]) >>
  simp[contextCodegenRelTheory.in_revert_forward_def] >>
  simp[contextCodegenRelTheory.revert_forward_at_def] >>
  metis_tac[]
QED

Theorem forwarding_copy_operand_taint:
  copy.inst_outputs = [] ==>
  op_taint (step_taint copy s u tn) op = op_taint tn op
Proof
  strip_tac >> Cases_on `op` >>
  simp[decoderGhostFramePtrTheory.step_taint_other_output,
    ptrDisciplineTheory.op_taint_def]
QED

(* The semantic step equations are supplied by the simulation; the pointer
   checks need neither provenance for the scratch region nor clean payload. *)
Theorem revert_forward_pair_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  copy.inst_operands = [p; Lit 0w; rds] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [p; rds] /\
  op_taint tn p = {} /\ op_taint tn rds = {} /\
  step_inst_base copy s = OK u /\
  step_inst_base rev (u with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G copy u) (step_taint copy s u tn) (Abort a t)
Proof
  strip_tac >>
  `step_inst 0 ctx copy s = OK u` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `~is_terminator copy.inst_opcode` by simp[venomInstTheory.is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (drule_all venomInstPropsTheory.step_preserves_halted >>
     drule_all venomInstPropsTheory.step_preserves_control_flow >> simp[]) >>
  `in_revert_forward fn s` by
    (irule forwarding_pair_active >> metis_tac[]) >>
  `about_to_revert fn copy s` by
    (simp[ptrDisciplineTheory.about_to_revert_def,
      contextCodegenRelTheory.active_inst_def] >>
     qexists_tac `rev` >> simp[] >> qexists_tac `bb` >>
     drule venomExecPropsTheory.lookup_block_MEM >>
     drule venomExecPropsTheory.lookup_block_label >>
     fs[venomInstTheory.get_instruction_def, AllCaseEqs()]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn copy s` by
    (irule ptr_inst_ok_forward_copy >>
     fs[ptrDisciplineTheory.op_taint_def]) >>
  qabbrev_tac `s' = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `in_revert_forward fn s'` by
    (irule forwarding_pair_active >> simp[Abbr `s'`] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn (step_prov PG G copy u)
     (step_taint copy s u tn) rev s'` by
    (irule ptr_inst_ok_forward_revert >>
     simp[forwarding_copy_operand_taint]) >>
  `gas_path_ptr D 0 ctx fn PG (step_prov PG G copy u)
    (step_taint copy s u tn) s' 0 (step_prov PG G copy u)
    (step_taint copy s u tn) (Abort a t)` by
    (irule gas_path_ptr_abort_instruction >> simp[Abbr `s'`] >> metis_tac[]) >>
  qunabbrev_tac `s'` >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
  simp[] >> metis_tac[]
QED

(* Copying an inline suffix may propagate padding taint: only robust
   element representations, not clean type-sized windows, are needed. *)
Theorem robust_pair_copied_suffix:
  val_wf ht hv /\ val_footprint ht hv <= type_memory_size ht /\
  val_wf tt tv /\ val_footprint tt tv <= n /\
  mem_bytes_at (b + type_memory_size ht) n mem' = mem_bytes_at a n mem /\
  (!i. i < n ==> (b + type_memory_size ht + i IN dirty' <=> a+i IN dirty)) /\
  (!i. ~(b + type_memory_size ht <= i /\ i < b + type_memory_size ht+n) ==>
    mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) /\
  (!i. ~(b + type_memory_size ht <= i /\ i < b + type_memory_size ht+n) ==>
    (i IN dirty' <=> i IN dirty)) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory ht hv b m) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tt tv a m) ==>
  !m. mem_agree_outside dirty' mem' m ==>
    val_in_memory (TupleTV [ht;tt]) (ArrayV (TupleV [hv;tv])) b m
Proof
  strip_tac >>
  `!m. mem_agree_outside dirty' mem' m ==>
    val_in_memory tt tv (b+type_memory_size ht) m` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`mem`, `mem'`, `n`, `a`, `dirty`, `dirty'`] >> simp[]) >>
  `!m. mem_agree_outside dirty' mem' m ==> val_in_memory ht hv b m` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
     qexistsl_tac [`mem`, `dirty`, `{i | b+type_memory_size ht <= i /\
       i < b+type_memory_size ht+n}`] >>
     simp[]) >>
  rpt strip_tac >> simp[valueEncodingDefsTheory.val_in_memory_def]
QED

Theorem robust_pair_mcopy:
  val_wf ht hv /\ val_footprint ht hv <= type_memory_size ht /\
  val_wf tt tv /\ val_footprint tt tv <= n /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory ht hv b m) /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory tt tv a m) ==>
  !m. mem_agree_outside
    ((dirty DIFF {i | b+type_memory_size ht <= i /\ i < b+type_memory_size ht+n})
      UNION {b+type_memory_size ht+i | i < n /\ a+i IN dirty})
    (mcopy (b+type_memory_size ht) a n s).vs_memory m ==>
    val_in_memory (TupleTV [ht;tt]) (ArrayV (TupleV [hv;tv])) b m
Proof
  rpt strip_tac >> irule robust_pair_copied_suffix >>
  simp[] >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  qexistsl_tac [`a`, `dirty`, `s.vs_memory`, `n`] >>
  simp[mcopy_mem_bytes_at_same] >>
  rpt conj_tac
  >- (rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >>
      decide_tac)
  >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem ptr_val_ok_from_type_covers:
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  ptr_covers G tn p s (type_memory_size tv) /\
  (!w mem. lookup_var p s = SOME w /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_val_ok cx ty v (Var p) G tn s
Proof
  strip_tac >> irule ptr_val_ok_from_covers >>
  conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[val_store_size_le] >> metis_tac[]
QED

Theorem raw_call_result_buffer_capacity:
  expr_type (Call ty (RawCallTarget flags) es ann) =
    (if tuple_result then TupleT [BaseT BoolT; BaseT (BytesT (Dynamic cap))]
     else BaseT (BytesT (Dynamic cap))) /\
  ptr_covers G tn p s
    ((if tuple_result then 32 else 0) + 32 + ((cap+31) DIV 32)*32) ==>
  ptr_buf_ok cenv (Call ty (RawCallTarget flags) es ann) (Var p) G s
Proof
  strip_tac >> irule ptr_buf_ok_from_covers >>
  goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[exprLoweringTheory.lowered_value_type_def] >>
  Cases_on `tuple_result` >>
  fs[compileEnvTheory.type_memory_bytes_def]
QED

Theorem bool_mstore_robust:
  !m. mem_agree_outside (dirty DIFF {i | b <= i /\ i < b+32})
    (mstore b (val_to_w256 (BoolV flag)) s).vs_memory m ==>
    val_in_memory (BaseTV BoolT) (BoolV flag) b m
Proof
  rpt strip_tac >> irule clean_footprint_robust_val_in_memory >>
  conj_tac >-
    simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def] >>
  qexistsl_tac [`dirty DIFF {i | b <= i /\ i < b+32}`,
    `(mstore b (val_to_w256 (BoolV flag)) s).vs_memory`] >>
  simp[valueEncodingDefsTheory.val_in_memory_def, mstore_mem_word_at_same,
    loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def]
QED

Theorem robust_pair_mcopy_step:
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME aw /\
  eval_operand count_op s = SOME nw /\
  w2n dw = b + type_memory_size ht /\
  val_wf ht hv /\ val_footprint ht hv <= type_memory_size ht /\
  val_wf tt tv /\ val_footprint tt tv <= w2n nw /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ht hv b m) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tt tv (w2n aw) m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n dw) (w2n aw) (w2n nw) s) tn).t_mem
    (mcopy (w2n dw) (w2n aw) (w2n nw) s).vs_memory m ==>
    val_in_memory (TupleTV [ht;tt]) (ArrayV (TupleV [hv;tv])) b m
Proof
  strip_tac >> simp[mcopy_operand_ghost_frame] >>
  gvs[] >> rpt strip_tac >> irule (SRULE [] robust_pair_mcopy) >> simp[] >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  qexists_tac `w2n nw` >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem bool_mstore_step_robust:
  lookup_var dst s = SOME a /\
  eval_operand value s = SOME (val_to_w256 (BoolV flag)) /\
  op_taint tn value = {} ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id MSTORE [Var dst;value] []) s
      (mstore (w2n a) (val_to_w256 (BoolV flag)) s) tn).t_mem
    (mstore (w2n a) (val_to_w256 (BoolV flag)) s).vs_memory m ==>
    val_in_memory (BaseTV BoolT) (BoolV flag) (w2n a) m
Proof
  strip_tac >> simp[mstore_ghost_frame] >>
  rpt strip_tac >> irule bool_mstore_robust >> simp[] >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`))
QED

Theorem robust_mstore_disjoint:
  val_wf tv v /\ (p + val_footprint tv v <= b \/ b+32 <= p) /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside (dirty DIFF {i | b <= i /\ i < b+32})
    (mstore b w s).vs_memory m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >>
  (irule robust_val_in_memory_exterior_frame >>
   conj_tac >- simp[] >>
   qexistsl_tac [`s.vs_memory`, `(mstore b w s).vs_memory`, `dirty`,
     `dirty DIFF {i | b <= i /\ i < b+32}`, `{i | b <= i /\ i < b+32}`] >>
   simp[] >> rpt strip_tac >>
   irule mstore_mem_bytes_at_disjoint >> decide_tac)
QED

(* The raw_call tuple stores its Boolean head before copying the bytes tail.
   Only the source's live footprint must be disjoint from that head store. *)
Theorem bool_pair_mstore_mcopy_robust:
  val_wf tt tv /\ val_footprint tt tv <= n /\
  (a + val_footprint tt tv <= b \/ b+32 <= a) /\
  (!m. mem_agree_outside dirty s.vs_memory m ==> val_in_memory tt tv a m) ==>
  !m. mem_agree_outside
    (((dirty DIFF {i | b <= i /\ i < b+32})
       DIFF {i | b+32 <= i /\ i < b+32+n}) UNION
      {b+32+i | i | i < n /\ a+i IN (dirty DIFF {j | b <= j /\ j < b+32})})
    (mcopy (b+32) a n (mstore b (val_to_w256 (BoolV flag)) s)).vs_memory m ==>
    val_in_memory (TupleTV [BaseTV BoolT;tt])
      (ArrayV (TupleV [BoolV flag;tv])) b m
Proof
  rpt strip_tac >>
  (irule (robust_pair_mcopy |> Q.INST [`ht` |-> `BaseTV BoolT`]
     |> SRULE [valueEncodingTheory.type_memory_size_def]) >>
   conj_tac >-
     simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
   conj_tac >- simp[] >>
   conj_tac >-
     simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def] >>
   qexistsl_tac [`a`, `dirty DIFF {i | b <= i /\ i < b+32}`, `n`,
     `mstore b (val_to_w256 (BoolV flag)) s`] >>
   simp[] >> conj_tac
   >- (rpt strip_tac >> irule robust_mstore_disjoint >> simp[] >>
       qexistsl_tac [`b`, `dirty`, `s`, `val_to_w256 (BoolV flag)`] >> simp[]) >>
   rpt strip_tac >> irule bool_mstore_robust >>
   goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)))
QED

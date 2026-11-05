Theory exprPtrUnwrapSingleton
Ancestors
  exprPtrUnwrapLoadSegment exprPtrUnwrapStoreSegment exprPtrUnwrapSeq
  exprPtrUnwrapFrames ghostPcTransportPtr slotCopyExecution fragGasSeqPtr
  fragExec bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst
  venomState finite_map exprLoweringProps instIdxIndep list valueEncodingProps
  exprSimStorageCopy venomMemProps valueEncoding

(* The actual singleton branch: a load directly followed by a store.
   The loaded word's taint is intentionally not required to be empty. *)
Theorem copy_singleton_segment:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  op_taint tn src = {} /\ root <> out /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id load [src] [out];
      mk_inst (id+1) MSTORE [Var root;Var out] []] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id load [src] [out];
       mk_inst (id+1) MSTORE [Var root;Var out] []] s Gf tnf /\
    t = mstore (w2n addr) (slot_copy_word load s key)
      (update_var out (slot_copy_word load s key) s) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p n. p <> out /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  mp_tac (Q.INST [`arg` |-> `src`] (SPEC_ALL copy_slot_load_segment)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `t = update_var _ _ _` SUBST_ALL_TAC >> (
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qabbrev_tac `u = update_var out (slot_copy_word load s key) s` >>
  qabbrev_tac `w = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers Gm tnm root w 32 /\
   eval_operand (Var root) w = SOME addr /\
   eval_operand (Var out) w = SOME (slot_copy_word load s key) /\
   allocas_from lo w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w)` by
    (fs[Abbr `w`, Abbr `u`, ptr_covers_inst_idx, eval_operand_def,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `w`, `G` |-> `Gm`, `tn` |-> `tnm`,
    `id` |-> `id+1`, `v` |-> `Var out`,
    `value` |-> `slot_copy_word load s key`] (SPEC_ALL copy_store_segment)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ w Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`, `mstore (w2n addr) (slot_copy_word load s key) u`] >>
  conj_tac
  >- (qspec_then `u.vs_inst_idx` mp_tac
        (Q.SPECL [`[mk_inst (id+1) MSTORE [Var root;Var out] []]`, `w`]
          run_inst_seq_inst_idx) >>
      simp[mk_inst_def, is_terminator_def, exec_result_map_def] >>
      simp[Abbr `w`, copy_mstore_inst_idx] >> strip_tac >>
      qpat_x_assum `run_inst_seq [mk_inst id load _ _] s = OK u`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `[mk_inst (id+1) MSTORE [Var root;Var out] []]` mp_tac) >>
      simp[mk_inst_def, mstore_def]) >>
  conj_tac
  >- (irule inst_seq_ptr_cons_compose >>
      conj_tac >- (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
      qexistsl_tac [`Gm`, `u`, `tnm`] >> gvs[Abbr `w`]) >>
  gvs[Abbr `w`, copy_mstore_inst_idx, ptr_covers_inst_idx,
      allocas_from_def, allocas_below_fmp_def] >> metis_tac[])
QED

Theorem copy_singleton_counted_path:
  (load=SLOAD \/ load=TLOAD) /\ eval_operand src s = SOME key /\
  op_taint tn src = {} /\ root <> out /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id load [src] [out];
    mk_inst (id+1) MSTORE [Var root;Var out] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
      (OK ((mstore (w2n addr) (slot_copy_word load s key)
        (update_var out (slot_copy_word load s key) s))
        with vs_inst_idx := s.vs_inst_idx+2)) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  mp_tac (SPEC_ALL copy_singleton_segment) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[] >>
  mp_tac (Q.INST [`code` |-> `[mk_inst id load [src] [out];
    mk_inst (id+1) MSTORE [Var root;Var out] []]`,
    `G'` |-> `Gf`, `tn'` |-> `tnf`] (SPEC_ALL run_inst_seq_gas_path_ptr)) >>
  (impl_tac >- (gvs[] >> simp[mk_inst_def, is_terminator_def])) >>
  gvs[] >> simp[mk_inst_def]
QED

(* Schematic endpoint projections also apply after the counted index update.
   The memory facts are inherited from the generic mstore interface. *)
Theorem copy_singleton_word:
  t = (mstore (w2n addr) (slot_copy_word load s key)
    (update_var out (slot_copy_word load s key) s)) with vs_inst_idx := ix ==>
  mem_word_at (w2n addr) t.vs_memory = slot_copy_word load s key
Proof
  strip_tac >> simp[mstore_mem_word_at_same]
QED

Theorem copy_singleton_exterior:
  t = (mstore (w2n addr) (slot_copy_word load s key)
    (update_var out (slot_copy_word load s key) s)) with vs_inst_idx := ix /\
  (a+n <= w2n addr \/ w2n addr+32 <= a) ==>
  mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory
Proof
  strip_tac >> simp[] >>
  irule EQ_TRANS >> irule_at (Pos hd) mstore_mem_bytes_at_disjoint >>
  simp[update_var_def]
QED

Theorem copy_singleton_runtime_frame:
  t = (mstore (w2n addr) (slot_copy_word load s key)
    (update_var out (slot_copy_word load s key) s)) with vs_inst_idx := ix ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\
  (!op. op <> Var out ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >> simp[mstore_def, update_var_def] >>
  Cases >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem copy_singleton_static:
  t = (mstore (w2n addr) (slot_copy_word load s key)
    (update_var out (slot_copy_word load s key) s)) with vs_inst_idx := ix ==>
  copy_static t = copy_static s
Proof
  simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem copy_singleton_memory_length:
  t = (mstore (w2n addr) (slot_copy_word load s key)
    (update_var out (slot_copy_word load s key) s)) with vs_inst_idx := ix ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp[LENGTH_mstore_eq, update_var_def]
QED

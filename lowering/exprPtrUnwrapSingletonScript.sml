(* Singleton copies retain the loaded slot's possibly nonempty taint. *)
Theory exprPtrUnwrapSingleton
Ancestors
  exprPtrUnwrapLoadSegment exprPtrUnwrapStoreSegment exprPtrUnwrapFrames
  ghostPcTransportPtr slotCopyExecution fragGasSeqPtr fragExec bodyPtrDefs
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  exprLoweringProps instIdxIndep list valueEncodingProps exprSimStorageCopy
  venomMemProps valueEncoding exprPtrUnwrapCopyEdges decoderGhostFramePtr

Theorem copy_singleton_execution:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  root <> out /\ lookup_var root s = SOME addr ==>
  run_inst_seq [mk_inst id load [src] [out];
    mk_inst (id+1) MSTORE [Var root;Var out] []] s =
  OK (mstore (w2n addr) (slot_copy_word load s key)
      (update_var out (slot_copy_word load s key) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id load [src] [out]) s =
     OK (update_var out (slot_copy_word load s key) s)` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
                   slot_copy_word_def]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var root;Var out] [])
     (update_var out (slot_copy_word load s key) s) =
     OK (mstore (w2n addr) (slot_copy_word load s key)
       (update_var out (slot_copy_word load s key) s))` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[] >> simp[run_inst_seq_def]
QED

Theorem copy_singleton_checks:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  op_taint tn src = {} /\ root <> out /\
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  u = update_var out (slot_copy_word load s key) s /\
  w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst id load [src] [out]) u /\
  tm = step_taint (mk_inst id load [src] [out]) s u tn ==>
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id load [src] [out];
     mk_inst (id+1) MSTORE [Var root; Var out] []] s
    (step_prov PG H (mk_inst (id+1) MSTORE [Var root; Var out] [])
      (mstore (w2n addr) (slot_copy_word load s key) w))
    (step_taint (mk_inst (id+1) MSTORE [Var root; Var out] []) w
      (mstore (w2n addr) (slot_copy_word load s key) w) tm)
Proof
  strip_tac >>
  `ptr_covers H tm root u 32` by
    (gvs[] >> irule ptr_covers_step_frame >>
     fs[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_inst_ok D lo 0 ctx fn H tm
     (mk_inst (id+1) MSTORE [Var root; Var out] []) w` by
    (irule ptr_inst_ok_mstore_tainted >>
     gvs[ptr_covers_inst_idx]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id load [src] [out]) s` by
    (irule ptr_inst_ok_slot_load >> simp[]) >>
  `step_inst_base (mk_inst id load [src] [out]) s = OK u` by
    (gvs[] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
                   slot_copy_word_def]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var root; Var out] []) w =
     OK (mstore (w2n addr) (slot_copy_word load s key) w)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  gvs[] >> simp[inst_seq_ptr_def]
QED

Theorem copy_singleton_ghost:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand src s = SOME key /\
  root <> out /\ lookup_var root s = SOME addr /\
  u = update_var out (slot_copy_word load s key) s /\
  w = (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  H = step_prov PG G (mk_inst id load [src] [out]) u /\
  tm = step_taint (mk_inst id load [src] [out]) s u tn /\
  Gf = step_prov PG H (mk_inst (id+1) MSTORE [Var root; Var out] [])
    (mstore (w2n addr) (slot_copy_word load s key) w) /\
  tnf = step_taint (mk_inst (id+1) MSTORE [Var root; Var out] []) w
    (mstore (w2n addr) (slot_copy_word load s key) w) tm ==>
  tnf.t_mem =
    (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
    {w2n addr+k | k IN key_taint
      (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var root) w = SOME addr /\
   eval_operand (Var out) w = SOME (slot_copy_word load s key)` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
   tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by
    (gvs[] >> irule slot_load_ghost_frame >> simp[]) >>
  `op_taint tm (Var out) = key_taint
    (if load=SLOAD then tn.t_stor else tn.t_trans) key` by
    (qpat_x_assum `tm = _` SUBST1_TAC >>
     irule slot_load_output_taint >> simp[]) >>
  `tnf.t_mem = (tm.t_mem DIFF
     {j | w2n addr <= j /\ j < w2n addr+32}) UNION
     {w2n addr+k | k IN op_taint tm (Var out)}` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     irule mstore_transferred_taint >> simp[]) >>
  fs[] >>
  simp[mstore_transferred_taint, step_taint_nonmemory_frame, mk_inst_def,
       step_prov_other_output, step_taint_other_output] >>
  rpt strip_tac >>
  gvs[] >> simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

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
  qabbrev_tac `u = update_var out (slot_copy_word load s key) s` >>
  qabbrev_tac `w = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `H = step_prov PG G (mk_inst id load [src] [out]) u` >>
  qabbrev_tac `tm = step_taint (mk_inst id load [src] [out]) s u tn` >>
  qabbrev_tac `Gf = step_prov PG H
    (mk_inst (id+1) MSTORE [Var root; Var out] [])
    (mstore (w2n addr) (slot_copy_word load s key) w)` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst (id+1) MSTORE [Var root; Var out] []) w
    (mstore (w2n addr) (slot_copy_word load s key) w) tm` >>
  qexistsl [`Gf`, `tnf`, `mstore (w2n addr) (slot_copy_word load s key) u`] >>
  conj_tac >- (simp[Abbr `u`] >>
    irule copy_singleton_execution >> simp[]) >>
  conj_tac
  >- (simp[Abbr `Gf`, Abbr `tnf`] >>
      irule copy_singleton_checks >>
      simp[Abbr `u`, Abbr `w`, Abbr `H`, Abbr `tm`]) >>
  `tnf.t_mem =
    (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
    {w2n addr+k | k IN key_taint
      (if load=SLOAD then tn.t_stor else tn.t_trans) key} /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p))` by
    (rule_assum_tac (REWRITE_RULE[markerTheory.Abbrev_def]) >>
     drule_all copy_singleton_ghost >> simp[]) >>
  fs[allocas_from_def, allocas_below_fmp_def] >>
  simp[Abbr `u`, allocas_from_def, allocas_below_fmp_def,
       mstore_def, update_var_def] >>
  rpt strip_tac >>
  fs[ptr_covers_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
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
  drule_all copy_singleton_segment >>
  disch_then (qspecl_then [`id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     [mk_inst id load [src] [out];
      mk_inst (id+1) MSTORE [Var root;Var out] []]` by
    (gvs[] >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >>
  gvs[] >> simp[mk_inst_def]
QED

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

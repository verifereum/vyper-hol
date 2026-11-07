Theory bodyPtrIfExpStorageCountedLoop
Ancestors
  bodyPtrIfExpStorageBodyInvariant bodyPtrIfExpStorageInvariant
  bodyPtrIfExpStorageControl slotCopyExecution copyExecution
  bodyPtrDefs compileEnv venomState ptrDiscipline finite_map words
  valueEncoding vyperValue fragGasPathPtr emitHelper venomInst

Theorem ifexp_copy_ptr_loop:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  fn_has_code cs (slot_copy_final cs src (Var out) n load) fn /\
  slot_copy_external cs src /\ slot_copy_external cs (Var out) /\
  eval_operand src sBase = SOME p /\ eval_operand (Var out) sBase = SOME d /\
  sa.cs_next_var <= cs.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n d \/ w2n d+32*n <= off) /\
  (!name pos len. local_region ce es.scopes s0 name pos len ==>
    pos+len <= w2n d \/ w2n d+32*n <= pos) /\
  (!name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\ lookup_var v sBase = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n d \/ w2n d+32*n <= w2n w)) /\
  (!j k. j<n /\ k IN (if load=SLOAD then key_taint tnBase.t_stor (p+n2w j)
    else key_taint tnBase.t_trans (p+n2w j)) ==> (j,k) IN X) ==>
  !i s G tn.
    ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
      cs load src (Var out) sBase GBase tnBase p d n X i s G tn /\
    s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?t G' tn'.
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
      ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
        cs load src (Var out) sBase GBase tnBase p d n X n t G' tn' /\
      t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >> measureInduct_on `n-i` >> rpt strip_tac >>
  `i <= n` by fs[ifexp_copy_ptr_inv_def, slot_copy_inv_def] >>
  drule_all ifexp_copy_reserved_external >> strip_tac >>
  drule_all ifexp_copy_ptr_condition >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  Cases_on `i=n`
  >- (qexistsl_tac [`slot_copy_cond_result cs n i s`, `G'`, `tn'`] >>
      simp[] >> gvs[] >> simp[slot_copy_cond_result_def, jump_to_def]) >>
  `i<n` by decide_tac >>
  qmatch_asmsub_abbrev_tac `OK cstate` >>
  `cstate.vs_current_bb = slot_copy_body cs /\ cstate.vs_inst_idx = 0 /\
   ~cstate.vs_halted` by
    simp[Abbr `cstate`, slot_copy_cond_result_def, jump_to_def] >>
  drule_all ifexp_copy_body_fetch >> strip_tac >>
  drule_all ifexp_copy_ptr_body >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK bstate` >>
  `bstate.vs_current_bb = slot_copy_cond cs /\ bstate.vs_inst_idx = 0 /\
   ~bstate.vs_halted` by
    simp[Abbr `bstate`, slot_copy_body_result_def, jump_to_def] >>
  `n-(i+1) < n-i` by decide_tac >>
  qpat_x_assum `!y. _` (qspec_then `i+1` mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qexistsl_tac [`t`, `G'''`, `tn'''`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_ptr_execution:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  fn_has_code cs (slot_copy_final cs src (Var out) n load) fn /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ~s.vs_halted /\ n < 2**256 /\ w2n d+32*n < 2**256 /\
  slot_copy_external cs src /\ slot_copy_external cs (Var out) /\
  eval_operand src s = SOME p /\ eval_operand (Var out) s = SOME d /\
  op_taint tn src = {} /\ ptr_covers G tn out s (32*n) /\
  sa.cs_next_var <= cs.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n d \/ w2n d+32*n <= off) /\
  (!name pos len. local_region ce es.scopes s0 name pos len ==>
    pos+len <= w2n d \/ w2n d+32*n <= pos) /\
  (!name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\ lookup_var v s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n d \/ w2n d+32*n <= w2n w)) /\
  (!j k. j<n /\ k IN (if load=SLOAD then key_taint tn.t_stor (p+n2w j)
    else key_taint tn.t_trans (p+n2w j)) ==> (j,k) IN X) /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
      cs load src (Var out) s G tn p d n X n t G' tn' /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >> drule_all ifexp_copy_reserved_external >> strip_tac >>
  `!v. Var out = Var v ==> ptr_covers G tn v s (32*n)` by simp[] >>
  drule_all ifexp_copy_ptr_initial >>
  disch_then (qspecl_then [`p`, `X`, `PG`, `D`] strip_assume_tac) >>
  ` (slot_copy_initial cs s).vs_current_bb = slot_copy_cond cs /\
    (slot_copy_initial cs s).vs_inst_idx = 0 /\ ~(slot_copy_initial cs s).vs_halted` by
    simp[slot_copy_initial_def, update_var_def, jump_to_def] >>
  drule_all ifexp_copy_ptr_loop >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G''`, `tn''`] >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

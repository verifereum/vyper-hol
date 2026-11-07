Theory bodyPtrIfExpStorageInvariant
Ancestors
  bodyPtrIfExpStorageFrame bodyPtrIfExpStorageInit bodyPtrIfExpStorageControl
  slotCopyExecution copyExecution createSourceCallback bodyPtrDefs appendStorageGhostPtr
  ptrDiscipline compileEnv venomState finite_map pred_set words

(* Packages the recurrent pointer induction hypothesis alongside the existing
   runtime invariant; this is not a replacement copy semantics. Original-frame
   and copy-start states remain distinct throughout the loop. *)
Definition ifexp_copy_ptr_inv_def:
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
    cs load src dst sBase GBase tnBase p d n X i s G tn <=>
  slot_copy_inv cs load sBase p d n [] i s /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  (!out. dst = Var out ==> ptr_covers G tn out s (32*n)) /\
  op_taint tn src = {} /\
  (!x. slot_copy_external cs (Var x) ==>
    FLOOKUP G x = FLOOKUP GBase x /\
    op_taint tn (Var x) = op_taint tnBase (Var x)) /\
  tn.t_stor = tnBase.t_stor /\ tn.t_trans = tnBase.t_trans /\
  tn.t_imm = tnBase.t_imm /\
  ghost_inv rty ce cx ee G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!j k. j < i /\ k < 32 /\ w2n d + 32*j + k IN tn.t_mem ==> (j,k) IN X)
End

(* A scratch-only step leaves every pointer field at the interface level.
   Runtime correctness is supplied independently by slotCopyExecution. *)
Theorem ifexp_copy_ptr_no_write:
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
    cs load src dst sBase GBase tnBase p d n X i s G tn /\
  slot_copy_inv cs load sBase p d n [] i t /\
  op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
  op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  sa.cs_next_var <= cs.cs_next_var /\
  (!x. not_fresh_at cs x ==> slot_copy_external cs (Var x)) /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!x. slot_copy_external cs (Var x) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
    cs load src dst sBase GBase tnBase p d n X i t G' tn'
Proof
  strip_tac >> fs[ifexp_copy_ptr_inv_def] >>
  `ghost_inv rty ce cx ee G' tn' t` by
    (irule ifexp_copy_ghost_inv_transport >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_kept ce es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_suffix_compose >> qexistsl_tac [`G`, `cs`, `tn`] >>
     simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  Cases_on `src` >> gvs[op_taint_def] >> metis_tac[]
QED

Theorem ifexp_copy_not_fresh_external:
  not_fresh_at cs x ==> slot_copy_external cs (Var x)
Proof
  simp[not_fresh_at_def, slot_copy_external_def, slot_copy_var_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `cs.cs_next_var+k` mp_tac) >> simp[]
QED

Theorem ifexp_copy_ptr_condition:
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
    cs load src dst sBase GBase tnBase p d n X i s G tn /\
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  sa.cs_next_var <= cs.cs_next_var /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK (slot_copy_cond_result cs n i s)) /\
    ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
      cs load src dst sBase GBase tnBase p d n X i
      (slot_copy_cond_result cs n i s) G' tn'
Proof
  strip_tac >>
  `i < 2**256 /\ n < 2**256 /\
   lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
   op_prov G (Var (slot_copy_var cs 0)) = NONE /\
   op_taint tn (Var (slot_copy_var cs 0)) = {}` by
    (fs[ifexp_copy_ptr_inv_def, slot_copy_inv_def] >> decide_tac) >>
  drule_all ifexp_copy_condition_transition >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  irule ifexp_copy_ptr_no_write >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  simp[ifexp_copy_not_fresh_external] >> conj_tac
  >- (irule slot_copy_condition_invariant >> fs[ifexp_copy_ptr_inv_def]) >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `x <> slot_copy_var cs 1` by
        (fs[slot_copy_external_def] >> metis_tac[DECIDE ``1 < 7``]) >>
      metis_tac[]) >>
  simp[slot_copy_cond_result_def, update_var_def, jump_to_def]
QED

Theorem ifexp_copy_ptr_initial:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  n < 2**256 /\ w2n d + 32*n < 2**256 /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  op_taint tn src = {} /\
  (!out. dst = Var out ==> ptr_covers G tn out s (32*n)) /\
  sa.cs_next_var <= cs.cs_next_var /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK (slot_copy_initial cs s)) /\
    ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee
      cs load src dst s G tn p d n X 0 (slot_copy_initial cs s) G' tn'
Proof
  strip_tac >> drule_all ifexp_copy_initial_transition >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `!x. slot_copy_external cs (Var x) ==>
    lookup_var x (slot_copy_initial cs s) = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> slot_copy_var cs 0` by
       (fs[slot_copy_external_def] >> metis_tac[DECIDE ``0 < 7``]) >> metis_tac[]) >>
  `ghost_inv rty ce cx ee G' tn' (slot_copy_initial cs s)` by
    (irule ifexp_copy_ghost_inv_transport >> qexistsl_tac [`G`, `s`, `tn`] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     simp[slot_copy_initial_def, update_var_def, jump_to_def]) >>
  `ghost_kept ce es sa G0 tn0 s0 G' tn'` by
    (irule ghost_kept_suffix_compose >> qexistsl_tac [`G`, `cs`, `tn`] >>
     simp[] >> metis_tac[ifexp_copy_not_fresh_external]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[ifexp_copy_ptr_inv_def] >>
  conj_tac
  >- (irule slot_copy_initial_invariant >>
      simp[create_memory_snapshot_def]) >>
  conj_tac
  >- (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  Cases_on `src` >> gvs[op_taint_def] >> metis_tac[]
QED

Theorem ifexp_copy_reserved_external:
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= cs.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
    slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x)) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> slot_copy_external cs (Var x))
Proof
  rw[local_ptrs_reserved_def] >> irule ifexp_copy_not_fresh_external >>
  metis_tac[stmtFragPtrTheory.not_fresh_at_mono]
QED

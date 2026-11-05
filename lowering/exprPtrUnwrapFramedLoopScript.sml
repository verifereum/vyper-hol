Theory exprPtrUnwrapFramedLoop
Ancestors
  exprPtrUnwrapStorageLoop exprPtrUnwrapStorageEntry exprPtrUnwrapCopyFrames
  exprPtrUnwrapFrames slotCopyExecution fragGasPathPtr fragGasSeqPtr
  bodyPtrDefs ptrDiscipline finite_map exprPtrUnwrapLoopInvariant
  venomExecSemantics venomState

(* Companion runtime frame, separate from the frozen slot_copy_inv. Bundling
   these compositional projections keeps the counted induction readable. *)
Definition slot_copy_runtime_frame_def:
  slot_copy_runtime_frame cs d i r s <=>
    s.vs_allocas = r.vs_allocas /\ s.vs_alloca_next = r.vs_alloca_next /\
    s.vs_accounts = r.vs_accounts /\ s.vs_transient = r.vs_transient /\
    s.vs_call_ctx = r.vs_call_ctx /\
    (!op. slot_copy_external cs op ==> eval_operand op s = eval_operand op r) /\
    (!a. ~(w2n d <= a /\ a < w2n d+32*i) ==>
      mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 r.vs_memory)
End

Theorem slot_copy_runtime_frame_initial:
  slot_copy_runtime_frame cs d 0 s (slot_copy_initial cs s)
Proof
  simp[slot_copy_runtime_frame_def, copy_initial_runtime_frame,
       copy_initial_external_operand]
QED

Theorem slot_copy_runtime_frame_condition:
  slot_copy_runtime_frame cs d i r s ==>
  slot_copy_runtime_frame cs d i r (slot_copy_cond_result cs n i s)
Proof
  simp[slot_copy_runtime_frame_def, copy_condition_allocation_frame,
       slot_copy_cond_frame, slot_copy_cond_operand] >> metis_tac[]
QED

Theorem slot_copy_runtime_frame_body:
  slot_copy_runtime_frame cs d i r s /\ w2n d+32*n < 2**256 /\ i<n ==>
  slot_copy_runtime_frame cs d (i+1) r (slot_copy_body_result cs p d load i s)
Proof
  simp[slot_copy_runtime_frame_def, copy_body_allocation_frame,
       slot_copy_body_sources, slot_copy_body_operand] >>
  rpt strip_tac >> irule copy_body_exterior_prefix >>
  (conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >>
  simp[] >> qexists_tac `n` >> simp[]
QED

Theorem copy_external_ptr_covers:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs (Var x) /\
  eval_operand (Var x) s = eval_operand (Var x) r ==>
  (ptr_covers G tn x s k <=> ptr_covers G0 tn0 x r k)
Proof
  strip_tac >> irule copy_ptr_covers_transport >>
  fs[slot_copy_ghost_inv_def, eval_operand_def]
QED

Theorem copy_counted_loop_framed:
  !i s G tn.
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks = SOME condbb /\
  condbb.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  slot_copy_runtime_frame cs d i r s ==>
  ?Gf tnf t.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    slot_copy_inv cs load original p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    slot_copy_runtime_frame cs d n r t
Proof
  measureInduct_on `n-i` >> rpt gen_tac >> strip_tac >> (
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME condbb` by simp[] >>
  Cases_on `i=n`
  >- (drule_all copy_condition_preserves_invariants >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl_tac [`G1`, `tn1`, `slot_copy_cond_result cs n n s`] >>
      gvs[slot_copy_cond_frame, slot_copy_runtime_frame_condition]) >>
  `i < n` by (fs[slot_copy_inv_def] >> decide_tac) >>
  mp_tac (Q.INST [`cond` |-> `condbb`] (SPEC_ALL copy_counted_iteration)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `op_taint tnf src = {}` by metis_tac[copy_ghost_external_taint] >>
  `slot_copy_runtime_frame cs d (i+1) r u` by
    (simp[Abbr `u`] >> irule slot_copy_runtime_frame_body >>
     (reverse conj_tac >- simp[slot_copy_runtime_frame_condition]) >>
     qexists_tac `n` >> fs[slot_copy_inv_def]) >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`u`, `Gf`, `tnf`] mp_tac) >>
  (impl_tac >- (gvs[slot_copy_body_counter, Abbr `u`])) >> strip_tac >>
  qexistsl_tac [`Gf'`, `tnf'`, `t`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`Gf`, `u`, `tnf`] >> gvs[])
QED

Theorem slot_copy_runtime_frame_projections:
  slot_copy_runtime_frame cs d i r s ==>
  s.vs_allocas = r.vs_allocas /\ s.vs_alloca_next = r.vs_alloca_next /\
  s.vs_accounts = r.vs_accounts /\ s.vs_transient = r.vs_transient /\
  s.vs_call_ctx = r.vs_call_ctx /\
  (!op. slot_copy_external cs op ==> eval_operand op s = eval_operand op r) /\
  (!a. ~(w2n d <= a /\ a < w2n d+32*i) ==>
    mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 r.vs_memory)
Proof
  rewrite_tac[slot_copy_runtime_frame_def]
QED

Theorem copy_external_ptr_covers_between:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 j H tm t /\
  slot_copy_external cs (Var x) /\
  eval_operand (Var x) t = eval_operand (Var x) s ==>
  (ptr_covers H tm x t k <=> ptr_covers G tn x s k)
Proof
  strip_tac >> irule copy_ptr_covers_transport >>
  fs[slot_copy_ghost_inv_def, eval_operand_def]
QED

Theorem copy_counted_loop_old_pointers:
  !i s G tn.
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks = SOME condbb /\
  condbb.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  slot_copy_runtime_frame cs d i r s ==>
  ?Gf tnf t.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    slot_copy_inv cs load original p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    slot_copy_runtime_frame cs d n r t /\
    (!x k. slot_copy_external cs (Var x) ==>
      (ptr_covers Gf tnf x t k <=> ptr_covers G tn x s k))
Proof
  rpt gen_tac >> strip_tac >> mp_tac (SPEC_ALL copy_counted_loop_framed) >>
  (impl_tac >- simp[]) >> strip_tac >> qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[] >>
  rpt strip_tac >>
  `eval_operand (Var x) t = eval_operand (Var x) s` by
    (fs[slot_copy_inv_def] >> metis_tac[]) >>
  metis_tac[copy_external_ptr_covers_between]
QED

Theorem copy_counted_entry_loop_framed:
  n < 2**256 /\ w2n d+32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src s = SOME p /\ lookup_var root s = SOME d /\
  op_taint tn0 src = {} /\ ptr_covers G0 tn0 root s (32*n) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks = SOME condbb /\
  condbb.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    gas_path_ptr D lo ctx fn PG G0 tn0 s 0 Gf tnf (OK t) /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    slot_copy_inv cs load s p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    slot_copy_runtime_frame cs d n s t /\
    (!x k. slot_copy_external cs (Var x) ==>
      (ptr_covers Gf tnf x t k <=> ptr_covers G0 tn0 x s k))
Proof
  strip_tac >>
  mp_tac (Q.INST [`G` |-> `G0`, `tn` |-> `tn0`]
    (SPEC_ALL (INST_TYPE [``:'a`` |-> ``:256``]
      copy_initial_counted_invariants))) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `slot_copy_runtime_frame cs d 0 s (slot_copy_initial cs s)` by
    simp[slot_copy_runtime_frame_initial] >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  `~(slot_copy_initial cs s).vs_halted` by
    metis_tac[gas_path_ptr_ok_not_halted] >>
  mp_tac (Q.INST [`G` |-> `G1`, `tn` |-> `tn1`,
    `original` |-> `s`, `s` |-> `slot_copy_initial cs s`, `i` |-> `0`,
    `r` |-> `s`] (SPEC_ALL copy_counted_loop_framed)) >>
  (impl_tac >- simp[slot_copy_initial_def, jump_to_def, update_var_def]) >>
  strip_tac >> qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[] >>
  (conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
        (SPEC_ALL gas_path_ptr_then))) >>
      qexistsl_tac [`G1`, `slot_copy_initial cs s`, `tn1`] >> simp[]) >>
  rpt strip_tac >>
  `eval_operand (Var x) t = eval_operand (Var x) s` by
    (fs[slot_copy_runtime_frame_def] >> metis_tac[]) >>
  metis_tac[copy_external_ptr_covers])
QED

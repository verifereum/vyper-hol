Theory exprPtrUnwrapFramedLoop
Ancestors
  exprPtrUnwrapLoopInvariant exprPtrUnwrapStorageEntry exprPtrUnwrapRuntimeFrame
  exprPtrUnwrapFrames slotCopyExecution fragGasPathPtr fragGasSeqPtr
  bodyPtrDefs ptrDiscipline finite_map venomExecSemantics venomState arithmetic

Theorem copy_counted_loop_framed:
  !i s G tn.
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
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
  measureInduct_on `n-i` >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME condbb` by simp[] >>
  Cases_on `i=n`
  >- (drule_all copy_condition_preserves_invariants >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl [`G1`, `tn1`, `slot_copy_cond_result cs n n s`] >>
      gvs[slot_copy_cond_frame, slot_copy_runtime_frame_condition]) >>
  `i < n` by (fs[slot_copy_inv_def] >> decide_tac) >>
  drule_all copy_counted_iteration >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `op_taint tnf src = {}` by metis_tac[copy_ghost_external_taint] >>
  `slot_copy_runtime_frame cs d (i+1) r u` by
    (simp[Abbr `u`] >> irule slot_copy_runtime_frame_body >>
     (reverse conj_tac >- simp[slot_copy_runtime_frame_condition]) >>
     qexists `n` >> fs[slot_copy_inv_def]) >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`u`, `Gf`, `tnf`] mp_tac) >>
  (impl_tac >- gvs[slot_copy_body_counter, Abbr `u`]) >> strip_tac >>
  qexistsl [`Gf'`, `tnf'`, `t`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl [`Gf`, `u`, `tnf`] >> gvs[]
QED

Theorem copy_external_ptr_covers_between:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 j H tm t /\
  slot_copy_external cs (Var x) /\ eval_operand (Var x) t = eval_operand (Var x) s ==>
  (ptr_covers H tm x t k <=> ptr_covers G tn x s k)
Proof
  strip_tac >> irule copy_ptr_covers_transport >>
  fs[slot_copy_ghost_inv_def, eval_operand_def]
QED

Theorem copy_counted_entry_loop_framed:
  (load=SLOAD \/ load=TLOAD) /\
  n < 2**256 /\ w2n d+32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
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
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``] copy_initial_counted_invariants) >>
  disch_then (qspecl_then [`p`, `load`, `PG`, `D`] strip_assume_tac) >>
  `slot_copy_runtime_frame cs d 0 s (slot_copy_initial cs s)` by
    simp[slot_copy_runtime_frame_initial] >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  `~(slot_copy_initial cs s).vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `(slot_copy_initial cs s).vs_current_bb = slot_copy_cond cs /\
   (slot_copy_initial cs s).vs_inst_idx = 0` by
    simp[slot_copy_initial_def, jump_to_def] >>
  drule_all copy_counted_loop_framed >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`, `t`] >> simp[] >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
      qexistsl [`G1`, `slot_copy_initial cs s`, `tn1`] >> simp[]) >>
  rpt strip_tac >>
  `eval_operand (Var x) t = eval_operand (Var x) s` by
    (fs[slot_copy_runtime_frame_def] >> metis_tac[]) >>
  drule_all copy_external_ptr_covers >> simp[]
QED

Theorem copy_counted_full_frame_projections:
  slot_copy_runtime_frame cs d i r s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s ==>
  copy_static s = copy_static r /\
  LENGTH r.vs_memory <= LENGTH s.vs_memory /\
  (!a k. a+k <= w2n d \/ w2n d+32*i <= a ==>
    mem_bytes_at a k s.vs_memory = mem_bytes_at a k r.vs_memory) /\
  tn.t_imm = tn0.t_imm
Proof
  strip_tac >> fs[slot_copy_runtime_frame_def, slot_copy_ghost_inv_def] >>
  rpt gen_tac >> first_x_assum MATCH_ACCEPT_TAC
QED

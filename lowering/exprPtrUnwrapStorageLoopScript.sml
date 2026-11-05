Theory exprPtrUnwrapStorageLoop
Ancestors
  exprPtrUnwrapLoopInvariant slotCopyExecution fragGasPathPtr fragGasSeqPtr
  ptrDiscipline bodyPtrDefs valueEncoding byte list rich_list

Theorem copy_counted_loop:
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
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    slot_copy_inv cs load original p d n regions n t /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)
Proof
  measureInduct_on `n-i` >> rpt gen_tac >> strip_tac >> (
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME condbb` by simp[] >>
  Cases_on `i=n`
  >- (drule_all copy_condition_preserves_invariants >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl_tac [`G1`, `tn1`, `slot_copy_cond_result cs n n s`] >>
      gvs[slot_copy_cond_frame]) >>
  `i < n` by (fs[slot_copy_inv_def] >> decide_tac) >>
  mp_tac (Q.INST [`cond` |-> `condbb`] (SPEC_ALL copy_counted_iteration)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `~u.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `op_taint tnf src = {}` by metis_tac[copy_ghost_external_taint] >>
  first_x_assum (qspec_then `i+1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`u`, `Gf`, `tnf`] mp_tac) >>
  (impl_tac >- (gvs[slot_copy_body_counter, Abbr `u`])) >> strip_tac >>
  qexistsl_tac [`Gf'`, `tnf'`, `t`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`Gf`, `u`, `tnf`] >> gvs[])
QED

Theorem copy_prefix_words:
  slot_copy_inv cs load original p d n regions i s ==>
  !j. j < i ==>
    mem_word_at (w2n d + 32*j) s.vs_memory =
      slot_copy_word load original (p+n2w j)
Proof
  simp[slot_copy_inv_def, slot_copy_prefix_def] >> strip_tac >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!j. j < i ==> _` drule >> strip_tac >>
  `32 <= LENGTH (DROP (32*j + w2n d) s.vs_memory)` by simp[] >>
  pure_rewrite_tac[mem_word_at_def] >>
  `w2n d+32*j = 32*j+w2n d` by decide_tac >>
  qpat_x_assum `w2n d+32*j = _` (fn th => pure_rewrite_tac[th]) >>
  `32 - LENGTH (DROP (32*j + w2n d) s.vs_memory) = 0` by decide_tac >>
  pure_asm_rewrite_tac[TAKE_APPEND, TAKE_0, APPEND_NIL] >>
  simp[word_of_bytes_word_to_bytes, dividesTheory.divides_def]
QED

Theorem copy_prefix_taint:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s ==>
  !j b. j < i /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    b IN key_taint (if load=SLOAD then tn0.t_stor else tn0.t_trans) (p+n2w j)
Proof
  simp[slot_copy_ghost_inv_def]
QED

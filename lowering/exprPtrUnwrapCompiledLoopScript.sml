(* Actual generated slot-copy loop, retaining allocation capacity separately. *)
Theory exprPtrUnwrapCompiledLoop
Ancestors
  exprPtrUnwrapFramedLoop exprPtrUnwrapCopyPost exprPtrUnwrapEnsureShape
  slotCopyExecution copyExecution exprPtrUnwrapRuntimeFrame
  exprPtrUnwrapLoopInvariant exprPtrUnwrapFrames exprLoweringProps
  bodyPtrDefs context compileEnv venomState venomInst ptrDiscipline
  createMemoryInterface list arithmetic

Theorem unwrap_compiled_slot_loop:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_slot_to_memory src (Var root) n loc cs = (lab,sb) /\
  fn_has_code cs sb fn /\ n < 2**256 /\ w2n d+32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src s = SOME p /\ lookup_var root s = SOME d /\
  op_taint tn0 src = {} /\ ptr_covers G0 tn0 root s (32*n) /\
  ptr_covers G0 tn0 root s nb /\
  s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    gas_path_ptr D lo ctx fn PG G0 tn0 s 0 Gf tnf (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_covers Gf tnf root t nb /\
    slot_copy_inv cs (if loc=LocStorage then SLOAD else TLOAD) s p d n regions n t /\
    slot_copy_ghost_inv cs (if loc=LocStorage then SLOAD else TLOAD)
      p d root n G0 tn0 n Gf tnf t /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    slot_copy_runtime_frame cs d n s t /\
    (!j. j < n ==> mem_word_at (w2n d+32*j) t.vs_memory =
      slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) s (p+n2w j)) /\
    (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tnf.t_mem ==>
      b IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans)
        (p+n2w j)) /\
    copy_static t = copy_static s /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+32*n <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    tnf.t_imm = tn0.t_imm /\
    (!x k. slot_copy_external cs (Var x) ==>
      (ptr_covers Gf tnf x t k <=> ptr_covers G0 tn0 x s k))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  qpat_assum `sb = slot_copy_final _ _ _ _ _` SUBST_ALL_TAC >>
  drule_all slot_copy_lookup >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := cs.cs_current_bb;
      bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>` by simp[] >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_body cs) _ = SOME body_block` >>
  qmatch_asmsub_abbrev_tac `lookup_block (slot_copy_cond cs) _ = SOME cond_block` >>
  qmatch_asmsub_abbrev_tac `lookup_block cs.cs_current_bb _ = SOME copy_entry_bb` >>
  `body_block.bb_instructions = slot_copy_body_insts cs src (Var root)
    (if loc=LocStorage then SLOAD else TLOAD)` by simp[Abbr `body_block`] >>
  `cond_block.bb_instructions = slot_copy_cond_insts cs n` by simp[Abbr `cond_block`] >>
  `copy_entry_bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs` by
    simp[Abbr `copy_entry_bb`] >>
  SUBGOAL_THEN
    ``(if loc=LocStorage then SLOAD else TLOAD) = SLOAD \/
      (if loc=LocStorage then SLOAD else TLOAD) = TLOAD`` assume_tac
  >- (Cases_on `loc=LocStorage` >> simp[]) >>
  drule_all (Q.INST
    [`load` |-> `if loc=LocStorage then SLOAD else TLOAD`]
    copy_counted_entry_loop_framed) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all copy_counted_full_frame_projections >> strip_tac >>
  drule copy_prefix_words >> strip_tac >>
  drule copy_prefix_taint >> strip_tac >>
  qexistsl [`Gf`, `tnf`, `t`] >> simp[] >>
  Cases_on `loc=LocStorage` >> gvs[] >> metis_tac[]
QED

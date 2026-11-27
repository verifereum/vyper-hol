(* Linked frame at the end of the three ECMul input stores. *)
Theory bodyECMulPayloadFrameMods
Ancestors
  bodyMemEcArithPayload bodyIfExpTypedImmFrameMods bodyIfExpTypedGhostMods
  exprLoweringProps emitHelper compileEnv loweringStateRelDefs typedMemoryCopy
  venomState venomInst ptrDiscipline words list

val _ = Parse.hide "cp";

Theorem ecmul_payload_frame_mods:
  (do xp <- emit_op ADD [Var root; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [Var src; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [Var root; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [Var src; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [Var src; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) ca = ((),cp) /\
  run_inst_seq (emitted_insts ca cp) s = OK r /\
  t = r with vs_inst_idx := LENGTH cp.cs_current_insts /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n wi,96) /\
  lookup_var root s = SOME wp /\ lookup_var src s = SOME wi /\
  eval_operand scalar s = SOME w /\
  not_fresh_at ca root /\ not_fresh_at ca src /\
  (!z. scalar = Var z ==> not_fresh_at ca z) /\
  w2n wp + 64 < dimword (:256) /\ w2n wi + 96 < dimword (:256) /\
  regions_disjoint (w2n wi) 96 (w2n wp) 64 /\
  stmt_state_rel H ctx func ce cx ee s /\ local_ptrs_rel func ce ee.scopes s /\
  local_ptrs_reserved ce ca /\
  sc.cs_next_var <= ca.cs_next_var /\ sc.cs_next_id <= ca.cs_next_id /\
  (!name b sz. local_region ce ee.scopes s name b sz ==>
    regions_disjoint (w2n wi) 96 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n wi) 96 b sz) /\
  (ce.ce_is_ctor ==> !name tv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wi) 96 off (type_memory_size tv)) /\
  immutable_frame_mods func ce cx ee s /\ ghost_inv_at_mods D lo d ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  typed_copy_state_frame ca (w2n wi) 96 s t /\ lo <= w2n wi /\
  (!z. not_fresh_at ca z ==>
    FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
  tn'.t_mem = tn.t_mem DIFF {i | w2n wi <= i /\ i < w2n wi+96} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
  ghost_inv_at_mods D lo d ce cx ee G' tn' t
Proof
  strip_tac >> conj_tac
  >- (`eval_operand (Var root) s = SOME wp /\ eval_operand (Var src) s = SOME wi` by
        simp[eval_operand_def] >>
      `!z. MEM (Var z) [Var root; Var src; scalar] ==> not_fresh_at ca z` by
        (simp[DISJ_IMP_THM, EQ_SYM_EQ] >> metis_tac[]) >>
      drule_all_then (qx_choose_then `u` strip_assume_tac) ecmul_input_stores_sim >>
      `u = r` by
        (qpat_assum `run_inst_seq _ s = OK u` mp_tac >>
         qpat_assum `run_inst_seq _ s = OK r` (fn th => simp[NoAsms,th])) >>
      qpat_x_assum `u = r` SUBST_ALL_TAC >> simp[stmt_state_rel_inst_idx]) >>
  conj_tac
  >- (irule ifexp_typed_immutable_frame_mods >>
      qexistsl [`w2n wi`,`inst`,`ca`,`96`,`s`] >> asm_rewrite_tac[]) >>
  irule ifexp_typed_copy_ghost_mods >>
  qexistsl [`G`,`w2n wi`,`func`,`ca`,`96`,`s`,`tn`] >> asm_rewrite_tac[] >>
  simp[pred_setTheory.IN_DIFF]
QED

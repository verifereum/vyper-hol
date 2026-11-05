(* Counted generated body prefix followed by the raw backedge, without PHIs. *)
Theory exprPtrUnwrapGeneratedPath
Ancestors
  exprPtrUnwrapGeneratedBody exprPtrUnwrapBackedge exprPtrUnwrapFrames
  copyExecution slotCopyExecution fragGasSeqPtr fragGasPathPtr fragExec
  bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst
  venomState list rich_list

Theorem copy_generated_backedge_path:
  (load = SLOAD \/ load = TLOAD) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  run_inst_seq (TAKE 7 bb.bb_instructions) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (TAKE 7 bb.bb_instructions) s Gf tnf /\
  t.vs_current_bb = s.vs_current_bb /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)))
Proof
  strip_tac >> (
  `gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := 7))` by
    (mp_tac (Q.INST [`code` |-> `TAKE 7 bb.bb_instructions`,
       `G'` |-> `Gf`, `tn'` |-> `tnf`] (SPEC_ALL run_inst_seq_gas_path_ptr)) >>
     simp[slot_copy_body_insts_def, mk_inst_def, is_terminator_def]) >>
  `~(t with vs_inst_idx := 7).vs_halted` by
    metis_tac[gas_path_ptr_ok_not_halted] >>
  `gas_path_ptr_edge D lo ctx fn PG Gf tnf (t with vs_inst_idx := 7) 0 Gf tnf
    (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)))` by
    (irule copy_jmp_counted_edge >> simp[] >>
     qexists_tac `cs.cs_next_id + 11` >>
     simp[slot_copy_body_insts_def, get_instruction_def]) >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL gas_path_ptr_then))) >>
  qexistsl_tac [`Gf`, `t with vs_inst_idx := 7`, `tnf`] >>
  simp[] >> irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
    (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
  qexistsl_tac [`Gf`, `jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)`, `tnf`] >>
  simp[] >> irule (cj 1 gas_path_ptr_rules) >>
  gvs[jump_to_def])
QED

(* The generated adapter's data frames survive the cursor update and raw JMP. *)
Theorem copy_generated_body_path:
  (load = SLOAD \/ load = TLOAD) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  eval_operand src s = SOME srcword /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
  root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5 /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off + 32 <= capacity /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 0) (k+1w)
      (update_var (slot_copy_var cs 6) (k+1w)
        (mstore (w2n (a+n2w off)) (slot_copy_word load s (srcword+k))
          (update_var (slot_copy_var cs 5) (a+n2w off)
            (update_var (slot_copy_var cs 4) (n2w off)
              (update_var (slot_copy_var cs 3) (slot_copy_word load s (srcword+k))
                (update_var (slot_copy_var cs 2) (srcword+k) s)))))) /\
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
      (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7))) /\
    op_taint tnf (Var (slot_copy_var cs 0)) = {} /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n (a+n2w off) <= j /\ j < w2n (a+n2w off) + 32}) UNION
      {w2n (a+n2w off) + j | j IN
        key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) (srcword+k)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    allocas_from lo (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)) /\
    (ctx_has_dalloca ctx ==>
      allocas_below_fmp (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7))) /\
    (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
         p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
         p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
      p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
      p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 /\
      ptr_covers G tn p s c ==>
      ptr_covers Gf tnf p (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)) c)
Proof
  strip_tac >> (
  mp_tac (SPEC_ALL copy_generated_body_segment) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >>
  `t.vs_current_bb = s.vs_current_bb` by
    simp[update_var_def, mstore_def] >>
  conj_tac >- simp[] >>
  conj_tac >- (irule copy_generated_backedge_path >> metis_tac[]) >>
  qpat_x_assum `t = _` kall_tac >>
  fs[jump_to_def, allocas_from_def, allocas_below_fmp_def,
     ptr_covers_def, lookup_var_def] >> metis_tac[])
QED

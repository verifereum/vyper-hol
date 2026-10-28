(* Link straight-line power certificates to the actual Venom block runner.
   No admitted expression simulation is used. *)
Theory powerBlockProps
Ancestors
  powerRunProps fragExec emitHelperProps exprLoweringProps
  compileEnv emitHelper exprLowering venomExecSemantics venomExecProofs
  venomInst venomInstProofs venomState instIdxIndep list rich_list

Theorem power_run_block_ok:
  run_inst_seq insts ss = OK ss' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> PHI) insts /\
  bb.bb_instructions = insts ++ [mk_inst id JMP [Label target] []] /\
  ~ss'.vs_halted ==>
  run_block fuel ctx bb ss = OK (jump_to target ss')
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (rw[EVERY_MEM] >> fs[EVERY_MEM]) >>
  simp[run_block_no_phis_eq_exec_block] >>
  irule exec_block_inst_seq_jmp >> simp[] >>
  qexistsl_tac [`insts`, `id`] >>
  simp[get_instruction_def, EL_APPEND_EQN, EVERY_MEM] >>
  fs[EVERY_MEM]
QED

Theorem power_run_block_abort:
  run_inst_seq insts ss = Abort a ss' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> PHI) insts /\
  bb.bb_instructions = insts ++ [mk_inst id JMP [Label target] []] ==>
  ?n. run_block fuel ctx bb ss = Abort a (ss' with vs_inst_idx := n)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (rw[EVERY_MEM] >> fs[EVERY_MEM]) >>
  simp[run_block_no_phis_eq_exec_block] >>
  mp_tac (Q.SPECL [`insts`, `ss with vs_inst_idx := 0`, `fuel`, `ctx`, `bb`]
    exec_block_run_inst_seq) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, EVERY_MEM] >>
  impl_tac >- (fs[EVERY_MEM] >> simp[]) >>
  strip_tac >> metis_tac[]
QED

Theorem power_sequence_preserves_halted:
  run_inst_seq insts ss = OK ss' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts ==>
  ss'.vs_halted = ss.vs_halted
Proof
  strip_tac >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_halted` run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

Theorem power_block_result:
  run_inst_seq insts ss = OK sout /\ eval_operand op sout = SOME value /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> PHI) insts /\
  bb.bb_instructions = insts ++ [mk_inst id JMP [Label target] []] /\
  ~ss.vs_halted ==>
  ?ss'. run_block fuel ctx bb ss = OK ss' /\ eval_operand op ss' = SOME value
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts`
    by fs[EVERY_MEM] >>
  drule_all power_sequence_preserves_halted >> strip_tac >>
  `~sout.vs_halted` by gvs[] >>
  drule_all power_run_block_ok >> strip_tac >>
  qexists_tac `jump_to target sout` >> simp[] >> Cases_on `op` >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def]
QED

(* The exact four opcodes emitted by the upper-bound branch. This also
   certifies absence of PHI/INVOKE/terminators needed by the real runner. *)
Theorem power_upper_checked_instructions:
  (do above <- emit_op GT [checked; Lit bound];
      ok <- emit_op ISZERO [above];
      emit_void ASSERT [ok];
      emit_op Exp [x; y] od) st = (op, st') ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> PHI) (emitted_insts st st')
Proof
  simp[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def,
       emitted_insts_def, is_terminator_def] >>
  strip_tac >> gvs[] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[is_terminator_def]
QED

(* This is a block containing the compiler's actual emitted instructions,
   not a separate mathematical EXP evaluator. The final JMP is a caller's
   continuation; it is never reached on the rejected path. *)
Theorem power_upper_checked_block:
  (do above <- emit_op GT [checked; Lit bound];
      ok <- emit_op ISZERO [above];
      emit_void ASSERT [ok];
      emit_op Exp [x; y] od) st = (op, st') /\
  st.cs_current_insts = [] /\
  bb.bb_instructions = st'.cs_current_insts ++ [mk_inst id JMP [Label target] []] /\
  eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
  eval_operand checked ss = SOME c /\ fresh_vars_wrt st ss /\ ~ss.vs_halted ==>
  (w2n c <= w2n bound ==>
   ?ss'. run_block fuel ctx bb ss = OK ss' /\
         eval_operand op ss' = SOME (word_exp a b)) /\
  (w2n bound < w2n c ==>
   ?ss'. run_block fuel ctx bb ss = Abort Revert_abort ss')
Proof
  strip_tac >> drule power_upper_checked_instructions >> strip_tac >>
  drule_all power_upper_checked_run >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  conj_tac >> strip_tac
  >- (first_x_assum drule >>
      disch_then (qx_choose_then `sout` strip_assume_tac) >>
      drule_all power_sequence_preserves_halted >> strip_tac >>
      `~sout.vs_halted` by gvs[] >>
      `bb.bb_instructions = emitted_insts st st' ++ [mk_inst id JMP [Label target] []]`
        by gvs[] >>
      drule_all power_run_block_ok >> strip_tac >>
      qexists_tac `jump_to target sout` >>
      simp[] >> Cases_on `op` >>
      gvs[jump_to_def, eval_operand_def, lookup_var_def]) >>
  first_x_assum drule >>
  disch_then (qx_choose_then `sout` strip_assume_tac) >>
  `bb.bb_instructions = emitted_insts st st' ++ [mk_inst id JMP [Label target] []]`
    by gvs[] >>
  drule_all power_run_block_abort >> metis_tac[]
QED

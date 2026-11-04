(*
 * LowerDload against the O1 pass contract: the output's taint reaches only
 * the dead bytes D.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_taint
 *)
Theory o1ContractLowerDloadTaint
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list

(* A complete untainted overwrite clears a word, even if the step also
   introduces fresh-site taint. *)
Theorem mem_word_taint_overwrite:
  written_taint tn inst s = {} /\
  (!k. k < 32 ==> off + k IN range_bytes (step_writes inst s s')) ==>
  mem_word_taint (mem_taint tn inst s s') off = {}
Proof
  rw[mem_word_taint_def, mem_taint_def, pred_setTheory.EXTENSION] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem codecopy_word_taint:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; len] /\
  eval_operand dst s = SOME dstw /\ eval_operand src s = SOME source /\
  eval_operand len s = SOME 32w ==>
  mem_word_taint (mem_taint tn inst s s') (w2n dstw) = {}
Proof
  strip_tac >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  irule mem_word_taint_overwrite >>
  simp[written_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def,
       range_bytes_def, wordsTheory.dimword_def] >> rpt strip_tac >> simp[]
QED

Theorem mload_out_taint:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [addr] /\
  eval_operand addr s = SOME w ==>
  out_taint tn inst s = mem_word_taint tn.t_mem (w2n w)
Proof
  simp[out_taint_def]
QED

Theorem step_taint_nonmemory:
  inst.inst_opcode <> SSTORE /\ inst.inst_opcode <> TSTORE /\
  inst.inst_opcode <> ISTORE /\ inst.inst_opcode <> CALL /\
  inst.inst_opcode <> STATICCALL ==>
  (step_taint inst s s' tn).t_stor = tn.t_stor /\
  (step_taint inst s s' tn).t_trans = tn.t_trans /\
  (step_taint inst s s' tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED

(* The output's taint reaches only the dead bytes D. *)
Theorem lower_dload_stage_taint:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    taint_within D C' vs
Proof
  cheat
QED

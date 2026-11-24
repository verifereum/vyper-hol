Theory entryCreateSubscriptCode
Ancestors
  entryCreateFocusSpec entryCreateAdminSequence bodyFullSubscriptArrayCodeOps
  context exprLoweringProps emitHelperProps fragExec abiEncoderProps
  venomExecSemantics venomInst

(* The runtime code length load has a real caller step, even with no GAS. *)
Theorem runtime_code_length_load_scope:
  compile_imm_load_word F imm arg sa = (op,sb) /\ fn_has_code sa sb func /\
  create_operand_at sa s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  t = (u with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  create_operand_full_scope sa sb E ctx func s [] (OK t)
Proof
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> irule create_admin_sequence_scope >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  fs[same_blocks_def, frag_ids_def, mk_inst_def, is_terminator_def]
QED

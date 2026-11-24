(* Scope and cut of the two straight-line stages of a widened IfExp arm. *)
Theory entryCreateIfExpWidenSeq
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  abiBufferAllocationCode bytesCopyCode bodyPtrIfExpBytesCounted
  compilerInstructionSuffix emitHelperProps abiEncoderProps exprLoweringProps
  fragExec venomExecSemantics venomInst venomState list arithmetic

(* Keep the allocation's base-step endpoint, then advance the actual PC. *)
Theorem ifexp_alloc_selected_site:
  compile_alloc_buffer n sa = (buf,sb) /\
  fn_has_code sa sb f /\ create_operand_at sa s ==>
  create_operand_cut sa sb E C f tops cx st0 source (es,s) /\
  (!out u. ~s.vs_halted /\ buf.buf_operand = Var out /\
     step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
     create_operand_full_scope sa sb E C f s []
       (OK (u with vs_inst_idx := SUC s.vs_inst_idx)))
Proof
  strip_tac >> drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >>
  strip_tac >> conj_tac
  >- (irule create_admin_sequence_cut >> simp[mk_inst_def, is_terminator_def]) >>
  rpt strip_tac >> gvs[] >>
  `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by fs[create_operand_at_def] >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by simp[run_inst_seq_def] >>
  qpat_assum `SUC s.vs_inst_idx = _` SUBST1_TAC >>
  irule create_admin_sequence_scope >> simp[mk_inst_def, is_terminator_def, frag_ids_def]
QED

(* The run equation names the same sf as the copy's pointer and memory
   posts. Its confined endpoint is reindexed, not freshly chosen. *)
Theorem ifexp_bytes_store_selected_site:
  compile_store_bytestring src dst sa = ((),sb) /\ fn_has_code sa sb f /\
  create_operand_at sa s ==>
  create_operand_cut sa sb E C f tops cx st0 source (es,s) /\
  (!sf. ~s.vs_halted /\ run_inst_seq (emitted_insts sa sb) s = OK sf ==>
     create_operand_full_scope sa sb E C f s []
       (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))))
Proof
  strip_tac >> drule bytesCopyCodeTheory.compile_store_bytestring_code >>
  strip_tac >>
  `sb.cs_next_id = sa.cs_next_id + 6` by
    (drule compile_store_bytestring_stages >> strip_tac >>
     imp_res_tac added_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     fs[]) >>
  `EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
              i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sa sb)` by
    simp[bytes_copy_insts_def, mk_inst_def, is_terminator_def, frag_ids_def] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    fs[create_operand_at_def] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  conj_tac
  >- (irule create_admin_sequence_cut >> fs[EVERY_MEM]) >>
  rpt strip_tac >> qpat_assum `s.vs_inst_idx + LENGTH _ = _` SUBST1_TAC >>
  irule create_admin_sequence_scope >> fs[EVERY_MEM]
QED

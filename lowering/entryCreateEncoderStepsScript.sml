(* Geometry of the concrete steps used by the ABI encoder window proofs. *)
Theory entryCreateEncoderSteps
Ancestors
  abiEncoderWindowSequence entryCreateAdminSequence entryCreatePathScope
  entryCreateFocusSpec entryCreateCompletedCut createSizePrefixReplay createMarkedPath
  emitHelperProps fragExec fragGasOrigin venomExecSemantics venomState
  venomInst list relation

(* Use the very same normalized raw result as window_seq_phase.  The
   enclosing exit need not coincide with the end of this sequence. *)
Theorem encoder_window_seq_prefix:
  window_seq st en s raw /\ fn_has_code st en func /\
  ~s.vs_halted /\ create_operand_at st s /\
  EVERY (\i. i.inst_id IN frag_ids st en /\ i.inst_opcode <> GAS)
    (emitted_insts st en) /\
  a.cs_next_id <= st.cs_next_id /\ en.cs_next_id <= b.cs_next_id /\
  (!bb i. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids st en) ==>
  create_expr_prefix a b explicit ctx func s []
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >>
  `create_operand_full_scope st en explicit ctx func s []
    (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts))` by
    (irule create_admin_sequence_scope >>
     fs[window_seq_def, inst_extends_def, EVERY_MEM]) >>
  fs[create_operand_full_scope_def] >>
  irule create_expr_prefix_lift >> metis_tac[]
QED

(* A loop branch need not advance to the next slot in its source block.
   Its concrete successor, including any entry actions, comes from the edge. *)
Theorem encoder_window_branch_prefix:
  ~create_operand_at b s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
  gas_origin_edge F explicit ctx func s [] (OK t) ==>
  create_expr_prefix a b explicit ctx func s [] t
Proof
  strip_tac >> simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def, create_prefix_step_def] >>
  fs[create_operand_at_def] >> metis_tac[]
QED

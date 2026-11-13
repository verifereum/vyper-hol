(* Whole lowered-buffer coverage at the assignment read boundary. *)
Theory assignBasePtrBoundary
Ancestors bodyPtrDefs representationCleanPtr fragExecPtr fragGasSeqPtr
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun

Theorem ptr_buf_ok_read_covers:
  !cenv e op G tn s w n.
    ptr_buf_ok cenv e op G s /\ op_taint tn op = {} /\
    eval_operand op s = SOME w /\
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    n <= type_memory_bytes cenv (lowered_value_type cenv e) ==>
    ?p. op = Var p /\ ptr_covers G tn p s n
Proof
  rpt strip_tac >>
  gvs[ptr_buf_ok_def] >>
  simp[ptr_covers_def] >> qexists_tac `w` >>
  gvs[eval_operand_def] >> decide_tac
QED

(* A local word store needs no fixed-run lifting: its actual edge is counted. *)
Theorem assign_word_store_edge_ptr:
  !D ctx fn PG G tn s bb id p v u.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var p; v] []) /\
    ptr_covers G tn p s 32 /\ op_taint tn v = {} /\
    step_inst_base (mk_inst id MSTORE [Var p; v] []) s = OK u ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MSTORE [Var p; v] []) u)
      (step_taint (mk_inst id MSTORE [Var p; v] []) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  drule_all ptr_inst_ok_mstore >>
  disch_then (qspecl_then [`D`, `fn`, `id`, `0`] assume_tac) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def]
QED

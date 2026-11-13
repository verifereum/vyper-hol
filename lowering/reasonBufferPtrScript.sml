(* Counted allocation boundaries for reason-encoder buffers. *)
Theory reasonBufferPtr
Ancestors
  reasonResourcesPtr allocationPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  ptrSafeRun ptrDiscipline venomInst venomInstProofs venomState
  bodyPtrDefs stmtSimDefs arithmetic venomExecSemantics

Theorem reason_buffer_alloca_path:
  !D ctx func PG G tn s id n out s1 bb cenv cx es.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    gas_path_ptr D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
      (OK (s1 with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
      out s1 n
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`gas_path_ptr_edge D 0 ctx func PG G tn s
         (if (mk_inst id ALLOCA [Lit (n2w n)] [out]).inst_opcode = GAS then 1 else 0)
         (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
         (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
         (OK (s1 with vs_inst_idx := SUC s.vs_inst_idx))` by
        (irule straight_line_ptr_edge >>
         simp[ptr_inst_ok_alloca, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
      `step_inst 0 ctx (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1` by
        simp[step_inst_non_invoke, mk_inst_def] >>
      `~s1.vs_halted` by
        (drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
      drule (cj 2 gas_path_ptr_rules) >>
      simp[] >> disch_then irule >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  irule alloca_step_ptr_covers >> metis_tac[]
QED

(* A clean selector/offset store is a zero-count encoder edge. *)
Theorem reason_buffer_mstore_path:
  !D ctx func PG G tn s id dst value s1 bb.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; value] []) /\
    ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
    step_inst_base (mk_inst id MSTORE [Var dst; value] []) s = OK s1 ==>
    gas_path_ptr D 0 ctx func PG G tn s 0
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) s1)
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s s1 tn)
      (OK (s1 with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt gen_tac >> strip_tac >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s
     (if (mk_inst id MSTORE [Var dst; value] []).inst_opcode = GAS then 1 else 0)
     (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) s1)
     (step_taint (mk_inst id MSTORE [Var dst; value] []) s s1 tn)
     (OK (s1 with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule straight_line_ptr_edge >>
     simp[mk_inst_def, is_terminator_def] >>
     metis_tac[SRULE [mk_inst_def] ptr_inst_ok_mstore]) >>
  `step_inst 0 ctx (mk_inst id MSTORE [Var dst; value] []) s = OK s1` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~s1.vs_halted` by
    (drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
  drule (cj 2 gas_path_ptr_rules) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

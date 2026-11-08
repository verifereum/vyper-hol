(* Taint-transparent scratch writes. Unlike clean header stores, the data
   operand may carry pointer taint; only the covered address must be clean. *)
Theory bodyPtrSubscriptScratchStore
Ancestors
  bodyPtrDefs contextCodegenRel codegenRel memLocDefs
  typedCopyPtr fragExec fragExecPtr fragGasSeqPtr fragGasPathPtr
  ptrDiscipline ptrSafeRun venomInstProofs venomExecSemantics venomState venomInst

Theorem ptr_inst_ok_mstore_taint_transparent:
  ptr_covers G tn dst s 32 /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst iid MSTORE [Var dst;value] []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand value s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

(* This generalizes the clean-data edge in the read-only
   bodyPtrSubscriptStore theory, without assuming the data is clean. *)
Theorem mstore_counted_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid MSTORE [Var dst;value] []) /\
  ptr_covers G tn dst s 32 /\ op_taint tn (Var dst) = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst iid MSTORE [Var dst;value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst iid MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst iid MSTORE [Var dst;value] []) s`
    by (irule ptr_inst_ok_mstore_taint_transparent >> simp[]) >>
  `step_inst_base (mk_inst iid MSTORE [Var dst;value] []) s =
    OK (mstore (w2n a) w s)`
    by (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `(mk_inst iid MSTORE [Var dst;value] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst iid MSTORE [Var dst;value] []).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> strip_tac >>
  `~(mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted`
    by simp[mstore_def] >>
  metis_tac[cj 1 gas_path_ptr_rules, cj 2 gas_path_ptr_rules,
            arithmeticTheory.ADD_CLAUSES]
QED

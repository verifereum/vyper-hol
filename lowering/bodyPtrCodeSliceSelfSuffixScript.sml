(* Runtime copy/store boundary, independent of operand evaluation and
   allocation implementation.  The code source is not a memory read. *)
Theory bodyPtrCodeSliceSelfSuffix
Ancestors
  bodyPtrCodeSliceSelfCopy fragExecPtr fragGasSeqPtr typedCopyPtr
  exprSimPtrTopLevelImmutableCopy bodyPtrHashBuiltinsGhostFrame
  lowerDloadPtrExpansionTransport emitHelperProps bodyPtrDefs
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  codegenRel words list finite_map pred_set

Theorem self_code_copy_store_checked:
  !D ctx fn PG G tn s t id sid dst out src len a n p b.
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
    eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
    lookup_var out s = SOME p /\ lookup_var dst s = SOME b /\
    op_taint tn src = {} /\ op_taint tn len = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id CODECOPY [Var dst;src;len] []) s = OK t ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id CODECOPY [Var dst;src;len] [];
       mk_inst sid MSTORE [Var out;len] []] s G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n b <= j /\ j < w2n b + w2n n}) DIFF
        {j | w2n p <= j /\ j < w2n p + 32})
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id CODECOPY [Var dst;src;len] []) s` by
    (irule ptr_inst_ok_codecopy >> simp[] >> metis_tac[]) >>
  `step_prov PG G (mk_inst id CODECOPY [Var dst;src;len] []) t = G /\
   step_taint (mk_inst id CODECOPY [Var dst;src;len] []) s t tn =
     tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}` by
    (drule_at (Pat `step_inst_base _ _ = _`) dload_codecopy_state_ghost >>
     simp[mk_inst_def, eval_operand_def] >> metis_tac[]) >>
  `t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels` by
    (drule_at (Pat `step_inst_base _ _ = _`) dload_codecopy_state_ghost >>
     simp[mk_inst_def, eval_operand_def, write_memory_with_expansion_def] >>
     metis_tac[]) >>
  simp[inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok _ _ _ _ _ _ un _ u` >>
  `lookup_var out u = SOME p /\ eval_operand len u = SOME n` by
    (Cases_on `len` >> gvs[Abbr `u`, lookup_var_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G un (mk_inst sid MSTORE [Var out;len] []) u` by
    (irule ptr_inst_ok_mstore >>
     gvs[Abbr `un`, Abbr `u`, ptr_covers_def, op_taint_def, lookup_var_def]) >>
  simp[] >>
  `step_inst_base (mk_inst sid MSTORE [Var out;len] []) u =
    OK (mstore (w2n p) n u)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  simp[] >>
  `step_prov PG G (mk_inst sid MSTORE [Var out;len] []) (mstore (w2n p) n u) = G /\
   step_taint (mk_inst sid MSTORE [Var out;len] []) u (mstore (w2n p) n u) un =
     un with t_mem := un.t_mem DIFF {j | w2n p <= j /\ j < w2n p + 32}` by
    (irule toplevel_immutable_mstore_ghost_frame >> gvs[Abbr `un`, op_taint_def]) >>
  gvs[Abbr `u`, Abbr `un`, inst_seq_ptr_def]
QED

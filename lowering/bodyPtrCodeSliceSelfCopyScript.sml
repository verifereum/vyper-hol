(* CODECOPY's pointer boundary.  Code offsets are clean words, not
   memory pointers; the destination alone must cover the copied range. *)
Theory bodyPtrCodeSliceSelfCopy
Ancestors
  fragExecPtr lowerDloadPtrExpansion lowerDloadPtrExpansionTransport
  emitHelperProps bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel words list finite_map

Theorem ptr_inst_ok_codecopy:
  !D ctx fn G tn s id dst src len a n fuel.
    ptr_covers G tn dst s (w2n n) /\
    eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
    op_taint tn src = {} /\ op_taint tn len = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id CODECOPY [Var dst; src; len] []) s
Proof
  rpt strip_tac >>
  `access_ok 0 G fn (mk_inst id CODECOPY [Var dst; src; len] []) s /\
   taint_ok fn tn (mk_inst id CODECOPY [Var dst; src; len] []) s` by
    (irule dload_codecopy_safe >>
     gvs[ptr_covers_def, mk_inst_def, eval_operand_def] >> metis_tac[]) >>
  simp[ptr_inst_ok_def, allocas_from_def, step_inst_non_invoke] >>
  `?w. eval_operand (Var dst) s = SOME w` by
    gvs[ptr_covers_def, eval_operand_def] >>
  `step_inst_base (mk_inst id CODECOPY [Var dst; src; len] []) s =
     OK (write_memory_with_expansion (w2n w)
       (TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w)) s)` by
    (irule step_CODECOPY >> simp[]) >>
  simp[write_memory_with_expansion_def]
QED

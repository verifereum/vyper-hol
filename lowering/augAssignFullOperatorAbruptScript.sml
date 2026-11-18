(* Allocation and exit resources at the supplied scalar abort endpoint. *)
Theory augAssignFullOperatorAbrupt
Ancestors
  exprLoweringProps venomMemProofs ptrDiscipline bodyPtrDefs haltExitProj exprSimDefs
  venomExecSemantics venomState venomInst list finite_map

Theorem augassign_abort_alloca_fields:
  !code s t a.
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
    run_inst_seq code s = Abort a t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >- (rename1 `step_inst_base h s = OK u` >>
      `u.vs_allocas = s.vs_allocas /\
       u.vs_alloca_next = s.vs_alloca_next` by
        metis_tac[step_inst_base_preserves_alloca_fields] >>
      first_x_assum drule >> simp[])
  >> metis_tac[step_inst_base_preserves_alloca_fields]
QED

Theorem augassign_operator_abrupt_resources:
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code /\
  run_inst_seq code s = Abort Revert_abort t /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  res = INR (Error (RuntimeError msg)) ==>
  (t with vs_inst_idx := j).vs_allocas = s.vs_allocas /\
  (t with vs_inst_idx := j).vs_alloca_next = s.vs_alloca_next /\
  allocas_from lo (t with vs_inst_idx := j) /\
  lo <= (t with vs_inst_idx := j).vs_alloca_next /\
  expr_exit res (Abort Revert_abort (t with vs_inst_idx := j)) /\
  (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt
     (Abort Revert_abort (t with vs_inst_idx := j))) /\
  halt_exit H cx ee res (Abort Revert_abort (t with vs_inst_idx := j)) /\
  (ctx_has_dalloca ctx ==>
    !u. (Abort Revert_abort (t with vs_inst_idx := j) = Halt u \/
         ?ir. Abort Revert_abort (t with vs_inst_idx := j) = IntRet ir u) ==>
        allocas_below_fmp u)
Proof
  strip_tac >> drule_all augassign_abort_alloca_fields >> strip_tac >>
  gvs[allocas_from_def, stmt_exit_ptr_def, expr_exit_def] >>
  conj_tac >- metis_tac[] >>
  irule halt_exit_not_halt >> simp[]
QED

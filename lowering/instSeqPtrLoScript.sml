(*
 * fragGasSeqPtr's straight-line pointer check, checked at (D0, 0), holds at
 * (D, lo) for every larger dead mask D and every bound lo that the start
 * state's ALLOCA sites and frontier already respect: the instruction-level
 * transport of ptrSafetyTransport's gas_path_ptr_zero_to_lo.
 *
 * TOP-LEVEL:
 *   inst_seq_ptr_zero_to_lo
 *)
Theory instSeqPtrLo
Ancestors
  fragGasSeqPtr ptrSafetyTransport venomExecProofs venomExecSemantics
  ptrDiscipline venomState

Theorem inst_seq_ptr_zero_to_lo:
  !insts D0 D lo ctx fn PG G tn s G' tn'.
    inst_seq_ptr D0 0 ctx fn PG G tn insts s G' tn' /\
    (!a st. D0.d_stor a st SUBSET D.d_stor a st) /\
    (!a st. D0.d_trans a st SUBSET D.d_trans a st) /\
    (!i. D0.d_imm i SUBSET D.d_imm i) /\
    (!r. D0.d_ret r SUBSET D.d_ret r) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next ==>
    inst_seq_ptr D lo ctx fn PG G tn insts s G' tn'
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule ptr_inst_ok_lower_bound_transport >>
      simp[] >> qexists_tac `0` >> simp[] >>
      irule ptr_inst_ok_dead_mono >> metis_tac[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >>
  `h.inst_opcode <> INVOKE` by
    metis_tac[venomExecProofsTheory.step_inst_base_OK_not_INVOKE] >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  drule_all step_inst_allocas_from >> strip_tac >>
  rpt conj_tac
  >- simp[]
  >- (fs[allocas_from_def] >> metis_tac[])
  >- (qexists_tac `D0` >> simp[])
QED

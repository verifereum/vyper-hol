(* A failed scalar assertion checks the prefix and stops before its suffix. *)
Theory abiDecodePtrScalarAbort
Ancestors
  bodyPtrBopScalarDynamic bodyPtrBopScalarSeq instSeqComposePtr
  exprLoweringProps venomExecSemantics venomInst list rich_list

Theorem scalar_seq_abort_replay_ptr:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = Abort a t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                     FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  qpat_x_assum `bop_scalar_seq R A code B` kall_tac >>
  drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> simp[] >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `run_inst_seq (prefix ++ [mk_inst id opc [op] []]) s = Abort a t` by
    (drule run_inst_seq_append >> disch_then (qspec_then `[mk_inst id opc [op] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (prefix ++ [mk_inst id opc [op] []])` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ, mk_inst_def, is_terminator_def] >>
     metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  irule inst_seq_ptr_abort_append >> metis_tac[]
QED

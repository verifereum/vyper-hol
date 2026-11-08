(* Consumer-level transport for scalar decoder phases. *)
Theory abiDecodePtrScalarFrame
Ancestors
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome abiDecodePtrMemberFrame
  bodyPtrDefs ptrDiscipline venomState venomExecSemantics venomInst
  finite_map pred_set

Theorem abi_decode_scalar_protected_operand:
  t.vs_labels = s.vs_labels /\ (!x. op = Var x ==> x IN R) /\
  (!x. x IN R ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) ==>
  eval_operand op t = eval_operand op s /\
  op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[lookup_var_def, op_taint_def]
QED

Theorem abi_decode_scalar_success_frame:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK u ==>
  ?H tm.
    inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
    (!op. op IN B ==> op_prov H op = NONE /\ op_taint tm op = {}) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. x IN R ==> lookup_var x (u with vs_inst_idx := j) = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!op. (!x. op = Var x ==> x IN R) ==>
      eval_operand op (u with vs_inst_idx := j) = eval_operand op s /\
      op_prov H op = op_prov G op /\ op_taint tm op = op_taint tn op) /\
    (!x cap. x IN R /\ ptr_covers G tn x s cap ==>
      ptr_covers H tm x (u with vs_inst_idx := j) cap) /\
    (!x b h. x IN R /\ abi_decode_ptr_window G tn s x b h ==>
      abi_decode_ptr_window H tm (u with vs_inst_idx := j) x b h)
Proof
  strip_tac >> drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `!x. x IN R ==> lookup_var x (u with vs_inst_idx := j) = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (fs[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `u = s with vs_vars := _` kall_tac >>
  conj_tac
  >- (gen_tac >> disch_tac >> irule abi_decode_scalar_protected_operand >>
      simp[] >> qexists_tac `R` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> fs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  rpt strip_tac >> irule abi_decode_ptr_window_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[]
QED

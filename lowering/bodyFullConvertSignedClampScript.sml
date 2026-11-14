(* Uniform clean-operand signed continuation certificates. *)
Theory bodyFullConvertSignedClamp
Ancestors
  bodyPtrSignedConvertClamp exprSimConvertFromBytes instSeqComposePtr
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragExec instIdxIndep
  exprLoweringProps emitHelperProps venomState venomInst venomExecSemantics
  ptrDiscipline finite_map words arithmetic list pred_set

Theorem double_check_uniform_prefix[local]:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq [mk_inst id opc1 [x;Lit lower] [a];
    mk_inst (id+1) ISZERO [Var a] [b]] s = OK u /\
  run_inst_seq [mk_inst (id+2) opc2 [x;Lit upper] [c];
    mk_inst (id+3) ISZERO [Var c] [d]] u = OK v /\
  run_inst_seq [mk_inst (id+4) AND [Var b;Var d] [e]] v = OK w ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc1 [x;Lit lower] [a];
       mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) opc2 [x;Lit upper] [c];
       mk_inst (id+3) ISZERO [Var c] [d];
       mk_inst (id+4) AND [Var b;Var d] [e]]
      (s with vs_inst_idx := q) H th) /\
    op_prov H (Var e) = NONE /\ op_taint th (Var e) = {} /\
    op_prov H x = NONE /\ op_taint th x = {} /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all scalar_double_checked_prefix >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[] >> rpt gen_tac >>
  drule_all scalar_double_checked_prefix >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `H' = H /\ th' = th` by metis_tac[inst_seq_ptr_ghost_unique] >>
  qpat_x_assum `H' = H` SUBST_ALL_TAC >>
  qpat_x_assum `th' = th` SUBST_ALL_TAC >>
  first_assum (qspec_then `q` ACCEPT_TAC)
QED

(* A failed ASSERT changes a field retained by state_frame. *)
Theorem failed_assert_not_success_frame[local]:
  ~s.vs_halted ==>
  state_frame ((revert_state (set_returndata [] s)) with vs_inst_idx := j) <>
  state_frame (s with vs_inst_idx := j)
Proof
  simp[stateFrameTheory.state_frame_def, revert_state_def, set_returndata_def] >>
  strip_tac >>
  disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >> simp[]
QED

Theorem double_check_uniform_certificate[local]:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq
    [mk_inst id opc1 [x;Lit lower] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x;Lit upper] [c]; mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b;Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s = OK t \/
   run_inst_seq
    [mk_inst id opc1 [x;Lit lower] [a]; mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) opc2 [x;Lit upper] [c]; mk_inst (id+3) ISZERO [Var c] [d];
     mk_inst (id+4) AND [Var b;Var d] [e]; mk_inst (id+5) ASSERT [Var e] []] s = Abort err t) ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc1 [x;Lit lower] [a]; mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) opc2 [x;Lit upper] [c]; mk_inst (id+3) ISZERO [Var c] [d];
       mk_inst (id+4) AND [Var b;Var d] [e]; mk_inst (id+5) ASSERT [Var e] []]
      (s with vs_inst_idx := q) H th) /\
    op_prov H x = NONE /\ op_taint th x = {} /\
    (!p. ~MEM p [a;b;c;d;e] ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_double_check_prefix_runs >> strip_tac >>
  drule_all double_check_uniform_prefix >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[] >> rpt gen_tac >>
  irule (PURE_REWRITE_RULE [APPEND] (Q.INST
    [`xs` |-> `[mk_inst id opc1 [x;Lit lower] [a];
      mk_inst (id+1) ISZERO [Var a] [b]; mk_inst (id+2) opc2 [x;Lit upper] [c];
      mk_inst (id+3) ISZERO [Var c] [d]; mk_inst (id+4) AND [Var b;Var d] [e]]`]
    (Q.INST [`id` |-> `id+5`] (SPEC_ALL checked_prefix_assert_certificate)))) >>
  imp_res_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_opcode_filter >>
  simp[mk_inst_def, is_terminator_def] >>
  simp[GSYM mk_inst_def] >>
  qexistsl [`w with vs_inst_idx := q`,`value`] >>
  simp[eval_operand_def, lookup_var_def] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  conj_tac
  >- (qpat_abbrev_tac `code = [_;_;_;_;_]` >>
      `run_inst_seq code s = OK w` by
        (simp[Abbr `code`] >>
         qpat_assum `run_inst_seq [_;_] s = OK u` (mp_tac o MATCH_MP run_inst_seq_append) >>
         disch_then (qspec_then
           `[mk_inst (id+2) opc2 [x;Lit upper] [c];
             mk_inst (id+3) ISZERO [Var c] [d];
             mk_inst (id+4) AND [Var b;Var d] [e]]` mp_tac) >>
         simp[] >> disch_then SUBST1_TAC >>
         qpat_assum `run_inst_seq [_;_] u = OK v` (mp_tac o MATCH_MP run_inst_seq_append) >>
         disch_then (qspec_then `[mk_inst (id+4) AND [Var b;Var d] [e]]` mp_tac) >>
         simp[]) >>
      simp[run_inst_seq_inst_idx, Abbr `code`, mk_inst_def,
           is_terminator_def, exec_result_map_def]) >>
  fs[eval_operand_def, lookup_var_def]
QED

Theorem double_check_runtime_endpoint[local]:
  MEM opc1 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  MEM opc2 [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  code = [mk_inst id opc1 [x;Lit lower] [a];
    mk_inst (id+1) ISZERO [Var a] [b];
    mk_inst (id+2) opc2 [x;Lit upper] [c];
    mk_inst (id+3) ISZERO [Var c] [d];
    mk_inst (id+4) AND [Var b;Var d] [e];
    mk_inst (id+5) ASSERT [Var e] []] /\
  (!z. x = Var z ==> ~MEM z [a;b;c;d;e]) ==>
  (!t. run_inst_seq code s = OK t ==>
    state_frame t = state_frame s /\
    (!z. ~MEM z [a;b;c;d;e] ==> lookup_var z t = lookup_var z s) /\
    eval_operand x t = eval_operand x s) /\
  (!err t. run_inst_seq code s = Abort err t ==>
    state_frame t = state_frame (revert_state (set_returndata [] s)) /\
    (!z. ~MEM z [a;b;c;d;e] ==> lookup_var z t = lookup_var z s) /\
    eval_operand x t = eval_operand x s)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `((t with vs_vars := s.vs_vars) = s) /\
       (!z. ~MEM z [a;b;c;d;e] ==> lookup_var z t = lookup_var z s)` by
        (irule scalar_double_check_runtime_frame >> metis_tac[]) >>
      conj_tac
      >- (qpat_x_assum `(t with vs_vars := _) = s` (mp_tac o AP_TERM ``state_frame``) >>
          simp[stateFrameTheory.state_frame_def]) >>
      conj_tac >- simp[] >>
      `t.vs_labels = s.vs_labels` by
        (qpat_x_assum `(t with vs_vars := _) = s`
          (mp_tac o AP_TERM ``\v:venom_state. v.vs_labels``) >> simp[]) >>
      Cases_on `x` >> simp[eval_operand_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `code = _` SUBST_ALL_TAC >>
  qpat_x_assum `run_inst_seq _ s = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs(),
    bodyPtrSignedConvertScalarOpsTheory.convert_scalar_no_abort,
    bodyPtrSignedConvertScalarOpsTheory.scalar_iszero_no_abort] >> strip_tac >>
  qpat_x_assum `step_inst_base (mk_inst id opc1 _ _) _ = _`
    (mp_then Any mp_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `w1` SUBST_ALL_TAC) >>
  qpat_x_assum `step_inst_base (mk_inst _ opc2 _ _) _ = _`
    (mp_then Any mp_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_run_shape) >> simp[] >>
  disch_then (qx_choose_then `w2` SUBST_ALL_TAC) >>
  qpat_x_assum `MEM opc1 _` kall_tac >>
  qpat_x_assum `MEM opc2 _` kall_tac >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac bodyPtrSignedConvertIszeroTheory.iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    (mp_then Any strip_assume_tac bodyPtrSignedConvertIszeroTheory.iszero_run_shape) >> gvs[] >>
  qpat_x_assum `step_inst_base (mk_inst _ AND _ _) _ = _`
    (mp_then Any mp_tac bodyPtrSignedConvertScalarOpsTheory.convert_scalar_run_shape) >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV
    [step_inst_base_def, mk_inst_def, instruction_accessors,
     instruction_accfupds, combinTheory.K_THM, opcode_case_def]))) >>
  simp[AllCaseEqs(), eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  simp[stateFrameTheory.state_frame_def, revert_state_def, set_returndata_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `x` >> gvs[eval_operand_def, lookup_var_def, revert_state_def,
                      set_returndata_def, update_var_def, FLOOKUP_UPDATE]
QED

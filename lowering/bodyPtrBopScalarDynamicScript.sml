Theory bodyPtrBopScalarDynamic
Ancestors
  bodyPtrBopScalarSeq bodyPtrBopScalarCompile exprLoweringProps fragExec fragGasSeqPtr
  venomExecSemantics venomInst venomState ptrDiscipline fragGasPathPtr finite_map list rich_list pred_set

Theorem bop_pure_no_abort[local]:
  (!f inst s a t. exec_pure1 f inst s <> Abort a t) /\
  (!f inst s a t. exec_pure2 f inst s <> Abort a t) /\
  (!f inst s a t. exec_pure3 f inst s <> Abort a t)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()]
QED

Theorem bop_scalar_no_abort:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] ==>
  step_inst_base (mk_inst id opc ops [tmp]) s <> Abort a t
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors, instruction_accfupds,
                    combinTheory.K_THM, opcode_case_def] >>
  simp[bop_pure_no_abort, AllCaseEqs()]
QED

Theorem bop_scalar_seq_abort_prefix:
  !code R A B s a t.
  bop_scalar_seq R A code B /\ run_inst_seq code s = Abort a t ==>
  ?prefix suffix C id opc op u.
    code = prefix ++ [mk_inst id opc [op] []] ++ suffix /\
    bop_scalar_seq R A prefix C /\ run_inst_seq prefix s = OK u /\
    (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\ op IN C /\
    step_inst_base (mk_inst id opc [op] []) u = Abort a t
Proof
  Induct
  >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[Once run_inst_seq_def]
  >- suspend "ok" >>
  suspend "abort"
QED

Resume bop_scalar_seq_abort_prefix[abort]:
  qpat_x_assum `bop_scalar_seq _ _ (h::code) _` mp_tac >>
  pure_once_rewrite_tac [bop_scalar_seq_def] >> strip_tac
  >- metis_tac[bop_scalar_no_abort] >>
  qexistsl_tac [`[]`, `code`, `A`, `id`, `opc`, `op`, `s`] >>
  gvs[run_inst_seq_def]
QED

Resume bop_scalar_seq_abort_prefix[ok]:
  qpat_x_assum `bop_scalar_seq _ _ (h::code) _` mp_tac >>
  pure_once_rewrite_tac [bop_scalar_seq_def] >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  rename1 `step_inst_base (mk_inst aid aopc [arg] []) u = Abort a t` >>
  qexistsl_tac [`h::prefix`, `suffix`, `C`, `aid`, `aopc`, `arg`, `u`] >>
  simp[Once run_inst_seq_def] >>
  pure_once_rewrite_tac [bop_scalar_seq_def] >>
  FIRST [
    (qpat_assum `h = mk_inst _ _ _ [_]` kall_tac >>
     disj1_tac >> qexistsl_tac [`id`, `opc`, `ops`, `tmp`] >> simp[]),
    (qpat_assum `h = mk_inst _ _ _ []` kall_tac >>
     disj2_tac >> qexistsl_tac [`id`, `opc`, `op`] >> simp[])]
QED

Finalise bop_scalar_seq_abort_prefix

Theorem bop_scalar_seq_abort_path:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = Abort a t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn' n j. gas_path_ptr D 0 ctx fn PG G tn s n G' tn'
      (Abort a (t with vs_inst_idx := j)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_abort_prefix >> strip_tac >>
  `isPREFIX (prefix ++ [mk_inst id opc [op] []])
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
  qpat_x_assum `bop_scalar_seq R A code B` kall_tac >>
  drule bop_scalar_seq_assert_abort_path >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> simp[] >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[] >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> metis_tac[]
QED

Theorem bop_scalar_certificate_result_path:
  (?B. bop_scalar_seq R A code B /\ v IN B) /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[]
QED

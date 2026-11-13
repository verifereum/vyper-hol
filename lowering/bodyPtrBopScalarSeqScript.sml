Theory bodyPtrBopScalarSeq
Ancestors
  bodyPtrBopScalarStep bodyPtrBopAssert fragGasSeqPtr exprLoweringProps
  instIdxIndep ptrDiscipline venomExecSemantics venomInst venomState finite_map list pred_set

(* A static availability certificate is needed in addition to inst_seq_ptr:
   it records which operands later scalar instructions are permitted to read,
   without defining another execution or a recursive ghost evaluator. *)
Definition bop_scalar_seq_def:
  (bop_scalar_seq R A [] B <=> B = A) /\
  (bop_scalar_seq R A (i::code) B <=>
    (?id opc ops tmp.
       i = mk_inst id opc ops [tmp] /\
       MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
                LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
                SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
       EVERY (\op. op IN A) ops /\ tmp NOTIN R /\
       bop_scalar_seq R (Var tmp INSERT A) code B) \/
    (?id opc op.
       i = mk_inst id opc [op] [] /\
       (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\ op IN A /\
       bop_scalar_seq R A code B))
End

Theorem bop_scalar_seq_nil[simp]:
  bop_scalar_seq R A [] B <=> B = A
Proof
  simp[bop_scalar_seq_def]
QED

Theorem bop_scalar_seq_single:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op IN A) ops /\ tmp NOTIN R ==>
  bop_scalar_seq R A [mk_inst id opc ops [tmp]] (Var tmp INSERT A)
Proof
  strip_tac >> simp[Once bop_scalar_seq_def] >>
  disj1_tac >> qexistsl_tac [`id`, `opc`, `ops`, `tmp`] >> fs[]
QED

Theorem bop_scalar_seq_assert:
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\ op IN A ==>
  bop_scalar_seq R A [mk_inst id opc [op] []] A
Proof
  strip_tac >> simp[Once bop_scalar_seq_def] >>
  disj2_tac >> qexistsl_tac [`id`, `opc`, `op`] >> simp[]
QED

Theorem bop_scalar_seq_opcodes:
  !code R A B. bop_scalar_seq R A code B ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) code
Proof
  Induct >> simp[Once bop_scalar_seq_def] >> rpt strip_tac >>
  gvs[mk_inst_def, MEM, is_terminator_def] >> metis_tac[]
QED

Theorem bop_scalar_available_step:
  MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
           LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
           SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN] /\
  EVERY (\op. op IN A) ops /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  step_inst_base (mk_inst id opc ops [tmp]) s = OK u ==>
  (!op. op IN Var tmp INSERT A ==>
    op_prov (step_prov PG G (mk_inst id opc ops [tmp]) u) op = NONE /\
    op_taint (step_taint (mk_inst id opc ops [tmp]) s u tn) op = {}) /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops [tmp]) s u tn).t_imm = tn.t_imm /\
  (!x. x <> tmp ==>
    FLOOKUP (step_prov PG G (mk_inst id opc ops [tmp]) u) x = FLOOKUP G x /\
    FLOOKUP (step_taint (mk_inst id opc ops [tmp]) s u tn).t_var x =
      FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    (drule_all bop_scalar_state_frame >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  drule_all bop_scalar_ghost_frame >>
  disch_then (qspecl_then [`tmp`, `id`, `PG`] strip_assume_tac) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `op` >> gvs[op_prov_def, op_taint_def] >>
  rename1 `Var v IN A` >>
  Cases_on `v = tmp` >> gvs[op_prov_def, op_taint_def] >>
  qpat_x_assum `!op. op IN A ==> _` (qspec_then `Var v` mp_tac) >>
  simp[]
QED

Theorem bop_scalar_seq_run:
  !code R A B s t G tn.
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK t ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  Induct
  >- (simp[bop_scalar_seq_def, run_inst_seq_def, inst_seq_ptr_def] >>
      rpt strip_tac >> qexistsl_tac [`G`, `tn`] >> simp[]) >>
  rpt gen_tac >>
  pure_once_rewrite_tac[bop_scalar_seq_def, run_inst_seq_def] >>
  strip_tac >> FULL_SIMP_TAC std_ss [AllCaseEqs(), exec_result_distinct, exec_result_11] >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  TRY (rename1 `step_inst_base (mk_inst id opc ops [tmp]) s = OK u` >>
       suspend "scalar" >> NO_TAC) >>
  suspend "assert"
QED

Resume bop_scalar_seq_run[scalar]:
  drule_all bop_scalar_available_step >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [tmp]) s` by
    (irule bop_scalar_ptr_inst_ok >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `run_inst_seq code (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def] >>
  first_x_assum (drule_at Any) >> disch_then drule >>
  disch_then drule >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  simp[Once inst_seq_ptr_def] >>
  rpt strip_tac >> metis_tac[]
QED

Resume bop_scalar_seq_run[assert]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[] >>
  rename1 `step_inst_base _ s = OK u` >>
  `u = s` by metis_tac[bop_assert_success_state] >>
  qpat_x_assum `u = s` SUBST_ALL_TAC >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G tn (i::code)` >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule bop_assert_ptr_inst_ok >>
     simp[] >> metis_tac[]) >>
  `step_prov PG G i s = G /\ step_taint i s s tn = tn` by
    simp[Abbr `i`, bop_assert_ghost] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `run_inst_seq code (s with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def] >>
  qpat_x_assum `!R A B s t G tn. _` (drule_at Any) >> disch_then drule >>
  disch_then drule >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >>
  simp[Once inst_seq_ptr_def] >> gvs[Abbr `i`]
QED

Finalise bop_scalar_seq_run

Theorem bop_scalar_seq_path:
  bop_scalar_seq R A code B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq code s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> GAS) code` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem bop_inst_seq_ptr_append:
  !prefix s t G tn G1 tn1 suffix G2 tn2.
  EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
  run_inst_seq prefix s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn prefix s G1 tn1 /\
  inst_seq_ptr D lo ctx fn PG G1 tn1 suffix
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH prefix) G2 tn2 ==>
  inst_seq_ptr D lo ctx fn PG G tn (prefix ++ suffix) s G2 tn2
Proof
  Induct
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[Once run_inst_seq_def, Once inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `run_inst_seq prefix (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, exec_result_map_def] >>
  simp[Once inst_seq_ptr_def] >>
  first_x_assum irule >>
  qexistsl_tac [`G1`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tn1`] >>
  simp[] >>
  `LENGTH prefix + SUC s.vs_inst_idx = SUC (LENGTH prefix) + s.vs_inst_idx`
    by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem bop_scalar_seq_assert_abort_checked:
  bop_scalar_seq R A prefix B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq prefix s = OK t /\ op IN B /\
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  step_inst_base (mk_inst id opc [op] []) t = Abort a v ==>
  ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
      (prefix ++ [mk_inst id opc [op] []]) s G' tn' /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) prefix` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ]) >>
  irule bop_inst_seq_ptr_append >> simp[] >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `~is_terminator (mk_inst id opc [op] []).inst_opcode` by
    gvs[mk_inst_def, is_terminator_def] >>
  `step_inst_base (mk_inst id opc [op] [])
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH prefix) =
   Abort a (v with vs_inst_idx := s.vs_inst_idx + LENGTH prefix)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  gvs[Once inst_seq_ptr_def] >>
  irule bop_assert_ptr_inst_ok >> simp[] >> metis_tac[]
QED

Theorem bop_scalar_seq_assert_abort_path:
  bop_scalar_seq R A prefix B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq prefix s = OK t /\ op IN B /\
  (opc = ASSERT \/ opc = ASSERT_UNREACHABLE) /\
  step_inst_base (mk_inst id opc [op] []) t = Abort a v /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (prefix ++ [mk_inst id opc [op] []])
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn' n j. gas_path_ptr D 0 ctx fn PG G tn s n G' tn'
      (Abort a (v with vs_inst_idx := j)) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP G' x = FLOOKUP G x /\
                      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >> drule bop_scalar_seq_assert_abort_checked >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (prefix ++ [mk_inst id opc [op] []])` by
    (drule bop_scalar_seq_opcodes >>
     gvs[EVERY_CONJ, EVERY_APPEND, mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (prefix ++ [mk_inst id opc [op] []]) s = Abort a v` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `[mk_inst id opc [op] []]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  gvs[] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_abort_gas_path_ptr >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  disch_then (qspec_then `bb` mp_tac) >>
  simp[EVERY_APPEND, mk_inst_def, is_terminator_def] >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`, `n`, `j`] >> simp[]
QED

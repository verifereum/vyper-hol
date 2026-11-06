Theory forPtrRangeChecked
Ancestors
  forPtrCheckedScalar forPtrRangeEntry exprSendPtr fragGasSeqPtr fragGasPathPtr
  exprSimOperands instIdxIndep emitHelperProps
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  exprLoweringProps rich_list finite_map pred_set list

(* S1's arbitrary-operand overwrite rule is local to stmtSimForRange. *)
Theorem for_checked_eval_operand_overwrite[local]:
  (!y. op = Var y ==> y <> x) ==>
  eval_operand op (update_var x w s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_update_var, update_var_def]
QED

Theorem for_checked_assign_step[local]:
  eval_operand op s = SOME w ==>
  step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s)
Proof
  simp[Once step_inst_base_def, mk_inst_def]
QED

(* The first four instructions establish the order-test predicate.  The
   following ASSERT is deliberately outside this successful scalar prefix. *)
Theorem for_checked_order_prefix_ptr:
  lookup_block ee.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst i ASSIGN [op1] [cv];
     mk_inst (i+1) SUB [op2;op1] [rv];
     mk_inst (i+2) cmp [op1;op2] [g1];
     mk_inst (i+3) ISZERO [Var g1] [z1]] ++ tail /\
  MEM cmp [SGT;GT] /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  ALL_DISTINCT [cv;rv;g1;z1] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1]) /\
  bad = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad = 0w)) s3 ==>
  gas_path_ptr D 0 ctx fn PG G tn ee 0
    (DRESTRICT G (COMPL {cv;rv;g1;z1}))
    (tn with t_var := tn.t_var |++ [(cv,{});(rv,{});(g1,{});(z1,{})])
    (OK (s4 with vs_inst_idx := 4))
Proof
  strip_tac >>
  `!x w s. MEM x [cv;rv;g1;z1] ==>
     eval_operand op1 (update_var x w s) = eval_operand op1 s /\
     eval_operand op2 (update_var x w s) = eval_operand op2 s` by
    (rpt strip_tac >> irule for_checked_eval_operand_overwrite >> metis_tac[]) >>
  `eval_operand op1 s1 = SOME a /\ eval_operand op2 s1 = SOME b /\
   eval_operand op1 s2 = SOME a /\ eval_operand op2 s2 = SOME b` by
    metis_tac[listTheory.MEM] >>
  `step_inst_base (mk_inst i ASSIGN [op1] [cv]) ee = OK s1` by
    (gvs[] >> irule for_checked_assign_step >> simp[]) >>
  `step_inst_base (mk_inst (i+1) SUB [op2;op1] [rv]) s1 = OK s2` by
    (gvs[] >> irule step_SUB >> simp[]) >>
  `step_inst_base (mk_inst (i+2) cmp [op1;op2] [g1]) s2 = OK s3` by
    (Cases_on `cmp = SGT`
     >- (gvs[] >> irule step_SGT >> simp[]) >>
     gvs[] >> irule step_GT >> simp[]) >>
  `step_inst_base (mk_inst (i+3) ISZERO [Var g1] [z1]) s3 = OK s4` by
    (qpat_x_assum `s4 = _` SUBST1_TAC >> irule step_ISZERO >>
     simp[eval_operand_def,lookup_var_update_var]) >>
  suspend "certificate"
QED

Resume for_checked_order_prefix_ptr[certificate]:
  qmatch_goalsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn ee 0 Gf tf _` >>
  qabbrev_tac `code = [mk_inst i ASSIGN [op1] [cv];
     mk_inst (i+1) SUB [op2;op1] [rv];
     mk_inst (i+2) cmp [op1;op2] [g1];
     mk_inst (i+3) ISZERO [Var g1] [z1]]` >>
  `inst_seq_ptr D 0 ctx fn PG G tn code ee Gf tf` by
    (simp[Abbr `code`] >> irule (iffRL for_checked_scalar_seq_cons) >>
     simp[] >> qexists_tac `a` >> simp[] >>
     qpat_assum `s1 = _` (fn th => rewrite_tac[GSYM th]) >>
     irule (iffRL for_checked_scalar_seq_index) >> simp[] >>
     (conj_tac >- metis_tac[for_checked_clean_operand_overwrite]) >>
     qexists_tac `b-a` >> simp[] >>
     qpat_assum `s2 = _` (fn th => rewrite_tac[GSYM th]) >>
     irule (iffRL for_checked_scalar_seq_index) >> simp[] >>
     (conj_tac >- (rpt strip_tac >>
       simp[for_checked_operand_taint_update, for_checked_operand_prov_restrict] >>
       metis_tac[])) >>
     (conj_tac >- gvs[]) >> qexists_tac `bool_to_word bad` >> simp[] >>
     qpat_assum `s3 = _` (fn th => rewrite_tac[GSYM th]) >>
     suspend "last_scalar") >>
  suspend "prefix_path"
QED

Resume for_checked_order_prefix_ptr[last_scalar]:
  (conj_tac >- (qpat_x_assum `step_inst_base (mk_inst _ cmp _ _) _ = _`
    mp_tac >> simp[])) >>
  irule (iffRL for_checked_scalar_seq_index) >> simp[] >>
  (conj_tac >- simp[for_checked_operand_taint_update,
    for_checked_operand_prov_removed]) >>
  qexists_tac `bool_to_word (bool_to_word bad = 0w)` >>
  (conj_tac >- (qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
    mp_tac >> simp[])) >>
  simp[inst_seq_ptr_def, Abbr `Gf`, Abbr `tf`, FUPDATE_LIST_THM] >>
  AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[]
QED

Resume for_checked_order_prefix_ptr[prefix_path]:
  `run_inst_seq code ee = OK s4` by
    simp[Abbr `code`, run_inst_seq_def, IgnAsm `s1 = _`, IgnAsm `s2 = _`,
         IgnAsm `s3 = _`, IgnAsm `s4 = _`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (simp[Abbr `code`, mk_inst_def, is_terminator_def] >> gvs[is_terminator_def]) >>
  `isPREFIX code (DROP ee.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[Abbr `code`, mk_inst_def] >> gvs[]
QED
Finalise for_checked_order_prefix_ptr

(* A bound test, independent of the preceding order test and of the block
   index.  The comparison outputs need not be distinct for this prefix. *)
Theorem for_checked_gt_zero_prefix_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst i GT [left;right] [g];
            mk_inst (i+1) ISZERO [Var g] [z]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  s1 = update_var g (bool_to_word (w2n a > w2n b)) s /\
  s2 = update_var z (bool_to_word (bool_to_word (w2n a > w2n b) = 0w)) s1 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {g;z}))
    (tn with t_var := tn.t_var |++ [(g,{});(z,{})])
    (OK (s2 with vs_inst_idx := s.vs_inst_idx + 2))
Proof
  strip_tac >>
  `step_inst_base (mk_inst i GT [left;right] [g]) s = OK s1` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >> irule step_GT >> simp[]) >>
  `step_inst_base (mk_inst (i+1) ISZERO [Var g] [z]) s1 = OK s2` by
    (qpat_x_assum `s2 = _` SUBST1_TAC >> irule step_ISZERO >>
     simp[eval_operand_def, lookup_var_update_var]) >>
  qmatch_goalsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf _` >>
  qabbrev_tac `code = [mk_inst i GT [left;right] [g];
                      mk_inst (i+1) ISZERO [Var g] [z]]` >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s Gf tf` by
    (simp[Abbr `code`] >> irule (iffRL for_checked_scalar_seq_cons) >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexists_tac `bool_to_word (w2n a > w2n b)` >> simp[] >>
     qpat_assum `s1 = _` (fn th => rewrite_tac[GSYM th]) >>
     irule (iffRL for_checked_scalar_seq_index) >> simp[] >>
     qexists_tac `bool_to_word (bool_to_word (w2n a > w2n b) = 0w)` >>
     (conj_tac >- (qpat_x_assum `step_inst_base (mk_inst _ ISZERO _ _) _ = _`
       mp_tac >> simp[])) >>
     simp[inst_seq_ptr_def, Abbr `Gf`, Abbr `tf`, FUPDATE_LIST_THM] >>
     AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[]) >>
  `run_inst_seq code s = OK s2` by
    simp[Abbr `code`, run_inst_seq_def, IgnAsm `s1 = _`, IgnAsm `s2 = _`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[Abbr `code`, mk_inst_def] >> gvs[]
QED

(* Shared assertion composition keeps both checked failure and success paths. *)
Theorem for_checked_assert_prefix_ptr:
  gas_path_ptr D 0 ctx fn PG G tn s n Gend tt (OK t) /\
  ~ctx_has_dalloca ctx /\ op_taint tt op = {} /\
  eval_operand op t = SOME w /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) ==>
  (w = 0w ==> ?u. gas_path_ptr D 0 ctx fn PG G tn s n Gend tt
    (Abort Revert_abort u)) /\
  (w <> 0w ==> gas_path_ptr D 0 ctx fn PG G tn s n Gend tt
    (OK (t with vs_inst_idx := SUC t.vs_inst_idx)))
Proof
  strip_tac >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  conj_tac >> strip_tac
  >- (`gas_path_ptr D 0 ctx fn PG Gend tt t 0 Gend tt
        (Abort Revert_abort (revert_state (set_returndata [] t)))` by
        (irule assert_fail_path_ptr >> simp[] >> metis_tac[]) >>
      drule gas_path_ptr_then >> disch_then drule >> simp[] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG Gend tt t 0 Gend tt
     (OK (t with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule assert_ok_path_ptr >> simp[] >> metis_tac[]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >> simp[]
QED

Theorem for_checked_order_assert_ptr:
  lookup_block ee.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst i ASSIGN [op1] [cv];
     mk_inst (i+1) SUB [op2;op1] [rv];
     mk_inst (i+2) cmp [op1;op2] [g1];
     mk_inst (i+3) ISZERO [Var g1] [z1];
     mk_inst (i+4) ASSERT [Var z1] []] ++ tail /\
  MEM cmp [SGT;GT] /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  ALL_DISTINCT [cv;rv;g1;z1] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1]) /\
  bad = (if cmp = SGT then word_gt a b else w2n a > w2n b) /\
  s1 = update_var cv a ee /\ s2 = update_var rv (b-a) s1 /\
  s3 = update_var g1 (bool_to_word bad) s2 /\
  s4 = update_var z1 (bool_to_word (bool_to_word bad = 0w)) s3 ==>
  (bad ==> ?t. gas_path_ptr D 0 ctx fn PG G tn ee 0
    (DRESTRICT G (COMPL {cv;rv;g1;z1}))
    (tn with t_var := tn.t_var |++ [(cv,{});(rv,{});(g1,{});(z1,{})])
    (Abort Revert_abort t)) /\
  (~bad ==> gas_path_ptr D 0 ctx fn PG G tn ee 0
    (DRESTRICT G (COMPL {cv;rv;g1;z1}))
    (tn with t_var := tn.t_var |++ [(cv,{});(rv,{});(g1,{});(z1,{})])
    (OK (s4 with vs_inst_idx := 5)))
Proof
  strip_tac >>
  qabbrev_tac `G4 = DRESTRICT G (COMPL {cv;rv;g1;z1})` >>
  qabbrev_tac `t4 = tn with t_var := tn.t_var |++ [(cv,{});(rv,{});(g1,{});(z1,{})]` >>
  `gas_path_ptr D 0 ctx fn PG G tn ee 0 G4 t4
     (OK (s4 with vs_inst_idx := 4))` by
    (simp[Abbr `G4`, Abbr `t4`] >> irule for_checked_order_prefix_ptr >>
     simp[mk_inst_def] >> gvs[] >> metis_tac[]) >>
  suspend "assert_paths"
QED

Resume for_checked_order_assert_ptr[assert_paths]:
  `~(s4 with vs_inst_idx := 4).vs_halted` by
    metis_tac[gas_path_ptr_ok_not_halted] >>
  `lookup_block (s4 with vs_inst_idx := 4).vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb 4 = SOME (mk_inst (i+4) ASSERT [Var z1] [])` by
    simp[update_var_def, get_instruction_def] >>
  `op_taint t4 (Var z1) = {}` by
    simp[Abbr `t4`, FUPDATE_LIST_THM, for_checked_operand_taint_update] >>
  `eval_operand (Var z1) (s4 with vs_inst_idx := 4) =
     SOME (bool_to_word (bool_to_word bad = 0w))` by
    (simp[instIdxIndepTheory.eval_op_inst_idx] >>
     simp[eval_operand_def, lookup_var_update_var]) >>
  `get_instruction bb (s4 with vs_inst_idx := 4).vs_inst_idx =
     SOME (mk_inst (i+4) ASSERT [Var z1] [])` by simp[] >>
  drule_all for_checked_assert_prefix_ptr >>
  simp[bool_to_word_def]
QED
Finalise for_checked_order_assert_ptr

Theorem for_checked_add_jump_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst i ADD [left;right] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst j JMP [Label lbl] []) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (jump_to lbl (update_var out (a+b) s)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst i ADD [left;right] [out]) s =
     OK (update_var out (a+b) s)` by (irule step_ADD >> simp[]) >>
  `new_site_bytes s (update_var out (a+b) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  qabbrev_tac `Gf = DRESTRICT G (COMPL {out})` >>
  qabbrev_tac `tf = tn with t_var := tn.t_var |+ (out,{})` >>
  qabbrev_tac `u = (update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)` by
    (simp[Abbr `Gf`, Abbr `tf`, Abbr `u`] >>
     irule for_checked_scalar_clean_path_ptr >> simp[mk_inst_def] >>
     simp[GSYM mk_inst_def] >> metis_tac[]) >>
  `~u.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `gas_path_ptr D 0 ctx fn PG Gf tf u 0 Gf tf (OK (jump_to lbl u))` by
    (irule for_range_jump_path_ptr >> simp[Abbr `u`, update_var_def] >>
     metis_tac[]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >>
  simp[Abbr `u`, jump_to_def]
QED

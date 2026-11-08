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

Theorem for_entry_checked_path_ptr:
  lookup_block ee.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst i ASSIGN [op1] [cv];
     mk_inst (i+1) SUB [op2;op1] [rv];
     mk_inst (i+2) cmp [op1;op2] [g1];
     mk_inst (i+3) ISZERO [Var g1] [z1];
     mk_inst (i+4) ASSERT [Var z1] [];
     mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
     mk_inst (i+6) ISZERO [Var g2] [z2];
     mk_inst (i+7) ASSERT [Var z2] [];
     mk_inst (i+8) ADD [op1;Var rv] [ev];
     mk_inst (i+9) JMP [Label lbl] []] /\
  MEM cmp [SGT;GT] /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) ==>
  (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
     w2n (b-a) > w2n (n2w bound : bytes32)) ==>
     ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn ee 0 Gf tf
       (Abort Revert_abort u)) /\
  (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
   ~(w2n (b-a) > w2n (n2w bound : bytes32)) ==>
   ?vs. lookup_var cv (ee with vs_vars := vs) = SOME a /\
     lookup_var ev (ee with vs_vars := vs) = SOME (a+(b-a)) /\
     (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
       lookup_var x (ee with vs_vars := vs) = lookup_var x ee) /\
     gas_path_ptr D 0 ctx fn PG G tn ee 0
       (DRESTRICT G (COMPL {cv;rv;g1;z1;g2;z2;ev}))
       (tn with t_var := tn.t_var |++
         [(cv,{});(rv,{});(g1,{});(z1,{});(g2,{});(z2,{});(ev,{})])
       (OK (jump_to lbl (ee with vs_vars := vs))))
Proof
  strip_tac >>
  qabbrev_tac `bad1 = if cmp = SGT then word_gt a b else w2n a > w2n b` >>
  qabbrev_tac `bad2 = (w2n (b-a) > w2n (n2w bound : bytes32))` >>
  qabbrev_tac `s1 = update_var cv a ee` >>
  qabbrev_tac `s2 = update_var rv (b-a) s1` >>
  qabbrev_tac `s3 = update_var g1 (bool_to_word bad1) s2` >>
  qabbrev_tac `s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3` >>
  qabbrev_tac `G4 = DRESTRICT G (COMPL {cv;rv;g1;z1})` >>
  qabbrev_tac `t4 = tn with t_var := tn.t_var |++ [(cv,{});(rv,{});(g1,{});(z1,{})]` >>
  `(bad1 ==> ?u. gas_path_ptr D 0 ctx fn PG G tn ee 0 G4 t4
       (Abort Revert_abort u)) /\
   (~bad1 ==> gas_path_ptr D 0 ctx fn PG G tn ee 0 G4 t4
       (OK (s4 with vs_inst_idx := 5)))` by
    (simp[Abbr `G4`, Abbr `t4`] >> irule for_checked_order_assert_ptr >>
     simp[Abbr `bad1`, Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `s4`] >>
     (conj_tac >- gvs[ALL_DISTINCT]) >>
     qexistsl_tac [`a`,`b`,`cmp`,`i`,`op1`,`op2`] >>
     simp[] >> gvs[ALL_DISTINCT] >> metis_tac[]) >>
  Cases_on `bad1`
  >- (simp[] >> metis_tac[]) >>
  qpat_x_assum `~bad1 ==> _` mp_tac >> simp[] >> strip_tac >>
  suspend "bound_prefix"
QED

Resume for_entry_checked_path_ptr[bound_prefix]:
  qabbrev_tac `u4 = s4 with vs_inst_idx := 5` >>
  qabbrev_tac `s5 = update_var g2 (bool_to_word bad2) u4` >>
  qabbrev_tac `s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5` >>
  qabbrev_tac `G6 = DRESTRICT G4 (COMPL {g2;z2})` >>
  qabbrev_tac `t6 = t4 with t_var := t4.t_var |++ [(g2,{});(z2,{})]` >>
  `~u4.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `gas_path_ptr D 0 ctx fn PG G4 t4 u4 0 G6 t6
      (OK (s6 with vs_inst_idx := u4.vs_inst_idx + 2))` by
    (simp[Abbr `G6`, Abbr `t6`] >>
     irule for_checked_gt_zero_prefix_ptr >>
     simp[Abbr `s5`, Abbr `s6`, Abbr `bad2`, Abbr `u4`] >>
     qexistsl_tac [`b-a`,`n2w bound`,`bb`,`i+5`,`Var rv`,`Lit (n2w bound)`] >>
     simp[Abbr `G4`, Abbr `t4`, Abbr `s4`, Abbr `s3`, Abbr `s2`,
       Abbr `s1`, update_var_def, eval_operand_def, lookup_var_def,
       for_checked_operand_taint_update, for_checked_operand_prov_removed,
       FUPDATE_LIST_THM] >> gvs[ALL_DISTINCT, FLOOKUP_UPDATE, op_taint_def]) >>
  suspend "second_assert"
QED

Resume for_entry_checked_path_ptr[second_assert]:
  `gas_path_ptr D 0 ctx fn PG G tn ee 0 G6 t6
     (OK (s6 with vs_inst_idx := 7))` by
    (rev_drule gas_path_ptr_then >> disch_then drule >>
     simp[Abbr `u4`]) >>
  `op_taint t6 (Var z2) = {}` by
    simp[Abbr `t6`, FUPDATE_LIST_THM, for_checked_operand_taint_update] >>
  `eval_operand (Var z2) (s6 with vs_inst_idx := 7) =
     SOME (bool_to_word (bool_to_word bad2 = 0w))` by
    simp[Abbr `s6`, instIdxIndepTheory.eval_op_inst_idx,
         eval_operand_def, lookup_var_update_var, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `lookup_block (s6 with vs_inst_idx := 7).vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb (s6 with vs_inst_idx := 7).vs_inst_idx =
     SOME (mk_inst (i+7) ASSERT [Var z2] [])` by
    simp[Abbr `s6`, Abbr `s5`, Abbr `u4`, Abbr `s4`, Abbr `s3`,
         Abbr `s2`, Abbr `s1`, update_var_def, get_instruction_def] >>
  drule_all for_checked_assert_prefix_ptr >>
  simp[bool_to_word_def] >> strip_tac >>
  (conj_tac >- metis_tac[]) >> strip_tac >>
  qpat_x_assum `~bad2 ==> _` mp_tac >> simp[] >> strip_tac >>
  suspend "add_jump"
QED

Resume for_entry_checked_path_ptr[add_jump]:
  qabbrev_tac `u6 = s6 with vs_inst_idx := 8` >>
  `~u6.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `!x w s. MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
     eval_operand op1 (update_var x w s) = eval_operand op1 s` by
    (rpt strip_tac >> irule for_checked_eval_operand_overwrite >> metis_tac[]) >>
  `eval_operand op1 u6 = SOME a /\
   eval_operand (Var rv) u6 = SOME (b-a)` by
    (simp[Abbr `u6`, Abbr `s6`, Abbr `s5`, Abbr `u4`, Abbr `s4`,
       Abbr `s3`, Abbr `s2`, Abbr `s1`, instIdxIndepTheory.eval_op_inst_idx] >>
     gvs[ALL_DISTINCT, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE]) >>
  `op_taint t6 op1 = {} /\ op_prov G6 op1 = NONE /\
   op_taint t6 (Var rv) = {} /\ op_prov G6 (Var rv) = NONE` by
    (simp[Abbr `G6`, Abbr `G4`, Abbr `t6`, Abbr `t4`, FUPDATE_LIST_THM,
       for_checked_operand_taint_update, for_checked_operand_prov_restrict,
       for_checked_operand_prov_removed] >>
     gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G6 t6 u6 0
     (DRESTRICT G6 (COMPL {ev})) (t6 with t_var := t6.t_var |+ (ev,{}))
     (OK (jump_to lbl (update_var ev (a+(b-a)) u6)))` by
    (irule for_checked_add_jump_ptr >> simp[] >>
     qexistsl_tac [`bb`,`i+8`,`i+9`,`op1`,`Var rv`] >> simp[] >>
     simp[Abbr `u6`, Abbr `s6`, Abbr `s5`, Abbr `u4`, Abbr `s4`,
       Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def, get_instruction_def]) >>
  suspend "finish"
QED

Resume for_entry_checked_path_ptr[finish]:
  `DRESTRICT G6 (COMPL {ev}) =
     DRESTRICT G (COMPL {cv;rv;g1;z1;g2;z2;ev})` by
    (simp[Abbr `G6`, Abbr `G4`, DRESTRICT_DRESTRICT] >>
     AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[]) >>
  `t6 with t_var := t6.t_var |+ (ev,{}) =
     tn with t_var := tn.t_var |++
       [(cv,{});(rv,{});(g1,{});(z1,{});(g2,{});(z2,{});(ev,{})]` by
    simp[Abbr `t6`, Abbr `t4`, FUPDATE_LIST_THM] >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn ee _ G6 t6 (OK u6)`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  `jump_to lbl (ee with vs_vars := (update_var ev (a+(b-a)) u6).vs_vars) =
     jump_to lbl (update_var ev (a+(b-a)) u6)` by
    simp[Abbr `u6`, Abbr `s6`, Abbr `s5`, Abbr `u4`, Abbr `s4`,
      Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def, jump_to_def] >>
  qexists_tac `(update_var ev (a+(b-a)) u6).vs_vars` >> simp[] >>
  simp[Abbr `u6`, Abbr `s6`, Abbr `s5`, Abbr `u4`, Abbr `s4`,
      Abbr `s3`, Abbr `s2`, Abbr `s1`, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE] >> gvs[ALL_DISTINCT]
QED
Finalise for_entry_checked_path_ptr

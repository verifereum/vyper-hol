Theory forPtrRangeTail
Ancestors
  forPtrCheckedFrame forPtrRangeChecked forPtrRangeLoop forPtrForcedEndpoint forPtrAllocationGhost
  stmtSimForRange stmtSimForParts stmtSimForLoop stmtSimProps
  forPtrRangeEntry forPtrRangeSource stmtSimFor localPtrsProps
  exprSimWordArgs exprSimProps stmtSimDefs loweringPosts stmtLowering
  exprLoweringProps compileEnv loweringStateRelDefs emitHelperProps loweringSlice venomInst
  ptrDiscipline ptrSafeRun list rich_list stmtSimDeclCompose valueEncoding
  exprBopSimProps gasContext
  bodyPtrDefs stmtFragPtr gasSummaryComposePtr gasOutcomeInitialObsPtr
  vyperInterpreter vyperState vyperValue vyperValueOperation
  integer_word venomState venomExecSemantics finite_map fragGasPathPtr fragExec exprSimDefs
Libs monadsyntax intLib

(* S1's source normalization is local to its range theory. *)
Theorem for_checked_range_tail_action:
  (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id stmts
        (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od) =
  if n1 <= n2 then
    if Num (n2-n1) <= bound then
      eval_for cx tyv id stmts
        (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1)))
    else raise (Error (RuntimeError "For too long"))
  else raise (Error (RuntimeError "no range"))
Proof
  simp[get_range_limits_def, lift_sum_def, check_def, assert_def,
       compatible_bound_def] >> Cases_on `n1 <= n2` >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, return_def, raise_def, assert_def] >>
  Cases_on `Num (n2-n1) <= bound` >> simp[return_def, raise_def]
QED

Theorem for_checked_range_test_words:
  is_int_type fty /\ evaluate_type tenv fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) ==>
  ((if (if is_signed_type fty then SGT else GT) = SGT then
       word_gt (i2w n1 : bytes32) (i2w n2)
    else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1) /\
  (n1 <= n2 ==>
    Num (n2-n1) < dimword (:256) /\
    (w2n (i2w n2 - i2w n1 : bytes32) > w2n (n2w bound : bytes32) <=>
       ~(Num (n2-n1) <= bound)))
Proof
  strip_tac >> drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
  disch_then (qspecl_then [`n1`,`n2`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `is_signed_type fty` >> gvs[]
QED

Theorem for_checked_runtime_error_outcome:
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tf
    (Abort Revert_abort t) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (raise (Error (RuntimeError msg))) (es,s,G,tn) Post
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`es`,`Gf`,`tf`,
                `Abort Revert_abort t`] >>
  simp[gas_marked_exec_ptr_def, raise_def, exit_result_def,
       stmt_exit_ptr_def, expr_exit_def]
QED

(* The checked entry has three semantic branches.  Keep their source/error
   correspondence here so the tail consumer only supplies checked paths and
   the existing loop outcome; no instruction semantics is reopened there. *)
Theorem for_checked_range_tail_compose:
  (~(n1 <= n2) ==>
     ?Gf tf t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tf
       (Abort Revert_abort t)) /\
  (n1 <= n2 /\ ~(Num (n2-n1) <= bound) ==>
     ?Gf tf t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tf
       (Abort Revert_abort t)) /\
  (n1 <= n2 /\ Num (n2-n1) <= bound ==>
     ?Gc tc cc.
       gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gc tc (OK cc) /\
       gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
         (eval_for cx tyv id stmts
           (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))))
         (es,cc,Gc,tc) Post
         (\res ee gt r. !tail.
           stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,s,G,tn) Post
    (\res ee gt r. !tail.
      stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rewrite_tac[for_checked_range_tail_action] >>
  Cases_on `n1 <= n2`
  >- (Cases_on `Num (n2-n1) <= bound` >> gvs[]
      >- (irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
          qexists_tac `0` >> simp[]) >>
      irule for_checked_runtime_error_outcome >> goal_assum (drule_at Any)) >>
  gvs[] >> irule for_checked_runtime_error_outcome >> goal_assum (drule_at Any)
QED

(* Consumer-facing checked entry: the continuation sees only the final map
   and its frame.  Arithmetic failure and checked aborts stay behind this
   boundary, while the continuation can use for_checked_entry_setup. *)
Theorem for_checked_range_entry_outcome_ptr:
  lookup_block ee.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst i ASSIGN [op1] [cv];
     mk_inst (i+1) SUB [op2;op1] [rv];
     mk_inst (i+2) (if is_signed_type fty then SGT else GT) [op1;op2] [g1];
     mk_inst (i+3) ISZERO [Var g1] [z1];
     mk_inst (i+4) ASSERT [Var z1] [];
     mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
     mk_inst (i+6) ISZERO [Var g2] [z2];
     mk_inst (i+7) ASSERT [Var z2] [];
     mk_inst (i+8) ADD [op1;Var rv] [ev];
     mk_inst (i+9) JMP [Label lbl] []] /\
  ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand op1 ee = SOME (i2w n1) /\
  eval_operand op2 ee = SOME (i2w n2) /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) /\
  (!vs. n1 <= n2 /\ Num (n2-n1) <= bound /\
     lookup_var cv (ee with vs_vars := vs) = SOME (i2w n1) /\
     lookup_var ev (ee with vs_vars := vs) = SOME (i2w n2) /\
     (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
       lookup_var x (ee with vs_vars := vs) = lookup_var x ee) ==>
     gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
       (eval_for cx tyv id stmts
         (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))))
       (es,jump_to lbl (ee with vs_vars := vs),
        DRESTRICT G (COMPL {cv;rv;g1;z1;g2;z2;ev}),
        tn with t_var := tn.t_var |++
          [(cv,{});(rv,{});(g1,{});(z1,{});(g2,{});(z2,{});(ev,{})]) Post
       (\res ee gt r. !tail.
         stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,ee,G,tn) Post
    (\res ee gt r. !tail.
      stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL for_checked_range_test_words)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_at (Pat `bb.bb_instructions = _`) for_entry_checked_path_ptr >>
  disch_then (drule_at (Pat `eval_operand op1 ee = _`)) >>
  disch_then (drule_at (Pat `eval_operand op2 ee = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (mp_tac o Q.INST [`D` |-> `cx_dead cx`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> Cases_on `is_signed_type fty` >> gvs[] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "compose"
QED

Resume for_checked_range_entry_outcome_ptr[compose]:
  irule for_checked_range_tail_compose >> rpt conj_tac
  >- (strip_tac >>
      qpat_x_assum `_ \/ _ ==> _` irule >> disj1_tac >>
      simp[integerTheory.INT_NOT_LT, GSYM integerTheory.INT_NOT_LE])
  >- (strip_tac >> qpat_x_assum `_ \/ _ ==> _` irule >>
      disj2_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `~_ /\ ~_ ==> ?vs. _` mp_tac >>
  simp[integerTheory.INT_NOT_LT, wordsTheory.WORD_SUB_ADD2] >>
  strip_tac >>
  goal_assum (drule_at Any) >> first_x_assum irule >> simp[]
QED
Finalise for_checked_range_entry_outcome_ptr

Theorem for_range_checked_tail_outcome_ptr:
  for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 st = ((),sf) /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ ret_pc_ok cenv st s /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
  32 <= type_memory_bytes cenv fty /\
  type_memory_bytes cenv fty < dimword (:256) /\
  bound < dimword (:256) /\ cenv.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
     cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  eval_operand op1 s = SOME (i2w n1) /\
  eval_operand op2 s = SOME (i2w n2) /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  (!l. op1 <> Label l /\ op2 <> Label l) /\
  (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x) /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  P (es with gas_obs := []) /\
  (!c st1 ex inc ei j.
     declare_local cenv id fty st = (c,st1) /\
     n1 <= n2 /\ Num (n2-n1) <= bound /\
     P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2-n1) ==>
     stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ c
       (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
       (ei with <| scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv;
           value := IntV (n1 + &j); popped := []|>)) :: ei.scopes;
         gas_obs := [] |>)) /\
  (!ei j gs r2 es2 sc rest.
     n1 <= n2 /\ Num (n2-n1) <= bound /\
     P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2-n1) /\
     eval_stmts cx stmts (ei with <| scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tyv;
         value := IntV (n1 + &j); popped := []|>)) :: ei.scopes;
       gas_obs := gs |>) = (r2,es2) /\
     (r2 = INL () \/ r2 = INR ContinueException) /\ es2.scopes = sc :: rest ==>
     P (es2 with scopes := rest)) /\
  gas_admissible
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (stmt_res_ok lctx) es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,s,G,tn)
    (\res ee Gf tf t.
       res = INL () /\ stmt_lands lctx sf res t /\ ~t.vs_halted /\
       ~block_is_terminated sf /\ stmt_state_rel ctx func cenv cx ee t /\
       ghost_inv d cenv cx ee Gf tf t /\
       (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
          lookup_var x t = SOME w) /\
       (!x. not_fresh_at st x ==> FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x)))
    (\res ee gt r. !tail.
       stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `cs_extends st st` by simp[cs_extends_refl] >>
  drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`)
    for_range_checked_parts >>
  disch_then (qspecl_then [`st`,`func`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then
    [`p`,`cv`,`rv`,`g1`,`z1`,`g2`,`z2`,`ev`,`dv`,`entry_lbl`,
     `cond_lbl`,`body_lbl`,`incr_lbl`,`exit_lbl`,`bc`,`sb0`,`sb1`,`sj`,`nv`]
    strip_assume_tac) >>
  drule_all declare_local_ptr >> strip_tac >> suspend "layout"
QED

Resume for_range_checked_tail_outcome_ptr[layout]:
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `!q. not_fresh_at st q ==>
     ~MEM q [p;cv;rv;g1;z1;g2;z2;ev;dv;nv]` by
    (rw[not_fresh_at_def] >> fs[] >>
     qpat_x_assum `sb0.cs_next_var <= sb1.cs_next_var` mp_tac >> fs[]) >>
  `!x. MEM x [p;cv;rv;g1;z1;g2;z2;ev;dv;nv] ==>
     !scs. not_local_ptr cenv scs x` by
    (rpt strip_tac >> fs[] >>
     irule reserved_fresh_not_local >> qexists_tac `st` >> fs[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `st with cs_next_var := st.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `type_memory_size tyv = 32` by
    (Cases_on `fty` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def]) >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block st.cs_current_bb _ = _`
       (mp_then Any mp_tac lookup_block_fn_insts) >> simp[Abbr `A`]) >>
  `for_code func cenv bc ty stmts id tyv p sz A cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl (st.cs_next_id + 12)
      (st.cs_next_id + 13) (st.cs_next_id + 14) bbb sj.cs_next_id
      (sj.cs_next_id + 1) (sj.cs_next_id + 2) sb0 sb1 sj` by
    (simp[for_code_def, Abbr `A`] >>
     conj_tac >- simp[block_is_terminated_def, mk_inst_def, is_terminator_def] >>
     simp[not_fresh_at_def] >> metis_tac[]) >>
  suspend "allocation"
QED

Resume for_range_checked_tail_outcome_ptr[allocation]:
  `get_instruction
    <|bb_label := st.cs_current_bb; bb_instructions :=
      st.cs_current_insts ++ [A; mk_inst (st.cs_next_id+1) JMP [Label entry_lbl] []]|>
    s.vs_inst_idx = SOME A` by simp[get_instruction_def, EL_APPEND_EQN] >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var p) q)` by
    (rpt strip_tac >> metis_tac[listTheory.MEM]) >>
  `?u a.
    step_inst_base A s = OK u /\
    stmt_state_rel ctx func cenv cx es u /\ lookup_var p u = SOME a /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (w2n a,sz) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
    ~u.vs_halted /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
      (step_prov PG G A u) (step_taint A s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers (step_prov PG G A u) (step_taint A s u tn) p u sz /\
    (!name lo z. local_region cenv es.scopes s name lo z ==>
      regions_disjoint (w2n a) sz lo z) /\
    (!x. x <> p ==> lookup_var x u = lookup_var x s /\
      FLOOKUP (step_prov PG G A u) x = FLOOKUP G x /\
      op_taint (step_taint A s u tn) (Var x) = op_taint tn (Var x))` by
    (simp[NoAsms, Abbr `A`] >>
     irule for_range_alloca_entry_path_ptr >> simp[] >> metis_tac[listTheory.MEM]) >>
  `ghost_inv d cenv cx es (step_prov PG G A u) (step_taint A s u tn) u` by
    (simp[Abbr `A`] >> irule for_alloca_ghost_inv >> simp[] >> metis_tac[listTheory.MEM]) >>
  qabbrev_tac `Ga = step_prov PG G A u` >>
  qabbrev_tac `ta = step_taint A s u tn` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG Ga ta
    (u with vs_inst_idx := SUC s.vs_inst_idx) 0 Ga ta
    (OK (jump_to entry_lbl u))` by
    (simp[NoAsms, jump_to_def] >> irule (SRULE [jump_to_def] (Q.INST
       [`s` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`]
       (SPEC_ALL for_range_jump_path_ptr))) >>
     simp[get_instruction_def, EL_APPEND_EQN, jump_to_def] >> metis_tac[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Ga ta
    (OK (jump_to entry_lbl u))` by (drule_all gas_path_ptr_then >> simp[]) >>
  suspend "checked_entry"
QED

Resume for_range_checked_tail_outcome_ptr[checked_entry]:
  qabbrev_tac `ee = jump_to entry_lbl u` >>
  `!x. op1 = Var x \/ op2 = Var x ==> x <> p /\
    ~MEM x [cv;rv;g1;z1;g2;z2;ev]` by metis_tac[listTheory.MEM] >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
     lookup_var x u = SOME w` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!q. not_fresh_at st q ==> ~MEM q _`
       (drule_then assume_tac) >>
     qpat_assum `!x. x <> p ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >> fs[]) >>
  `!op. eval_operand op ee = eval_operand op u` by
    (Cases >> simp[Abbr `ee`, eval_operand_def, jump_to_def, lookup_var_def]) >>
  `eval_operand op1 ee = SOME (i2w n1) /\
   eval_operand op2 ee = SOME (i2w n2)` by
    (simp[] >> conj_tac >>
     irule eval_operand_frame >> (conj_tac >- simp[]) >>
     qexistsl_tac [`st`,`s`] >> simp[] >>
     rpt strip_tac >> qpat_x_assum `!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x`
       irule >> simp[]) >>
  `!op. (!x. op = Var x ==> x <> p) ==>
     op_taint ta op = op_taint tn op /\ op_prov Ga op = op_prov G op` by
    (qpat_x_assum `!x. x <> p ==> lookup_var x u = _ /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> Cases >>
     simp[op_prov_def, op_taint_def] >> strip_tac >>
     first_x_assum drule >> simp[op_taint_def]) >>
  `op_taint ta op1 = {} /\ op_taint ta op2 = {} /\
   op_prov Ga op1 = NONE /\ op_prov Ga op2 = NONE` by
    (qpat_x_assum `!op. (!x. op = Var x ==> x <> p) ==> _` mp_tac >>
     qpat_x_assum `!x. op1 = Var x \/ op2 = Var x ==> x <> p /\ _` mp_tac >>
     qpat_x_assum `op_taint tn op1 = {}` mp_tac >>
     qpat_x_assum `op_taint tn op2 = {}` mp_tac >>
     qpat_x_assum `op_prov G op1 = NONE` mp_tac >>
     qpat_x_assum `op_prov G op2 = NONE` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  irule gas_outcome_ptr_prefix >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ s _ _ _ _`)) >>
  `ee.vs_current_bb = entry_lbl` by simp[Abbr `ee`, jump_to_def] >>
  pop_assum (fn th =>
    qpat_assum `lookup_block _ _ = SOME
      <|bb_label := _; bb_instructions := mk_inst _ ASSIGN _ _ :: _|>`
      (mp_then Any mp_tac
        (SRULE [th, GSYM arithmeticTheory.ADD_ASSOC]
          (Q.INST [`ee` |-> `ee`]
            (SPEC_ALL for_checked_range_entry_outcome_ptr))))) >>
  disch_then irule >>
  simp[GSYM arithmeticTheory.ADD_ASSOC, mk_inst_def] >>
  suspend "entry_premises"
QED

Resume for_range_checked_tail_outcome_ptr[entry_premises]:
  conj_tac >- simp[Abbr `ee`, jump_to_def] >>
  conj_tac >- simp[Abbr `ee`, jump_to_def] >>
  qexists_tac `fty` >> simp[] >>
  (reverse conj_tac >-
    (qpat_x_assum `!x. op1 = Var x \/ op2 = Var x ==> x <> p /\ _` mp_tac >>
     qpat_x_assum `eval_operand op1 ee = SOME _` mp_tac >>
     qpat_x_assum `eval_operand op2 ee = SOME _` mp_tac >>
     simp[] >> rpt (pop_assum kall_tac) >> metis_tac[])) >>
  gen_tac >> strip_tac >> suspend "loop_setup"
QED

Resume for_range_checked_tail_outcome_ptr[loop_setup]:
  qpat_assum `cv = _` (fn th =>
    qpat_x_assum `lookup_var _ (ee with vs_vars := vs) = SOME (i2w n1)`
      (assume_tac o ONCE_REWRITE_RULE [SYM th])) >>
  qpat_assum `ev = _` (fn th =>
    qpat_x_assum `lookup_var _ (ee with vs_vars := vs) = SOME (i2w n2)`
      (assume_tac o ONCE_REWRITE_RULE [SYM th])) >>
  map_every (fn q => qpat_assum q (fn th =>
    once_rewrite_tac [SYM th] >>
    qpat_x_assum `!x. _ ==> lookup_var x (ee with vs_vars := vs) = _`
      (assume_tac o ONCE_REWRITE_RULE [SYM th])))
    [`cv = _`,`rv = _`,`g1 = _`,`z1 = _`,`g2 = _`,`z2 = _`,`ev = _`] >>
  qpat_assum `cond_lbl = _` (fn th => once_rewrite_tac [SYM th]) >>
  qabbrev_tac `cc = jump_to cond_lbl (ee with vs_vars := vs)` >>
  qabbrev_tac `Gc = DRESTRICT Ga (COMPL {cv;rv;g1;z1;g2;z2;ev})` >>
  qabbrev_tac `tc = ta with t_var := ta.t_var |++
    [(cv,{});(rv,{});(g1,{});(z1,{});(g2,{});(z2,{});(ev,{})]` >>
  suspend "entry_setup"
QED

Resume for_range_checked_tail_outcome_ptr[entry_setup]:
  `ghost_inv d cenv cx es Ga ta ee /\
   stmt_state_rel ctx func cenv cx es ee /\ ptr_covers Ga ta p ee sz` by
    (conj_tac >- simp[Abbr `ee`, jump_to_def,
       stmtFragPtrTheory.ghost_inv_jump_to] >>
     conj_tac >- simp[Abbr `ee`, stmt_state_rel_jump_to] >>
     qpat_x_assum `ptr_covers Ga ta p u sz` mp_tac >>
     simp[NoAsms, Abbr `ee`, ptr_covers_def, jump_to_def, lookup_var_def]) >>
  `~MEM p [cv;rv;g1;z1;g2;z2;ev]` by (fs[] >> rw[] >> fs[]) >>
  `!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
    not_local_ptr cenv es.scopes x /\ cenv.ce_imm_alloca <> SOME (Var x) /\
    (!q. cenv.ce_return_buf <> SOME (PtrVar (Var x) q))` by
    (rpt strip_tac
     >- (qpat_assum `!x. MEM x [p;cv;rv;g1;z1;g2;z2;ev;dv;nv] ==> _`
           irule >> fs[])
     >- (drule_all local_ptrs_reserved_imm_base >>
         qpat_x_assum `!q. not_fresh_at st q ==> ~MEM q _` mp_tac >>
         qpat_x_assum `MEM x [cv;rv;g1;z1;g2;z2;ev]` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!x q. cenv.ce_return_buf = _ ==> _` drule >>
     qpat_x_assum `!q. not_fresh_at st q ==> ~MEM q _` mp_tac >>
     qpat_x_assum `MEM x [cv;rv;g1;z1;g2;z2;ev]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ ee`) for_checked_entry_setup >>
  disch_then (drule_at (Pat `stmt_state_rel _ func _ _ _ ee`)) >>
  disch_then (mp_tac o Q.INST
    [`outputs` |-> `[cv;rv;g1;z1;g2;z2;ev]`, `lbl` |-> `cond_lbl`,
     `sf` |-> `cc`, `Gf` |-> `Gc`, `tf` |-> `tc`] o SPEC_ALL) >>
  (impl_tac >- simp[Abbr `cc`, Abbr `Gc`, Abbr `tc`]) >>
  strip_tac >> suspend "entry_frames"
QED

Resume for_range_checked_tail_outcome_ptr[entry_frames]:
  `lookup_var cv cc = SOME (i2w n1) /\ lookup_var ev cc = SOME (i2w n2)` by
    (simp[NoAsms, Abbr `cc`, jump_to_def, lookup_var_def] >>
     fs[lookup_var_def]) >>
  `lookup_var p cc = SOME a /\
   FLOOKUP cc.vs_allocas st.cs_next_id = SOME (w2n a,sz) /\ ~cc.vs_halted` by
    (qpat_assum `!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==> lookup_var x cc = _ /\ _`
       (qspec_then `p` mp_tac) >>
     simp[Abbr `ee`, jump_to_def, lookup_var_def] >> gvs[lookup_var_def]) >>
  `(!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x cc = SOME w) /\
   (!x. not_fresh_at st x ==> FLOOKUP Gc x = FLOOKUP G x /\
      op_taint tc (Var x) = op_taint tn (Var x))` by
    (qpat_x_assum `!q. not_fresh_at st q ==> ~MEM q _` mp_tac >>
     qpat_x_assum `!x. x <> p ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_x_assum `!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==> lookup_var x cc = _ /\ _` mp_tac >>
     simp[NoAsms, Abbr `ee`, jump_to_def, lookup_var_def] >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `!name lo z. local_region cenv es.scopes cc name lo z ==>
    regions_disjoint (w2n a) sz lo z` by
    (rpt strip_tac >>
     `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
     `local_region cenv es.scopes s name lo z` by
       (irule local_region_frame >> metis_tac[]) >> metis_tac[]) >>
  suspend "loop"
QED

Resume for_range_checked_tail_outcome_ptr[loop]:
  qabbrev_tac `vals = GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))` >>
  qabbrev_tac `Inv = \j ei gf tf t.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ j <= Num (n2-n1) /\
    t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx ei t /\ ghost_inv d cenv cx ei gf tf t /\
    lookup_var cv t = SOME (i2w (n1 + &j)) /\
    lookup_var ev t = SOME (i2w n2) /\ lookup_var p t = SOME a /\
    FLOOKUP gf cv = NONE /\ FLOOKUP gf ev = NONE /\
    op_taint tf (Var cv) = {} /\ op_taint tf (Var ev) = {} /\
    ptr_covers gf tf p t sz /\
    FLOOKUP t.vs_allocas A.inst_id = SOME (w2n a,sz) /\
    (!name lo z. local_region cenv ei.scopes t name lo z ==>
      regions_disjoint (w2n a) sz lo z) /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` >>
  qabbrev_tac `Done = \ei gf tf t.
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx ei t /\ ghost_inv d cenv cx ei gf tf t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!x. not_fresh_at st x ==> FLOOKUP gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` >>
  `Inv 0 (es with gas_obs := []) Gc tc cc` by
    (simp[Abbr `Inv`, Abbr `A`, stmt_state_rel_gas_obs, ghost_inv_gas_obs,
       mk_inst_def] >>
     qpat_assum `!x. MEM x [cv;rv;g1;z1;g2;z2;ev] ==> FLOOKUP Gc x = _ /\ _`
       mp_tac >> simp[] >> metis_tac[]) >>
  suspend "loop_outcome"
QED

Resume for_range_checked_tail_outcome_ptr[loop_outcome]:
  drule (Q.INST [`P` |-> `\ei. P ei /\ lookup_scopes id ei.scopes = NONE`]
    (SPEC_ALL for_range_loop_ptr)) >>
  disch_then (drule_at (Pat `Inv _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ret_pc_ok cenv st s`)) >>
  disch_then (mp_tac o Q.INST
    [`G0` |-> `G`, `tn0` |-> `tn`, `vs` |-> `vals`, `Done` |-> `Done`] o SPEC_ALL) >>
  (impl_tac >- suspend "loop_static") >>
  simp[DROP_0] >> strip_tac >> suspend "finish"
QED

Resume for_range_checked_tail_outcome_ptr[loop_static]:
  fs[] >> simp[DROP_0] >> reverse conj_tac
  >- (qpat_x_assum `gas_admissible _ _ es` mp_tac >>
      simp[for_checked_range_tail_action, gas_admissible_gas_obs, Abbr `vals`]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!ex inc ei j. _` irule >> fs[Abbr `vals`]) >>
  conj_tac >- simp[Abbr `Inv`, SF CONJ_ss] >>
  conj_tac
  >- (simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >>
      drule for_body_outer_preserves >>
      disch_then (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [] >> rpt strip_tac >> irule not_local_ptr_name_update >>
      qexistsl_tac [`cenv`,`id`] >> simp[] >>
      qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  simp[Abbr `vals`] >> conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  rpt gen_tac >> disch_tac >> simp[] >> irule i2w_counter_ne >> simp[]
QED

Resume for_range_checked_tail_outcome_ptr[finish]:
  fs[gas_outcome_ptr_initial_obs] >>
  drule gas_outcome_ptr_conseq >> disch_then irule >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      pop_assum mp_tac >>
      simp[NoAsms, Abbr `Done`] >>
      qpat_x_assum `sf.cs_current_bb = _` mp_tac >>
      qpat_x_assum `sf.cs_current_insts = []` mp_tac >>
      rpt (pop_assum kall_tac) >>
      rpt strip_tac >> gvs[stmt_lands_def, block_is_terminated_def]) >>
  rpt gen_tac >> strip_tac >> pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]
QED
Finalise for_range_checked_tail_outcome_ptr

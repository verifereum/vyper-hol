(*
 * Statement simulation: For over a range with constant ends (#637)
 *
 * TOP-LEVEL:
 *   compile_for_range_frag            — For over a range whose ends lower
 *                                       to words without code, under a
 *                                       loop invariant
 *   compile_for_range_lit_frag        — the same for literal ends
 *   compile_for_range_lit_frag_simple — the same with the body's judgment
 *                                       at every source state
 *)

Theory stmtSimFor
Ancestors
  stmtSimProps
  stmtSimDefs
  loweringPosts
   stmtSimForParts stmtSimForLoop stmtSimDeclCompose
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  gasOutcome gasContext stmtSimForRounds
  fragGasSeq fragGasPath fragGasMode gasCount stmtSimDeclPath
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* ===== For over a range with constant ends ===== *)

Theorem eval_stmt_for_range_lit_action[local]:
  evaluate_type (get_tenv cx) fty = SOME tyv /\
  n1 <= n2 /\ Num (n2 - n1) <= bound ==>
  eval_stmt cx
    (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
       bound stmts) =
  eval_for cx tyv id stmts
    (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM,
       lift_option_type_def, lift_option_def, return_def, raise_def,
       eval_iterator_range_lit, check_def, assert_def, compatible_bound_def]
QED

Theorem for_entry_zero_path[local]:
  !ctx func s cv ev a b lbl cond_lbl i1 i2 i3.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl; bb_instructions :=
        [mk_inst i1 ASSIGN [Lit a] [cv];
         mk_inst i2 ADD [Lit a; Lit b] [ev];
         mk_inst i3 JMP [Label cond_lbl] []] |> /\
    s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    gas_marked_path F ctx func s 0
      (OK (jump_to cond_lbl (update_var ev (a + b) (update_var cv a s))))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `code = [mk_inst i1 ASSIGN [Lit a] [cv];
                       mk_inst i2 ADD [Lit a; Lit b] [ev]]` >>
  qabbrev_tac `t = update_var ev (a + b) (update_var cv a s)` >>
  `run_inst_seq code s = OK t` by
    (`step_inst_base (mk_inst i2 ADD [Lit a; Lit b] [ev])
        (update_var cv a s) = OK t` by
       (simp[Abbr `t`] >> irule step_ADD >> simp[eval_operand_def]) >>
     `step_inst_base (mk_inst i1 ASSIGN [Lit a] [cv]) s =
        OK (update_var cv a s)` by
       simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
     simp[Abbr `code`, run_inst_seq_def]) >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`,
    `<| bb_label := lbl; bb_instructions := code ++
        [mk_inst i3 JMP [Label cond_lbl] []] |>`] mp_tac) >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >> strip_tac >>
  `gas_path_edge ctx func (t with vs_inst_idx := 2) 0
     (OK (jump_to cond_lbl t))` by
    (simp[gas_path_edge_def, Abbr `t`, update_var_def] >>
     qexists_tac `0` >>
     simp[get_instruction_def, step_inst_non_invoke, mk_inst_def,
          gas_count_step_def, is_terminator_def, step_jmp_behavior,
          jump_to_def, update_var_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `cond_lbl` >> simp[]) >>
  `gas_path ctx func (jump_to cond_lbl t) 0 (OK (jump_to cond_lbl t))` by
    (irule (cj 1 gas_path_rules) >> simp[Abbr `t`, jump_to_def, update_var_def]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path _ _ s _ _` mp_tac >>
  disch_then (mp_then Any mp_tac gas_path_then) >>
  disch_then drule >> simp[gas_marked_path_def, Abbr `t`]
QED

Theorem for_alloca_state[local]:
  !ctx func cenv cx es s A p sz.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM A (fn_insts func) /\ A.inst_opcode = ALLOCA /\
    A.inst_operands = [Lit (n2w sz)] /\ A.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\ sz < dimword (:256) /\ ~s.vs_halted ==>
    ?s1 w.
      step_inst_base A s = OK s1 /\
      stmt_state_rel ctx func cenv cx es s1 /\
      lookup_var p s1 = SOME w /\
      FLOOKUP s1.vs_allocas A.inst_id = SOME (w2n w, sz) /\
      s1.vs_current_bb = s.vs_current_bb /\
      s1.vs_inst_idx = s.vs_inst_idx /\ ~s1.vs_halted /\
      (!x. x <> p ==> lookup_var x s1 = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                   FLOOKUP s1.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> strip_tac >>
  `?s1. exec_alloca A s (n2w sz : bytes32) = OK s1` by
    (Cases_on `FLOOKUP s.vs_allocas A.inst_id`
     >- simp[exec_alloca_def] >>
     rename1 `FLOOKUP s.vs_allocas A.inst_id = SOME entry` >>
     PairCases_on `entry` >> simp[exec_alloca_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  drule_all exec_alloca_frames >> strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_inst_idx = s.vs_inst_idx /\ ~s1.vs_halted` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def, AllCaseEqs()]) >>
  qexistsl_tac [`s1`, `w`] >> simp[] >>
  simp[step_inst_base_def]
QED

Theorem reserved_fresh_not_local:
  !cenv st n scs.
    local_ptrs_reserved cenv st /\ st.cs_next_var <= n ==>
    not_local_ptr cenv scs (STRING #"%" (toString n))
Proof
  metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_fresh]
QED

Theorem for_reserved_index[local]:
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= n ==>
  (!scs. not_local_ptr cenv scs (STRING #"%" (toString n))) /\
  (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString n))
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
  simp[not_fresh_at_def]
QED

Theorem for_condition_state[local]:
  !ctx func cenv cx es sa s0 s1 p w aid sz cv ev a b entry cond cc.
    cc = jump_to cond (update_var ev b (update_var cv a (jump_to entry s1))) /\
    stmt_state_rel ctx func cenv cx es s1 /\ ~s1.vs_halted /\
    not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes ev /\
    cv <> ev /\ p <> cv /\ p <> ev /\ lookup_var p s1 = SOME w /\
    FLOOKUP s1.vs_allocas aid = SOME (w2n w, sz) /\
    (!x. not_fresh_at sa x ==> x <> p /\ x <> cv /\ x <> ev) /\
    (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
    (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
             FLOOKUP s1.vs_allocas aid = SOME v) /\
    ret_pc_ok cenv sa s0 ==>
    stmt_state_rel ctx func cenv cx es cc /\ ret_pc_ok cenv sa cc /\
    cc.vs_current_bb = cond /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    lookup_var cv cc = SOME a /\ lookup_var ev cc = SOME b /\
    lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas aid = SOME (w2n w, sz) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
           lookup_var x cc = SOME v) /\
    (!aid v. FLOOKUP s0.vs_allocas aid = SOME v ==>
             FLOOKUP cc.vs_allocas aid = SOME v)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (simp[stmt_state_rel_jump_to] >> irule stmt_state_rel_update_var >>
     simp[] >> irule stmt_state_rel_update_var >>
     simp[stmt_state_rel_jump_to]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x cc = SOME v` by
    (rpt strip_tac >>
     `x <> p /\ x <> cv /\ x <> ev` by metis_tac[] >>
     simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[lookup_var_def]) >>
  `ret_pc_ok cenv sa cc` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

(* For over a range whose ends are source integer literals: the loop
   variable's ALLOCA, the
   entry block, then the loop from the first counter value; on a normal
   finish the code ends at the start of the exit block.  The body's
   judgment is assumed for the environment declare_local gives, at the
   iteration states over source states where the invariant P holds; P
   holds at the start and again after each iteration that goes on.  P sees
   the state and not the counter, so this composes with an induction whose
   hypothesis holds at every state satisfying an invariant, not with one
   over the evaluator's recursion, which gives the body only at the visited
   (state, counter) pairs.  Only for n1 <= n2 (not the source's "no range"
   error), a loop variable of one word, and ce_alloca_locals, which the
   lowering sets for external functions only. *)
Theorem compile_for_range_frag:
  !P ctx func cx lctx RetQ cenv ty id fty e1 n1 e2 n2 bound stmts es tyv.
    eval_expr cx e1 es = (INL (Value (IntV n1)), es) /\
    eval_expr cx e2 es = (INL (Value (IntV n2)), es) /\
    (!s. lower_value compile_expr cenv fty e1 s = (Lit (i2w n1), s)) /\
    (!s. lower_value compile_expr cenv fty e2 s = (Lit (i2w n2), s)) /\
    (?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P (es with gas_obs := []) /\
    (!st0 c st1 ex inc ei j.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  gvs[eval_expr_int_lit] >>
  rewrite_tac[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all eval_stmt_for_range_lit_action >> disch_then (fn th => fs[th]) >>
  gvs[lower_value_int_lit] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty
    (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
      bound stmts) sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = ((), sb)` >>
  drule compile_for_range_lit_parts >>
  disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  suspend "entry"
QED

Resume compile_for_range_frag[entry]:
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
   cv <> ev /\ cv <> p /\ ev <> p` by (fs[] >> rw[] >> fs[]) >>
  `!n. sa.cs_next_var <= n ==>
    (!scs. not_local_ptr cenv scs (STRING #"%" (toString n))) /\
    (!x. not_fresh_at sa x ==> x <> STRING #"%" (toString n))` by
    (gen_tac >> strip_tac >> irule for_reserved_index >> simp[]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs ev) /\
   (!scs. not_local_ptr cenv scs dv) /\ (!scs. not_local_ptr cenv scs nv) /\
   (!scs. not_local_ptr cenv scs p)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `ev = _` SUBST1_TAC >>
     qpat_assum `dv = _` SUBST1_TAC >> qpat_assum `nv = _` SUBST1_TAC >>
     qpat_assum `p = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `sa` >> fs[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb _ = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] lookup_block_fn_insts)) >> simp[]) >>
  `for_code func cenv bc ty stmts id tyv p sz A cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl (sa.cs_next_id + 5)
      (sa.cs_next_id + 6) (sa.cs_next_id + 7) bbb sj.cs_next_id
      (sj.cs_next_id + 1) (sj.cs_next_id + 2) sb0 sb1 sj` by
    (simp[for_code_def, Abbr `A`] >>
     conj_tac >- simp[block_is_terminated_def, mk_inst_def, is_terminator_def] >>
     simp[not_fresh_at_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> x <> p /\ x <> cv /\ x <> ev /\ x <> dv /\ x <> nv` by
    (rw[not_fresh_at_def] >> fs[] >>
     qpat_x_assum `sb0.cs_next_var <= sb1.cs_next_var` mp_tac >> fs[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >> irule not_local_ptr_name_update >>
     qexistsl_tac [`cenv`, `id`] >> simp[] >>
     qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `evaluate_type _ _ = _` kall_tac >>
  qpat_x_assum `lookup_block cond_lbl _ = _` kall_tac >>
  qpat_x_assum `lookup_block body_lbl _ = _` kall_tac >>
  qpat_x_assum `get_instruction bbb _ = _` kall_tac >>
  qpat_x_assum `lookup_block incr_lbl _ = _` kall_tac >>
  qpat_x_assum `~block_is_terminated sb1 ==> _` kall_tac >>
  suspend "state"
QED

Resume compile_for_range_frag[state]:
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = sa.cs_next_id` by simp[Abbr `A`, mk_inst_def] >>
  `not_local_ptr cenv es.scopes p` by simp[] >>
  drule_all for_alloca_state >> strip_tac >>
  qabbrev_tac `cc = jump_to cond_lbl (update_var ev (i2w n2)
    (update_var cv (i2w n1) (jump_to entry_lbl s1)))` >>
  `gas_marked_path F ctx func s0 0 (OK (jump_to entry_lbl s1))` by
    (irule for_start_zero_path >> simp[] >>
     qexists_tac `sa.cs_next_id + 1` >> simp[]) >>
  `gas_marked_path F ctx func (jump_to entry_lbl s1) 0 (OK cc)` by
    (drule for_entry_zero_path >>
     disch_then (qspecl_then [`ctx`, `jump_to entry_lbl s1`] mp_tac) >>
     simp[jump_to_def, Abbr `cc`, wordsTheory.WORD_SUB_ADD2]) >>
  `cc = jump_to cond_lbl (update_var ev (i2w n2)
     (update_var cv (i2w n1) (jump_to entry_lbl s1)))` by simp[Abbr `cc`] >>
  drule for_condition_state >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `sa`, `s0`,
                          `p`, `w`, `A.inst_id`, `sz`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  suspend "loop"
QED

Resume compile_for_range_frag[loop]:
  `!ei j. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
     stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
       (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
       (ei with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
          value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)` by
    (rpt strip_tac >> qpat_x_assum `!st0 c st1 ex inc ei j. _` irule >>
     asm_rewrite_tac [] >>
     qexistsl_tac [`sa`, `sa with cs_next_var := sa.cs_next_var + 1`] >>
     first_assum ACCEPT_TAC) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
     (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1))))
     (es,cc)
     (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
       s.vs_inst_idx = 0 /\ ~s.vs_halted /\ stmt_state_rel ctx func cenv cx ee s /\
       (!x v. not_fresh_at sa x /\ lookup_var x cc = SOME v ==> lookup_var x s = SOME v) /\
       (!a b. FLOOKUP cc.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b) /\
       (!frame_start. frame_start.cs_next_id <= A.inst_id /\
          frame_start.cs_next_id <= sb0.cs_next_id ==>
          alloca_frame cenv es frame_start cc cenv ee s))
     (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (qpat_x_assum `bc with <| ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _ |> = cenv` kall_tac >>
     qpat_x_assum `cc = _` kall_tac >>
     qpat_x_assum `Abbrev (cc = _)` kall_tac >>
     irule (SRULE [] (Q.INST [`k` |-> `0`] (SPEC_ALL for_loop_alloca))) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qpat_x_assum `sb0.cs_next_var = _` (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qexistsl_tac [`lctx`, `Num (n2 - n1)`] >>
                  simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qhdtm_assum `for_code` (irule_at Any) >>
     qexistsl_tac [`w`, `P`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (gen_tac >> disch_tac >>
       qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >>
       disch_then strip_assume_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume compile_for_range_frag[finish]:
  irule gas_outcome_zero_prefix >> qexists_tac `cc` >>
  conj_tac >-
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_marked_path_then))) >>
     qexists_tac `jump_to entry_lbl s1` >>
     simp[NoAsms] >> conj_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `gas_outcome` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- suspend "post" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >> first_assum ACCEPT_TAC
QED

Resume compile_for_range_frag[post]:
  qexists_tac `marks` >> disj1_tac >>
  qhdtm_x_assum `gas_summary_at` mp_tac >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee` (qx_choose_then `r` strip_assume_tac)))
  >- suspend "post_normal" >>
  qexistsl_tac [`res`, `ee`, `r`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_for_range_frag[post_normal]:
  `exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (qpat_x_assum `step_inst_base A s0 = _` mp_tac >>
     simp[step_inst_base_def] >> disch_then ACCEPT_TAC) >>
  `s1.vs_memory = s0.vs_memory` by
    (drule stmtSimDeclPathTheory.exec_alloca_memory >> simp[]) >>
  `cc.vs_memory = s0.vs_memory` by
    (qpat_assum `cc = _` SUBST1_TAC >>
     simp[NoAsms, jump_to_def, update_var_def] >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `cc = _` kall_tac >>
  qpat_x_assum `Abbrev (cc = _)` kall_tac >>
  qexistsl_tac [`res`, `ee`, `r`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj1_tac >> qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `(\res ee s. _) res _ t` mp_tac >>
  simp_tac bool_ss [boolTheory.FORALL_AND_THM] >> strip_tac >>
  rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  simp_tac bool_ss [stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac >- (disj1_tac >> conj_tac >> asm_rewrite_tac[listTheory.LENGTH]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[block_is_terminated_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!x v. not_fresh_at sa x /\ lookup_var x cc = _ ==> _` irule >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `!x v. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _` irule >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!a b. FLOOKUP cc.vs_allocas a = _ ==> _` irule >>
      qpat_x_assum `!aid v. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >>
      first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv es cc` by
    (irule alloca_frame_of_mem_frame >> simp[] >> metis_tac[]) >>
  irule alloca_frame_trans >>
  qexistsl_tac [`cenv`, `es`, `cc`, `sa`] >>
  simp[] >>
  qpat_x_assum `!frame_start. _` (qspec_then `sa` mp_tac) >>
  simp[alloca_frame_def]
QED

Finalise compile_for_range_frag

(* Original fixed-run proof, retained during counted port.
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [stmt_frag_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (For id fty (Range e1 e2) bound stmts)
              sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = (uu, sb)` >>
  `uu = ()` by simp[oneTheory.one] >> gvs[] >>
  (* the code and the source loop *)
  drule compile_for_range_parts >>
  disch_then (qspecl_then [`i2w n1`, `i2w n2`, `func`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  drule_all eval_stmt_for_range >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  (* the loop variable's ALLOCA *)
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb _ = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] lookup_block_fn_insts)) >>
     simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (simp[not_local_ptr_def] >> rpt strip_tac >>
     fs[local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = sa.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `step_inst_base A s0 = exec_alloca A s0 (n2w sz : bytes32)` by
    simp[Abbr `A`, step_inst_base_def, venomInstTheory.mk_inst_def] >>
  `?s1. exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (simp[exec_alloca_def] >> BasicProvers.every_case_tac >> simp[]) >>
  fs[] >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `A`, `p`,
               `n2w sz : bytes32`, `s1`, `ctx`] mp_tac stmt_state_rel_exec_alloca >>
  impl_tac >- fs[] >> strip_tac >>
  `s1.vs_current_bb = s0.vs_current_bb /\ s1.vs_inst_idx = s0.vs_inst_idx /\
   ~s1.vs_halted /\ (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
   (!a b. FLOOKUP s0.vs_allocas a = SOME b ==>
          FLOOKUP s1.vs_allocas a = SOME b)` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >> simp[exec_alloca_def] >>
     BasicProvers.every_case_tac >> rw[] >>
     fs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> rw[] >>
     fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `w2n (n2w sz : bytes32) = sz` by fs[] >> fs[] >>
  (* the start and entry blocks *)
  qspecl_then [`ctx`, `func`, `s0`, `s1`, `A`, `sa.cs_current_insts`,
               `sa.cs_current_bb`, `entry_lbl`, `sa.cs_next_id + 1`]
    mp_tac for_start_block >>
  impl_tac >- fs[] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `jump_to entry_lbl s1`, `cv`, `ev`, `i2w n1`,
               `i2w n2 - i2w n1`, `entry_lbl`, `cond_lbl`, `sa.cs_next_id + 2`,
               `sa.cs_next_id + 3`, `sa.cs_next_id + 4`]
    mp_tac for_entry_block >>
  impl_tac >- fs[jump_to_def] >>
  REWRITE_TAC [wordsTheory.WORD_SUB_ADD2] >> strip_tac >>
  (* the variables *)
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
   cv <> ev /\ cv <> p /\ ev <> p` by (fs[] >> rw[] >> fs[]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs ev) /\
   (!scs. not_local_ptr cenv scs dv) /\ (!scs. not_local_ptr cenv scs nv)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `ev = _` SUBST1_TAC >>
     qpat_assum `dv = _` SUBST1_TAC >> qpat_assum `nv = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `sa` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_x_assum `sb0.cs_next_var <= sb1.cs_next_var` mp_tac >>
     qpat_x_assum `sb0.cs_next_var = _` SUBST1_TAC >>
     simp[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >>
     `not_local_ptr cenv (FEMPTY::scs) p` by
       (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
        qexists_tac `sa` >> simp[]) >>
     irule not_local_ptr_name_update >> qexistsl_tac [`cenv`, `id`] >> simp[] >>
     qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  (* the state at the condition block *)
  qabbrev_tac `cc = jump_to cond_lbl (update_var ev (i2w n2)
                  (update_var cv (i2w n1) (jump_to entry_lbl s1)))` >>
  `stmt_state_rel ctx func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >>
     conj_tac >- (irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
     irule stmt_state_rel_update_var >>
     conj_tac >- (irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
     fs[stmt_state_rel_jump_to]) >>
  `lookup_var p cc = SOME w` by
    (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >>
     qpat_x_assum `lookup_var p s1 = _` mp_tac >>
     qpat_assum `p = _` (fn th => REWRITE_TAC [th]) >> simp[lookup_var_def]) >>
  `FLOOKUP cc.vs_allocas A.inst_id = SOME (w2n w, sz)` by
    (simp[Abbr `cc`, jump_to_def, update_var_def] >>
     qpat_x_assum `FLOOKUP s1.vs_allocas A.inst_id = _` mp_tac >>
     qpat_assum `A.inst_id = _` (fn th => REWRITE_TAC [th])) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x cc = SOME v` by
    (rpt strip_tac >>
     `x <> p /\ x <> cv /\ x <> ev` by
       (fs[not_fresh_at_def] >> rpt conj_tac >> first_x_assum irule >>
        simp[]) >>
     simp[Abbr `cc`, lookup_var_def, jump_to_def, update_var_def,
          FLOOKUP_UPDATE] >>
     fs[GSYM lookup_var_def] >> metis_tac[]) >>
  `ret_pc_ok cenv sa cc` by
    (qspecl_then [`cenv`, `cenv`, `sa`, `sa`, `s0`, `cc`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `!fuel rr. run_from fuel ctx func cc = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func s0 = rr` by
    (simp[Abbr `cc`] >> metis_tac[]) >>
  `!a b. FLOOKUP s0.vs_allocas a = SOME b ==> FLOOKUP cc.vs_allocas a = SOME b`
    by simp[Abbr `cc`, jump_to_def, update_var_def] >>
  `cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
   lookup_var cv cc = SOME (i2w (n1 + 0)) /\ lookup_var ev cc = SOME (i2w n2)`
    by (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
             FLOOKUP_UPDATE] >> fs[jump_to_def]) >>
  (* the loop *)
  qspecl_then [`Num (n2 - n1)`, `P`, `ctx`, `func`, `cenv`, `bc`, `cx`, `lctx`,
               `RetQ`, `ty`, `stmts`, `id`, `tyv`, `p`, `sz`, `A`, `cv`, `ev`,
               `dv`, `nv`, `n1`, `n2`, `cond_lbl`, `exit_lbl`, `body_lbl`,
               `incr_lbl`, `sa.cs_next_id + 5`, `sa.cs_next_id + 6`,
               `sa.cs_next_id + 7`, `bbb`, `sj.cs_next_id`, `sj.cs_next_id + 1`,
               `sj.cs_next_id + 2`, `sb0`, `sb1`, `sj`, `sa`, `0`, `es`, `cc`,
               `w`, `res`, `es'`] mp_tac for_loop_alloca >>
  impl_tac
  >- (simp[for_code_def] >> conj_tac
      >- simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
              is_terminator_def, not_fresh_at_def] >>
      conj_tac
      >- (rw[not_fresh_at_def] >>
          first_x_assum (qspec_then `sb1.cs_next_var` mp_tac) >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac
  >- (rename1 `s9.vs_current_bb = exit_lbl` >> disj1_tac >>
      qexists_tac `s9` >> qexists_tac `cenv` >>
      simp[stmt_lands_def, block_is_terminated_def, cenv_top_ext_refl] >>
      rpt strip_tac >> metis_tac[]) >>
  disj2_tac >> rename1 `exit_result r9` >>
  drule exit_result_not_error >> strip_tac >> metis_tac[]
QED

*)

(* The literal-ends case. *)
Theorem compile_for_range_lit_frag:
  !P ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es tyv.
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P (es with gas_obs := []) /\
    (!st0 c st1 ex inc ei j.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts))
      (eval_stmt cx
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts)) es
Proof
  rpt strip_tac >> irule compile_for_range_frag >>
  simp[eval_expr_int_lit, lower_value_int_lit] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `P` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The same with the body's judgment at every source state. *)
Theorem compile_for_range_lit_frag_simple:
  !ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es tyv.
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!st0 c st1 ex inc es1.
       declare_local cenv id fty st0 = (c, st1) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts) es1) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts))
      (eval_stmt cx
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts)) es
Proof
  rpt strip_tac >>
  irule (Q.SPEC `\e. T` compile_for_range_lit_frag) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!st0 c st1 ex inc es1. _` drule >> simp[]
QED

(* Integrity gate for the preserved public literal-range guarantees. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "FOR_FORCE_AUDIT OK\n"
     else raise Fail "range consumer inherited admission"
  end) [compile_for_range_parts, compile_for_range_lit_parts,
        compile_for_range_frag, compile_for_range_lit_frag,
        compile_for_range_lit_frag_simple];

(*
 * Assert Combiner Pass — Abort Proofs (Part 3a)
 *
 * Contains abort_head_is_assert, ac_sim_step_abort, ac_run_insts_sim_abort.
 *)

Theory acAbortProofs
Ancestors
  acSimPrecondProofs acChainProofs acBaseProofs assertCombinerDefs
  passSimulationDefs passSimulationProps
  stateEquiv stateEquivProps execEquivParamProps venomInstProps venomExecProps
  dfgAnalysisProps venomState venomWf venomExecSemantics venomExecProofs
  analysisSimDefs analysisSimProofsBase
Libs
  pred_setTheory arithmeticTheory listTheory rich_listTheory alistTheory

(* Prefix abort propagation: if prefix aborts, append also aborts *)
Triviality run_insts_prefix_abort[local]:
  !xs ys fuel ctx s a sa.
    run_insts fuel ctx xs s = Abort a sa ==>
    run_insts fuel ctx (xs ++ ys) s = Abort a sa
Proof
  rpt strip_tac >> simp[run_insts_append] >>
  qpat_assum `_ = Abort _ _` (fn ab => REWRITE_TAC[ab]) >> simp[]
QED

(* Two-step prefix then abort: [a;b;c] where [a;b] OK, c aborts *)
Triviality run_insts_two_snoc_abort[local]:
  !a b c fuel ctx s s' r sa.
    run_insts fuel ctx [a; b] s = OK s' /\
    step_inst fuel ctx c s' = Abort r sa ==>
    run_insts fuel ctx [a; b; c] s = Abort r sa
Proof
  rpt strip_tac >>
  simp[run_insts_three] >>
  first_assum (fn ok => REWRITE_TAC[ok]) >>
  simp[Once run_insts_def, Once run_insts_def]
QED

(* Passthrough abort tactic: when contrib = [h] and h aborts on s_t.
   Expects:
     - merge step fact as top assumption
     - step_inst h s_t = Abort ... in assumptions
     - ac_sim_precond in assumptions (will be removed)
     - state_equiv in assumptions *)
(* execution_equiv V ==> execution_equiv UNIV *)
Triviality exec_equiv_weaken_UNIV[local]:
  !V s1 s2. execution_equiv V s1 s2 ==> execution_equiv UNIV s1 s2
Proof
  simp[execution_equiv_def]
QED

(* state_equiv V ==> execution_equiv UNIV *)
Triviality state_equiv_exec_equiv_UNIV[local]:
  !V s1 s2. state_equiv V s1 s2 ==> execution_equiv UNIV s1 s2
Proof
  metis_tac[state_equiv_def, exec_equiv_weaken_UNIV]
QED

(* Passthrough abort: merge step gives (mp', [h]), h aborts on s_t.
   Top assumption must be the merge step equation.
   Removes ac_sim_precond to avoid simp loops. *)
val passthrough_abort_tac =
  qpat_assum `ac_sim_precond _ _ _ _ _ _` (K ALL_TAC) >>
  pop_assum (fn ms =>
    let val ms' = SIMP_RULE std_ss [LET_THM] ms
        val eqs = CONJUNCTS (REWRITE_RULE [pairTheory.PAIR_EQ] ms')
    in EVERY (map (fn eq => REWRITE_TAC[eq]) eqs) end) >>
  qpat_assum `sa = _` SUBST_ALL_TAC >>
  simp_tac std_ss [run_insts_append, LET_THM,
                    Once run_insts_def, Once run_insts_def] >>
  qpat_assum `step_inst _ _ _ s_t = _`
    (fn ab => REWRITE_TAC[ab]) >>
  simp_tac (srw_ss()) [] >>
  irule revert_returndata_exec_equiv_UNIV >>
  metis_tac[state_equiv_exec_equiv_UNIV];

(* Abort preamble: when step_inst aborts and precond holds, h is ASSERT.
   Also provides inst_wf, operand eval equiv, and var constraints. *)
Triviality abort_head_is_assert[local]:
  !h insts cands mp dfg fuel ctx s_o s_t V sa.
    step_inst fuel ctx h s_o = Abort Revert_abort sa /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V ==>
    h.inst_opcode = ASSERT /\ inst_wf h /\ h.inst_opcode <> INVOKE /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s_t)) /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s_o)) /\
    (!op. MEM op h.inst_operands ==>
       eval_operand op s_o = eval_operand op s_t) /\
    (!x. MEM (Var x) h.inst_operands ==> x NOTIN V) /\
    (!x. MEM x h.inst_outputs ==> x NOTIN V)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `ac_sim_precond _ _ _ _ _ _`
    (fn th =>
       ASSUME_TAC th >>
       let val hf = MATCH_MP ac_sim_precond_head_facts th
           fun rest t = CONJUNCT2 t
       in
         ASSUME_TAC (CONJUNCT1 hf) >>
         ASSUME_TAC (CONJUNCT1 (rest hf)) >>
         ASSUME_TAC (CONJUNCT1 (rest (rest hf))) >>
         ASSUME_TAC (CONJUNCT1 (rest (rest (rest (rest hf))))) >>
         ASSUME_TAC (CONJUNCT1 (rest (rest (rest (rest (rest hf)))))) >>
         ASSUME_TAC (CONJUNCT1 (rest (rest (rest (rest (rest (rest hf)))))))
       end) >>
  `!op. MEM op h.inst_operands ==>
     eval_operand op s_o = eval_operand op s_t` by (
    rpt strip_tac >> match_mp_tac eval_operand_equiv >>
    qexists_tac `V` >> conj_tac >- metis_tac[state_equiv_sym] >>
    rpt strip_tac >> metis_tac[MEM]) >>
  `!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s_o)` by
    metis_tac[] >>
  `h.inst_opcode = ASSERT` suffices_by metis_tac[] >>
  qpat_x_assum `_ \/ _` mp_tac >> strip_tac >>
  `?s'. step_inst fuel ctx h s_o = OK s'` by
    metis_tac[safe_between_wf_step_ok] >>
  qpat_x_assum `step_inst _ _ _ _ = Abort _ _` mp_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` (fn ok => REWRITE_TAC[ok]) >>
  simp_tac (srw_ss()) []
QED

Triviality cons_three_append[local]:
  !a b c rest. a::b::c::rest = [a;b;c] ++ rest
Proof simp[]
QED

(* When mc.mc_first_id = h.inst_id, mc.mc_second_id is in rest *)
Triviality cands_first_at_head_MEM[local]:
  !cands h rest mc.
    ac_cands_ordered cands (h :: rest) /\ MEM mc cands /\
    mc.mc_first_id = h.inst_id ==>
    ?inst_s. MEM inst_s rest /\ inst_s.inst_id = mc.mc_second_id
Proof
  rw[ac_cands_ordered_def] >>
  first_x_assum (qspec_then `mc` mp_tac) >> simp[] >>
  (impl_tac >- (qexists_tac `h` >> simp[])) >>
  strip_tac >>
  `idx_f = 0` by (
    spose_not_then assume_tac >>
    Cases_on `idx_f` >> gvs[] >>
    `MEM ((EL n rest).inst_id) (MAP (\i. i.inst_id) rest)` by
      (rw[MEM_MAP] >> qexists_tac `EL n rest` >> simp[MEM_EL] >>
       qexists_tac `n` >> simp[]) >>
    gvs[ALL_DISTINCT]) >>
  gvs[] >>
  qexists_tac `EL (idx_s - 1) rest` >>
  Cases_on `idx_s` >> gvs[MEM_EL] >>
  qexists_tac `n` >> simp[]
QED

(* Case 6: diff preds, nofid — contrib = [OR;IZ;h'], h' aborts *)
Triviality abort_case_diff_nofid[local]:
  !h insts cands mp mc dfg fuel ctx s_o s_t V.
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc /\
    ~EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) <> mc.mc_second_pred /\
    h.inst_opcode = ASSERT /\
    step_inst fuel ctx h s_t =
      Abort Revert_abort (revert_state (set_returndata [] s_t)) /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    ?sa'.
      run_insts fuel ctx
        (contrib ++ SND (FOLDL (ac_apply_merge_step cands) (mp', []) insts)) s_t =
        Abort Revert_abort sa' /\
      execution_equiv UNIV
        (revert_state (set_returndata [] s_o)) sa'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `afp = case ALOOKUP mp mc.mc_first_id of
                        NONE => mc.mc_first_pred | SOME p => p` >>
  qabbrev_tac `or_v = ac_or_var h.inst_id` >>
  qabbrev_tac `iz_v = ac_iz_var h.inst_id` >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by
    (first_assum (mp_tac o MATCH_MP FIND_P) >> simp[]) >>
  `?v. h.inst_operands = [Var v] /\
       ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred` by
    (drule_all ac_sim_precond_find_iszero >> simp[]) >>
  `eval_operand (Var v) s_t = SOME 0w` by (
    `IS_SOME (eval_operand (Var v) s_t)` by (
      qpat_assum `ac_sim_precond _ _ _ _ _ _`
        (ASSUME_TAC o MATCH_MP ac_sim_precond_head_facts) >>
      gvs[] >> metis_tac[MEM]) >>
    Cases_on `eval_operand (Var v) s_t` >- gvs[] >>
    rename1 `SOME cv` >>
    Cases_on `cv = 0w` >- simp[] >>
    `step_inst fuel ctx h s_t = OK s_t` by
      metis_tac[step_assert_ok] >>
    gvs[]) >>
  `?pred_val. eval_operand mc.mc_second_pred s_t = SOME pred_val /\
     pred_val <> 0w` by (
    match_mp_tac ac_assert_abort_pred_nonzero >>
    qexistsl_tac [`dfg`, `v`] >> simp[] >>
    metis_tac[ac_sim_precond_dfg_inv]) >>
  `?afp_val. eval_operand afp s_t = SOME afp_val` by (
    drule_all ac_sim_precond_afp_eval >>
    simp[Abbr`afp`, optionTheory.IS_SOME_EXISTS]) >>
  `or_v <> iz_v` by simp[Abbr`or_v`, Abbr`iz_v`, ac_or_iz_distinct] >>
  (* Merge step equation — establish BEFORE rename *)
  qabbrev_tac `or_inst = <| inst_id := h.inst_id; inst_opcode := OR;
      inst_operands := [afp; mc.mc_second_pred];
      inst_outputs := [or_v] |>` >>
  qabbrev_tac `iz_inst = <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
      inst_operands := [Var or_v]; inst_outputs := [iz_v] |>` >>
  qabbrev_tac `h' = h with inst_operands := [Var iz_v]` >>
  `ac_apply_merge_step cands (mp,[]) h =
     ((mc.mc_second_id, Var or_v)::mp, [or_inst; iz_inst; h'])` by (
    mp_tac (SIMP_RULE (srw_ss()) [LET_THM] ac_step_diff_nofid) >>
    disch_then (qspecl_then [`cands`, `mp`, `h`, `mc`] mp_tac) >>
    impl_tac >- fs[NOT_EXISTS] >>
    simp[Abbr`afp`, Abbr`or_v`, Abbr`iz_v`,
         Abbr`or_inst`, Abbr`iz_inst`, Abbr`h'`]) >>
  (* OR/IZ step: run [or_inst; iz_inst] s_t = OK s_iz *)
  qspecl_then [`fuel`, `ctx`, `s_t`, `afp`, `mc.mc_second_pred`,
               `or_v`, `iz_v`, `h.inst_id`, `afp_val`, `pred_val`]
    mp_tac ac_or_iz_step >>
  simp[] >> simp[LET_THM] >> strip_tac >>
  (* Substitute Abbrevs into the or/iz run_insts assumption *)
  qpat_x_assum `Abbrev (or_inst = _)` (SUBST_ALL_TAC o GSYM o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (iz_inst = _)` (SUBST_ALL_TAC o GSYM o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rename1 `run_insts _ _ [or_inst; iz_inst] s_t = OK s_iz` >>
  `bool_to_word (afp_val || pred_val = 0w) = 0w` by (
    `afp_val || pred_val <> 0w` by
      (CCONTR_TAC >> full_simp_tac std_ss [word_or_eq_0w]) >>
    simp[bool_to_word_def]) >>
  `eval_operand (Var iz_v) s_iz = SOME 0w` by full_simp_tac std_ss [] >>
  `step_inst fuel ctx h' s_iz =
     Abort Revert_abort (revert_state (set_returndata [] s_iz))` by (
    simp[Abbr`h'`] >> match_mp_tac step_assert_abort >>
    qexists_tac `Var iz_v` >> simp[]) >>
  (* Compose: [or;iz;h'] aborts *)
  `run_insts fuel ctx [or_inst; iz_inst; h'] s_t =
     Abort Revert_abort (revert_state (set_returndata [] s_iz))` by
    metis_tac[run_insts_two_snoc_abort] >>
  (* Finish *)
  simp[LET_THM] >>
  qexists_tac `revert_state (set_returndata [] s_iz)` >> conj_tac
  >- (ONCE_REWRITE_TAC[cons_three_append] >>
      irule run_insts_prefix_abort >> first_assum ACCEPT_TAC)
  >- (irule revert_returndata_exec_equiv_UNIV >>
      irule execution_equiv_trans >> qexists_tac `s_t` >> conj_tac
      >- metis_tac[state_equiv_exec_equiv_UNIV]
      >- first_assum ACCEPT_TAC)
QED

(* Transfer from ac_sim_precond to ac_chain_inv.
   Given ac_sim_precond for h::insts, produce ac_chain_inv for insts
   with possibly extended mp and new state, given a diff-preds witness. *)
Triviality precond_to_chain_inv[local]:
  !cands h insts mp s V dfg mp_new s_new pred_op v.
    ac_sim_precond cands mp dfg (h::insts) s V /\
    (* State: pred_op evaluable to nonzero *)
    eval_operand pred_op s_new = SOME v /\ v <> 0w /\
    (* State preservation: eval preserved for all relevant operands *)
    (!i op. MEM i insts /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s_new)) /\
    (!mc. MEM mc cands ==> IS_SOME (eval_operand mc.mc_second_pred s_new) /\
                            IS_SOME (eval_operand mc.mc_first_pred s_new)) /\
    (!id p. ALOOKUP mp_new id = SOME p ==> IS_SOME (eval_operand p s_new)) /\
    (* pred_op not clobbered by remaining instructions *)
    (!i x. MEM i insts /\ pred_op = Var x ==> ~MEM x i.inst_outputs) /\
    (* pred_op fresh w.r.t. or/iz vars *)
    (!mc x. MEM mc cands /\ pred_op = Var x /\
       (?i. MEM i insts /\ mc.mc_second_id = i.inst_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (* MP: keys disjoint from remaining instruction IDs *)
    (!i. MEM i insts ==> ALOOKUP mp_new i.inst_id = NONE) /\
    (* MP: outputs don't clobber mp pred vars *)
    (!i x id. MEM i insts /\ MEM x i.inst_outputs /\
       ALOOKUP mp_new id = SOME (Var x) ==> F) /\
    (* MP: or/iz freshness for mp pred vars *)
    (!id x mc. ALOOKUP mp_new id = SOME (Var x) /\ MEM mc cands /\
       (?i. MEM i insts /\ i.inst_id = mc.mc_second_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (* Diff-preds witness *)
    (?inst_s mc_s. MEM inst_s insts /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp_new mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp_new mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    ac_chain_inv cands insts mp_new s_new pred_op v
Proof
  rw[ac_chain_inv_def, ac_sim_precond_def] >>
  rpt strip_tac >> metis_tac[MEM, ac_cands_ordered_tail]
QED

(* Bridge from ac_sim_precond to ac_chain_inv_w (weak invariant).
   Used for fid abort cases where we stay in state s_t (no OR/IZ prefix). *)
Triviality precond_to_chain_inv_w[local]:
  !cands h insts mp s V dfg pred_op v.
    ac_sim_precond cands mp dfg (h::insts) s V /\
    eval_operand pred_op s = SOME v /\ v <> 0w /\
    (!i x. MEM i insts /\ pred_op = Var x ==> ~MEM x i.inst_outputs) /\
    (!mc x. MEM mc cands /\ pred_op = Var x /\
       (?i. MEM i insts /\ mc.mc_second_id = i.inst_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (?inst_s mc_s. MEM inst_s insts /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    ac_chain_inv_w cands insts mp dfg s pred_op v
Proof
  rw[ac_chain_inv_w_def, ac_sim_precond_def] >>
  rpt strip_tac >> metis_tac[MEM, ac_cands_ordered_tail]
QED



(* NOP after OR/IZ: [OR;IZ;NOP] succeeds *)
Triviality run_insts_or_iz_nop[local]:
  !fuel ctx or_inst iz_inst nop_inst s s_iz.
    run_insts fuel ctx [or_inst; iz_inst] s = OK s_iz /\
    nop_inst.inst_opcode = NOP ==>
    run_insts fuel ctx [or_inst; iz_inst; nop_inst] s = OK s_iz
Proof
  rpt strip_tac >>
  simp[run_insts_three] >>
  first_assum (fn ok => REWRITE_TAC[ok]) >>
  simp[Once run_insts_def, Once run_insts_def, step_nop_identity]
QED

(* FIND returns the specific element when ALL_DISTINCT on the key field *)
Triviality FIND_unique_match[local]:
  !cands mc0.
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    MEM mc0 cands ==>
    FIND (\mc'. mc'.mc_second_id = mc0.mc_second_id) cands = SOME mc0
Proof
  Induct_on `cands` >> simp[FIND_thm] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `mc0.mc_second_id <> h.mc_second_id` by
    (fs[ALL_DISTINCT, MAP, MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

(* Case 1: fid, FIND=NONE — contrib = [NOP], chain_inv_w + deferred abort *)
Triviality abort_case_fid_none[local]:
  !h insts cands mp dfg fuel ctx s_o s_t V.
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands /\
    h.inst_opcode = ASSERT /\
    step_inst fuel ctx h s_t =
      Abort Revert_abort (revert_state (set_returndata [] s_t)) /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_t)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    ?sa'.
      run_insts fuel ctx
        (contrib ++ SND (FOLDL (ac_apply_merge_step cands) (mp', []) insts)) s_t =
        Abort Revert_abort sa' /\
      execution_equiv UNIV
        (revert_state (set_returndata [] s_o)) sa'
Proof
  rpt gen_tac >> strip_tac >>
  (* Extract mc_fid with mc_fid.mc_first_id = h.inst_id *)
  `?mc_fid. MEM mc_fid cands /\ mc_fid.mc_first_id = h.inst_id` by
    (fs[EXISTS_MEM] >> metis_tac[]) >>
  (* Iszero bridge from precond: h is first_id *)
  `?cond_v. h.inst_operands = [Var cond_v] /\
     ac_get_iszero_operand dfg {} (Var cond_v) = SOME mc_fid.mc_first_pred` by
    (fs[ac_sim_precond_def] >> metis_tac[MEM]) >>
  `eval_operand (Var cond_v) s_t = SOME 0w` by (
    `IS_SOME (eval_operand (Var cond_v) s_t)` by
      (fs[ac_sim_precond_def] >> metis_tac[MEM]) >>
    Cases_on `eval_operand (Var cond_v) s_t` >- gvs[] >>
    rename1 `SOME cv` >> Cases_on `cv = 0w` >- simp[] >>
    `step_inst fuel ctx h s_t = OK s_t` by metis_tac[step_assert_ok] >>
    gvs[]) >>
  `?pred_val. eval_operand mc_fid.mc_first_pred s_t = SOME pred_val /\
     pred_val <> 0w` by (
    match_mp_tac ac_assert_abort_pred_nonzero >>
    qexistsl_tac [`dfg`, `cond_v`] >> simp[] >>
    metis_tac[ac_sim_precond_dfg_inv]) >>
  (* Merge step *)
  `ac_apply_merge_step cands (mp,[]) h = (mp,
     [h with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>])` by
    metis_tac[ac_step_fid_none] >>
  (* Witness in insts *)
  `ac_cands_ordered cands (h::insts)` by fs[ac_sim_precond_def] >>
  `?inst_s. MEM inst_s insts /\ inst_s.inst_id = mc_fid.mc_second_id` by
    metis_tac[cands_first_at_head_MEM] >>
  `ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands)` by
    fs[ac_sim_precond_def] >>
  `FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_fid` by
    metis_tac[FIND_unique_match] >>
  `ALOOKUP mp mc_fid.mc_first_id = NONE` by (
    `ALOOKUP mp h.inst_id = NONE` by
      metis_tac[ac_sim_precond_head_facts] >>
    gvs[]) >>
  (* Build chain_inv_w: expand to proof obligation, use precond *)
  (* precond_to_chain_inv_w residual conjuncts *)
  `!i x. MEM i insts /\ mc_fid.mc_first_pred = Var x ==>
     ~MEM x i.inst_outputs` by
    (rpt strip_tac >> fs[ac_sim_precond_def] >> metis_tac[MEM]) >>
  `!mc' x. MEM mc' cands /\ mc_fid.mc_first_pred = Var x /\
     (?i. MEM i insts /\ mc'.mc_second_id = i.inst_id) ==>
     x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id` by
    (rpt strip_tac >> fs[ac_sim_precond_def] >> metis_tac[MEM]) >>
  (`ac_chain_inv_w cands insts mp dfg s_t mc_fid.mc_first_pred pred_val` by (
    match_mp_tac precond_to_chain_inv_w >>
    qexistsl_tac [`h`, `V`] >>
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    qexistsl_tac [`inst_s`, `mc_fid`] >>
    simp[])) >>
  drule ac_deferred_chain_abort_w >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  simp[LET_THM, run_insts_append, Once run_insts_def, step_nop_identity,
       Once run_insts_def] >>
  irule execution_equiv_trans >>
  qexists_tac `revert_state (set_returndata [] s_t)` >>
  conj_tac >| [
    irule revert_returndata_exec_equiv_UNIV >>
    metis_tac[state_equiv_exec_equiv_UNIV],
    first_assum ACCEPT_TAC
  ]
QED

(* Extend chain_inv_w mp: when all insts have inst_id <> key, and the new
   value is evaluable and doesn't clash with outputs/preds, extending mp
   preserves chain_inv_w. *)
Triviality chain_inv_w_extend_mp[local]:
  !cands insts mp dfg s pred_op v key new_val.
    ac_chain_inv_w cands insts mp dfg s pred_op v /\
    (!i. MEM i insts ==> i.inst_id <> key) /\
    IS_SOME (eval_operand new_val s) /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs /\ new_val = Var x ==> F) /\
    (?inst_s mc_s. MEM inst_s insts /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP ((key, new_val)::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    ac_chain_inv_w cands insts ((key, new_val)::mp) dfg s pred_op v
Proof
  rw[ac_chain_inv_w_def] >>
  rpt strip_tac >>
  TRY (pop_assum mp_tac >> simp[ALOOKUP_def] >>
       Cases_on `key = id` >> simp[] >> metis_tac[])
QED

(* Case 3: same preds, fid — contrib = [NOP], chain_inv_w + deferred abort *)
Triviality abort_case_same_fid[local]:
  !h insts cands mp mc dfg fuel ctx s_o s_t V.
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred /\
    h.inst_opcode = ASSERT /\
    step_inst fuel ctx h s_t =
      Abort Revert_abort (revert_state (set_returndata [] s_t)) /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_t)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    ?sa'.
      run_insts fuel ctx
        (contrib ++ SND (FOLDL (ac_apply_merge_step cands) (mp', []) insts)) s_t =
        Abort Revert_abort sa' /\
      execution_equiv UNIV
        (revert_state (set_returndata [] s_o)) sa'
Proof
  rpt gen_tac >> strip_tac >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by
    (first_assum (mp_tac o MATCH_MP FIND_P) >> simp[]) >>
  qabbrev_tac `afp = case ALOOKUP mp mc.mc_first_id of
                        NONE => mc.mc_first_pred | SOME p => p` >>
  (* Extract iszero bridge *)
  `?cond_v. h.inst_operands = [Var cond_v] /\
     ac_get_iszero_operand dfg {} (Var cond_v) = SOME mc.mc_second_pred` by
    (drule_all ac_sim_precond_find_iszero >> simp[]) >>
  `eval_operand (Var cond_v) s_t = SOME 0w` by (
    `IS_SOME (eval_operand (Var cond_v) s_t)` by (
      qpat_assum `ac_sim_precond _ _ _ _ _ _`
        (ASSUME_TAC o MATCH_MP ac_sim_precond_head_facts) >>
      gvs[] >> metis_tac[MEM]) >>
    Cases_on `eval_operand (Var cond_v) s_t` >- gvs[] >>
    rename1 `SOME cv` >> Cases_on `cv = 0w` >- simp[] >>
    `step_inst fuel ctx h s_t = OK s_t` by metis_tac[step_assert_ok] >>
    gvs[]) >>
  `?pred_val. eval_operand mc.mc_second_pred s_t = SOME pred_val /\
     pred_val <> 0w` by (
    match_mp_tac ac_assert_abort_pred_nonzero >>
    qexistsl_tac [`dfg`, `cond_v`] >> simp[] >>
    metis_tac[ac_sim_precond_dfg_inv]) >>
  (* Merge step *)
  `ac_apply_merge_step cands (mp,[]) h =
     ((mc.mc_second_id, afp)::mp,
      [h with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>])` by (
    mp_tac (SIMP_RULE (srw_ss()) [LET_THM] ac_step_same_fid) >>
    disch_then (qspecl_then [`cands`, `mp`, `h`, `mc`] mp_tac) >>
    impl_tac >- simp[] >>
    simp[Abbr`afp`]) >>
  (* Witness in insts for fid *)
  `?mc_fid. MEM mc_fid cands /\ mc_fid.mc_first_id = h.inst_id` by
    (fs[EXISTS_MEM] >> metis_tac[]) >>
  `ac_cands_ordered cands (h::insts)` by fs[ac_sim_precond_def] >>
  `?inst_s. MEM inst_s insts /\ inst_s.inst_id = mc_fid.mc_second_id` by
    metis_tac[cands_first_at_head_MEM] >>
  `ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands)` by
    fs[ac_sim_precond_def] >>
  `FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_fid` by
    metis_tac[FIND_unique_match] >>
  `ALOOKUP mp h.inst_id = NONE` by metis_tac[ac_sim_precond_head_facts] >>
  (* same_preds: afp = mc.mc_second_pred, so pred_op = afp *)
  `afp = mc.mc_second_pred` by simp[Abbr`afp`] >>
  (* Build chain_inv_w with extended mp directly *)
  (* Chain consistency: mc and mc_fid share h.inst_id *)
  `mc.mc_second_pred = mc_fid.mc_first_pred` by
    (fs[ac_sim_precond_def] >> metis_tac[]) >>
  (* Rewrite eval using chain consistency *)
  `eval_operand mc_fid.mc_first_pred s_t = SOME pred_val` by gvs[] >>
  (* Pre-establish residual conjuncts *)
  `!i x. MEM i insts /\ mc_fid.mc_first_pred = Var x ==>
     ~MEM x i.inst_outputs` by
    (rpt strip_tac >> fs[ac_sim_precond_def] >> metis_tac[MEM]) >>
  `!mc' x. MEM mc' cands /\ mc_fid.mc_first_pred = Var x /\
     (?i. MEM i insts /\ mc'.mc_second_id = i.inst_id) ==>
     x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id` by
    (rpt strip_tac >> fs[ac_sim_precond_def] >> metis_tac[MEM]) >>
  (* Build chain_inv_w with old mp *)
  (`ac_chain_inv_w cands insts mp dfg s_t mc_fid.mc_first_pred pred_val` by (
    match_mp_tac precond_to_chain_inv_w >>
    qexistsl_tac [`h`, `V`] >> rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    qexistsl_tac [`inst_s`, `mc_fid`] >> simp[])) >>
  (* Simplify the let with the merge step equation *)
  simp[LET_THM] >> gvs[] >>
  (* Extend chain_inv_w from mp to (h.inst_id, mc_fid.mc_first_pred)::mp *)
  `!i. MEM i insts ==> i.inst_id <> h.inst_id` by (
    rpt strip_tac >>
    fs[ac_cands_ordered_def, ALL_DISTINCT, MEM_MAP] >>
    metis_tac[]) >>
  drule chain_inv_w_extend_mp >>
  disch_then (qspecl_then [`h.inst_id`, `mc_fid.mc_first_pred`] mp_tac) >>
  simp[optionTheory.IS_SOME_DEF] >>
  (impl_tac >- (
    (conj_tac >- metis_tac[]) >>
    qexistsl_tac [`inst_s`, `mc_fid`] >> simp[ALOOKUP_def])) >>
  strip_tac >>
  (* Apply deferred chain abort *)
  drule ac_deferred_chain_abort_w >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  (impl_tac >- (
    conj_tac >- (rpt strip_tac >> res_tac >>
      gvs[optionTheory.NOT_IS_SOME_EQ_NONE]) >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >>
  simp[Once run_insts_def, step_nop_identity] >>
  irule execution_equiv_trans >>
  qexists_tac `revert_state (set_returndata [] s_t)` >>
  conj_tac >| [
    irule revert_returndata_exec_equiv_UNIV >>
    metis_tac[state_equiv_exec_equiv_UNIV],
    first_assum ACCEPT_TAC
  ]
QED

(* Transfer ac_sim_precond to ac_chain_inv after OR/IZ step.
   Specialized for the diff-preds fid case: mp extended with (h.inst_id, Var or_v),
   state s_iz = s_t + or_v/iz_v, with a diff-preds witness in insts. *)
(* Eval transfer helper: transfer IS_SOME from s_t to s_iz via freshness *)
Triviality eval_transfer_is_some[local]:
  !opr or_v iz_v s_t s_iz.
    IS_SOME (eval_operand opr s_t) /\
    (!opr'. (!x. opr' = Var x ==> x <> or_v /\ x <> iz_v) ==>
       eval_operand opr' s_iz = eval_operand opr' s_t) /\
    (!x. opr = Var x ==> x <> or_v /\ x <> iz_v)
  ==>
    IS_SOME (eval_operand opr s_iz)
Proof
  rpt strip_tac >> `eval_operand opr s_iz = eval_operand opr s_t` by
    metis_tac[] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Triviality alookup_extended_mp_or_iz_fresh[local]:
  !h insts cands mp dfg s V id x mc i.
    ac_sim_precond cands mp dfg (h::insts) s V /\
    ALOOKUP ((h.inst_id, Var (ac_or_var h.inst_id))::mp) id = SOME (Var x) /\
    MEM mc cands /\ MEM i insts /\ i.inst_id = mc.mc_second_id ==>
    x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_id = id`
  >- ((* TRUE: lookup hits new entry, x = ac_or_var h.inst_id *)
      gvs[ALOOKUP_def, operand_11] >>
      (`ALL_DISTINCT (MAP (\i. i.inst_id) (h::insts))` by
        metis_tac[ac_sim_precond_def, ac_cands_ordered_def]) >>
      pop_assum (mp_tac o SIMP_RULE (srw_ss()) [MAP, ALL_DISTINCT, MEM_MAP]) >>
      strip_tac >>
      metis_tac[])
  >- ((* FALSE: lookup falls through to mp *)
      gvs[ALOOKUP_def] >>
      metis_tac[ac_sim_precond_mp_or_iz_fresh, MEM])
QED

Triviality alookup_extended_mp_eval[local]:
  !h insts cands mp dfg s_t s_iz V id p mc_h or_val.
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    ALOOKUP ((h.inst_id, Var (ac_or_var h.inst_id))::mp) id = SOME p /\
    eval_operand (Var (ac_or_var h.inst_id)) s_iz = SOME or_val /\
    MEM mc_h cands /\ mc_h.mc_second_id = h.inst_id /\
    (!opr. (!x. opr = Var x ==> x <> ac_or_var h.inst_id /\ x <> ac_iz_var h.inst_id) ==>
       eval_operand opr s_iz = eval_operand opr s_t) ==>
    IS_SOME (eval_operand p s_iz)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_id = id`
  >- (gvs[ALOOKUP_def, operand_11] >> metis_tac[optionTheory.IS_SOME_DEF])
  >- (gvs[ALOOKUP_def] >>
      (`IS_SOME (eval_operand p s_t)` by
        metis_tac[ac_sim_precond_mp_eval]) >>
      (`MEM h (h::insts)` by simp[]) >>
      metis_tac[eval_transfer_is_some, ac_sim_precond_mp_or_iz_fresh])
QED

Triviality precond_to_chain_inv_or_iz[local]:
  !cands h insts mp s_t s_iz V dfg or_v iz_v or_val
   mc0 i_s0.
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    Abbrev (or_v = ac_or_var h.inst_id) /\
    Abbrev (iz_v = ac_iz_var h.inst_id) /\
    eval_operand (Var or_v) s_iz = SOME or_val /\
    or_val <> 0w /\
    (?mc_h. MEM mc_h cands /\ mc_h.mc_second_id = h.inst_id) /\
    (!opr. (!x. opr = Var x ==> x <> or_v /\ x <> iz_v) ==>
       eval_operand opr s_iz = eval_operand opr s_t) /\
    (* Diff-preds witness *)
    MEM mc0 cands /\ mc0.mc_first_id = h.inst_id /\
    MEM i_s0 insts /\ i_s0.inst_id = mc0.mc_second_id /\
    FIND (\mc'. mc'.mc_second_id = i_s0.inst_id) cands = SOME mc0
  ==>
    ac_chain_inv cands insts ((h.inst_id, Var or_v)::mp) s_iz
      (Var or_v) or_val
Proof
  rpt strip_tac >>
  qunabbrev_tac `or_v` >> qunabbrev_tac `iz_v` >>
  (* Pre-extract facts that multiple goals need *)
  (`ALL_DISTINCT (MAP (\i. i.inst_id) (h::insts))` by
    metis_tac[ac_sim_precond_def, ac_cands_ordered_def]) >>
  (`!i. MEM i insts ==> h.inst_id <> i.inst_id` by (
    pop_assum (mp_tac o SIMP_RULE (srw_ss()) [MAP, ALL_DISTINCT, MEM_MAP]) >>
    metis_tac[MEM_MAP])) >>
  irule precond_to_chain_inv >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  (* G1: ∀i x id. outputs vs ALOOKUP mp_new ⇒ F *)
  >- (rpt strip_tac >>
      pop_assum (mp_tac o SIMP_RULE std_ss [ALOOKUP_def]) >>
      COND_CASES_TAC >> simp_tac (srw_ss()) [operand_11] >> rpt strip_tac
      >- ((`MEM i (h::insts)` by metis_tac[MEM]) >>
          metis_tac[ac_sim_precond_def])
      >- ((`MEM i (h::insts)` by metis_tac[MEM]) >>
          metis_tac[ac_sim_precond_def]))
  (* G2: pred_op output freshness *)
  >- (simp_tac (srw_ss()) [operand_11] >> metis_tac[MEM, ac_sim_precond_def])
  (* G3: operand eval transfer *)
  >- (rpt strip_tac >>
      (`MEM i (h::insts)` by metis_tac[MEM]) >>
      metis_tac[eval_transfer_is_some, ac_sim_precond_def])
  (* G4: mp_new keys disjoint *)
  >- (rpt strip_tac >>
      (`h.inst_id <> i.inst_id` by metis_tac[]) >>
      ASM_SIMP_TAC std_ss [ALOOKUP_def] >>
      (`MEM i (h::insts)` by metis_tac[MEM]) >>
      metis_tac[ac_sim_precond_def])
  (* G5: pred_op or/iz freshness *)
  >- (simp_tac (srw_ss()) [operand_11] >> rpt strip_tac >>
      metis_tac[ac_sim_precond_def, ac_cands_ordered_def, MEM])
  (* G6: cand pred eval transfer *)
  >- (rpt strip_tac >>
      metis_tac[eval_transfer_is_some, ac_sim_precond_def])
  (* G7: ALOOKUP mp_new or/iz freshness *)
  >- metis_tac[alookup_extended_mp_or_iz_fresh]
  (* G8: ALOOKUP mp_new eval *)
  >- (rpt strip_tac >>
      match_mp_tac (alookup_extended_mp_eval |> REWRITE_RULE[AND_IMP_INTRO]) >>
      metis_tac[])
  (* G9: witness existential *)
  >- (qexistsl_tac [`i_s0`, `mc0`] >> simp_tac std_ss [] >>
      (`mc0.mc_first_id = h.inst_id` by metis_tac[]) >>
      ASM_SIMP_TAC std_ss [ALOOKUP_def] >>
      Cases_on `mc0.mc_second_pred` >> simp_tac (srw_ss()) [operand_11] >>
      metis_tac[ac_sim_precond_def, ac_or_var_inj, ac_or_iz_distinct])
  (* G10: ac_sim_precond existential *)
  >- metis_tac[]
QED

(* Case 5: diff preds, fid — contrib = [OR;IZ;NOP], chain_inv + deferred abort *)
Triviality abort_case_diff_fid[local]:
  !h insts cands mp mc dfg fuel ctx s_o s_t V.
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) <> mc.mc_second_pred /\
    h.inst_opcode = ASSERT /\
    step_inst fuel ctx h s_t =
      Abort Revert_abort (revert_state (set_returndata [] s_t)) /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    ?sa'.
      run_insts fuel ctx
        (contrib ++ SND (FOLDL (ac_apply_merge_step cands) (mp', []) insts)) s_t =
        Abort Revert_abort sa' /\
      execution_equiv UNIV
        (revert_state (set_returndata [] s_o)) sa'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `afp = case ALOOKUP mp mc.mc_first_id of
                        NONE => mc.mc_first_pred | SOME p => p` >>
  qabbrev_tac `or_v = ac_or_var h.inst_id` >>
  qabbrev_tac `iz_v = ac_iz_var h.inst_id` >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by
    (first_assum (mp_tac o MATCH_MP FIND_P) >> simp[]) >>
  `?v. h.inst_operands = [Var v] /\
       ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred` by
    (drule_all ac_sim_precond_find_iszero >> simp[]) >>
  `eval_operand (Var v) s_t = SOME 0w` by (
    `IS_SOME (eval_operand (Var v) s_t)` by (
      qpat_assum `ac_sim_precond _ _ _ _ _ _`
        (ASSUME_TAC o MATCH_MP ac_sim_precond_head_facts) >>
      gvs[] >> metis_tac[MEM]) >>
    Cases_on `eval_operand (Var v) s_t` >- gvs[] >>
    rename1 `SOME cv` >>
    Cases_on `cv = 0w` >- simp[] >>
    `step_inst fuel ctx h s_t = OK s_t` by
      metis_tac[step_assert_ok] >>
    gvs[]) >>
  `?pred_val. eval_operand mc.mc_second_pred s_t = SOME pred_val /\
     pred_val <> 0w` by (
    match_mp_tac ac_assert_abort_pred_nonzero >>
    qexistsl_tac [`dfg`, `v`] >> simp[] >>
    metis_tac[ac_sim_precond_dfg_inv]) >>
  `?afp_val. eval_operand afp s_t = SOME afp_val` by (
    drule_all ac_sim_precond_afp_eval >>
    simp[Abbr`afp`, optionTheory.IS_SOME_EXISTS]) >>
  `or_v <> iz_v` by simp[Abbr`or_v`, Abbr`iz_v`, ac_or_iz_distinct] >>
  (* Merge step equation *)
  qabbrev_tac `or_inst = <| inst_id := h.inst_id; inst_opcode := OR;
      inst_operands := [afp; mc.mc_second_pred];
      inst_outputs := [or_v] |>` >>
  qabbrev_tac `iz_inst = <| inst_id := h.inst_id + 1; inst_opcode := ISZERO;
      inst_operands := [Var or_v]; inst_outputs := [iz_v] |>` >>
  qabbrev_tac `nop_inst = h with <| inst_opcode := NOP;
      inst_operands := []; inst_outputs := [] |>` >>
  `ac_apply_merge_step cands (mp,[]) h =
     ((mc.mc_second_id, Var or_v)::mp, [or_inst; iz_inst; nop_inst])` by (
    mp_tac (SIMP_RULE (srw_ss()) [LET_THM] ac_step_diff_fid) >>
    disch_then (qspecl_then [`cands`, `mp`, `h`, `mc`] mp_tac) >>
    impl_tac >- simp[] >>
    simp[Abbr`afp`, Abbr`or_v`, Abbr`iz_v`,
         Abbr`or_inst`, Abbr`iz_inst`, Abbr`nop_inst`]) >>
  (* OR/IZ step: run [or_inst; iz_inst] s_t = OK s_iz *)
  qspecl_then [`fuel`, `ctx`, `s_t`, `afp`, `mc.mc_second_pred`,
               `or_v`, `iz_v`, `h.inst_id`, `afp_val`, `pred_val`]
    mp_tac ac_or_iz_step >>
  simp[] >> simp[LET_THM] >> strip_tac >>
  (* Substitute Abbrevs *)
  qpat_x_assum `Abbrev (or_inst = _)` (SUBST_ALL_TAC o GSYM o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (iz_inst = _)` (SUBST_ALL_TAC o GSYM o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  rename1 `run_insts _ _ [or_inst; iz_inst] s_t = OK s_iz` >>
  qabbrev_tac `or_val = afp_val || pred_val` >>
  `or_val <> 0w` by
    (simp[Abbr`or_val`] >> CCONTR_TAC >>
     full_simp_tac std_ss [word_or_eq_0w]) >>
  `eval_operand (Var or_v) s_iz = SOME or_val` by
    full_simp_tac std_ss [Abbr`or_val`] >>
  `nop_inst.inst_opcode = NOP` by simp[Abbr`nop_inst`] >>
  (* NOP succeeds: [or;iz;nop] s_t = OK s_iz *)
  `run_insts fuel ctx [or_inst; iz_inst; nop_inst] s_t = OK s_iz` by
    metis_tac[run_insts_or_iz_nop] >>
  (* Establish chain_inv for insts with updated mp, state s_iz *)
  (* Need: mc0 (fid witness for h) provides the diff-preds witness *)
  `?mc0. MEM mc0 cands /\ mc0.mc_first_id = h.inst_id` by
    (fs[EXISTS_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands)` by
    (fs[ac_sim_precond_def]) >>
  (* Helper: eval preservation from s_t to s_iz for non-or/iz vars *)
  `!opr. (!x. opr = Var x ==> x <> or_v /\ x <> iz_v) ==>
     eval_operand opr s_iz = eval_operand opr s_t` by metis_tac[] >>
  (* mc0.mc_second_id has an instruction in insts *)
  `?i_s0. MEM i_s0 insts /\ i_s0.inst_id = mc0.mc_second_id` by (
    `ac_cands_ordered cands (h::insts)` by fs[ac_sim_precond_def] >>
    fs[ac_cands_ordered_def] >>
    first_x_assum (qspec_then `mc0` mp_tac) >>
    impl_tac >- (simp[] >> qexists_tac `h` >> simp[]) >>
    strip_tac >>
    `idx_f = 0` by (
      Cases_on `idx_f` >> gvs[] >>
      `n < LENGTH insts` by simp[] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) (h::insts))` by
        fs[ac_sim_precond_def, ac_cands_ordered_def] >>
      fs[ALL_DISTINCT, MAP, MEM_MAP, EL_CONS] >> metis_tac[MEM_EL]) >>
    `idx_s > 0` by simp[] >>
    qexists_tac `EL (idx_s - 1) insts` >>
    `idx_s - 1 < LENGTH insts` by simp[] >>
    conj_tac >- metis_tac[MEM_EL] >>
    Cases_on `idx_s` >> gvs[EL_CONS]) >>
  `FIND (\mc'. mc'.mc_second_id = i_s0.inst_id) cands = SOME mc0` by
    metis_tac[FIND_unique_match] >>
  `ac_chain_inv cands insts ((h.inst_id, Var or_v)::mp) s_iz
     (Var or_v) or_val` by (
    irule (precond_to_chain_inv_or_iz |> REWRITE_RULE[AND_IMP_INTRO]) >>
    simp[Abbr`or_v`, Abbr`iz_v`] >>
    metis_tac[]) >>
  (* Apply ac_deferred_chain_abort *)
  `?sa_rest. run_insts fuel ctx
     (SND (FOLDL (ac_apply_merge_step cands)
       ((h.inst_id, Var or_v)::mp, []) insts)) s_iz =
     Abort Revert_abort sa_rest /\
     execution_equiv UNIV (revert_state (set_returndata [] s_iz)) sa_rest` by
    metis_tac[ac_deferred_chain_abort] >>
  (* Compose: [or;iz;nop] ++ rest aborts *)
  simp[LET_THM] >>
  qexists_tac `sa_rest` >> conj_tac
  >- (ONCE_REWRITE_TAC[cons_three_append] >>
      simp[run_insts_append] >>
      first_assum (fn ok => REWRITE_TAC[ok]) >>
      simp[])
  >- (irule execution_equiv_trans >>
      qexists_tac `revert_state (set_returndata [] s_iz)` >> conj_tac
      >- (irule revert_returndata_exec_equiv_UNIV >>
          irule execution_equiv_trans >> qexists_tac `s_t` >> conj_tac
          >- metis_tac[state_equiv_exec_equiv_UNIV]
          >- first_assum ACCEPT_TAC)
      >- first_assum ACCEPT_TAC)
QED

(* Abort at head: the head instruction aborts, and the contribution also
   aborts (or defers the abort which eventually fires). *)
Theorem ac_sim_step_abort:
  !h insts cands mp dfg fuel ctx s_o s_t sa V.
    step_inst fuel ctx h s_o = Abort Revert_abort sa /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg (h::insts) s_t V /\
    (!i x. MEM i (h::insts) /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_t)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::insts))) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    ?sa'.
      run_insts fuel ctx
        (contrib ++ SND (FOLDL (ac_apply_merge_step cands) (mp', []) insts)) s_t =
        Abort Revert_abort sa' /\
      execution_equiv UNIV sa sa'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abort_head_is_assert >> strip_tac >>
  `?cond_op. h.inst_operands = [cond_op]` by
    metis_tac[assert_single_operand] >>
  `eval_operand cond_op s_o = SOME 0w` by (
    `IS_SOME (eval_operand cond_op s_o)` by metis_tac[MEM] >>
    Cases_on `eval_operand cond_op s_o` >- full_simp_tac std_ss [] >>
    rename1 `SOME cv` >>
    Cases_on `cv = 0w` >- simp[] >>
    `step_inst fuel ctx h s_o = OK s_o` by
      metis_tac[step_assert_ok] >>
    full_simp_tac (srw_ss()) []) >>
  `eval_operand cond_op s_t = SOME 0w` by metis_tac[MEM] >>
  `step_inst fuel ctx h s_t =
   Abort Revert_abort (revert_state (set_returndata [] s_t))` by
    metis_tac[step_assert_abort] >>
  `step_inst fuel ctx h s_o =
   Abort Revert_abort (revert_state (set_returndata [] s_o))` by
    metis_tac[step_assert_abort] >>
  `sa = revert_state (set_returndata [] s_o)` by
    metis_tac[exec_result_11] >>
  (* Remove inst_wf early to prevent simp loops *)
  qpat_assum `inst_wf _` (K ALL_TAC) >>
  (* Derive insts-restricted (a)+(b) for abort case helpers *)
  (Q.SUBGOAL_THEN `!i x. MEM i insts /\ MEM x i.inst_outputs ==>
      ~IS_SOME (lookup_var x s_t)` ASSUME_TAC >-
    (rpt strip_tac >> res_tac >> gvs[])) >>
  (Q.SUBGOAL_THEN `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts))`
    ASSUME_TAC >-
    fs[ALL_DISTINCT_APPEND]) >>
  Cases_on `FIND (\mc. mc.mc_second_id = h.inst_id) cands`
  >- (
    Cases_on `EXISTS (\mc. mc.mc_first_id = h.inst_id) cands`
    >- (drule_all abort_case_fid_none >> simp[LET_THM] >>
        qpat_assum `sa = _` SUBST_ALL_TAC >> simp[])
    >- (
      (* Case 2: passthrough — contrib = [h], h aborts on s_t *)
      `ac_apply_merge_step cands (mp,[]) h = (mp, [h])` by
        metis_tac[ac_step_passthrough] >>
      passthrough_abort_tac
    )
  )
  >- (
    rename1 `FIND _ _ = SOME mc` >>
    Cases_on `EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands`
    >- (
      Cases_on `(case ALOOKUP mp mc.mc_first_id of
                   SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred`
      >- (drule_all abort_case_same_fid >> simp[LET_THM] >>
          qpat_assum `sa = _` SUBST_ALL_TAC >> simp[])
      >- (
        (* Case 5: diff preds, fid — use abort_case_diff_fid *)
        drule_all abort_case_diff_fid >> simp[LET_THM] >>
        qpat_assum `sa = _` SUBST_ALL_TAC >> simp[]
      )
    )
    >- (
      Cases_on `(case ALOOKUP mp mc.mc_first_id of
                   SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred`
      >- (
        (* Case 4: same preds passthrough — contrib = [h], h aborts on s_t *)
        `ac_apply_merge_step cands (mp,[]) h =
           ((mc.mc_second_id,
             case ALOOKUP mp mc.mc_first_id of
               SOME p => p | NONE => mc.mc_first_pred)::mp, [h])` by
          metis_tac[ac_step_same_nofid] >>
        passthrough_abort_tac
      )
      >- (
        (* Case 6: diff preds, nofid — use extracted triviality *)
        drule_all abort_case_diff_nofid >> simp[LET_THM] >>
        qpat_assum `sa = _` SUBST_ALL_TAC >> simp[]
      )
    )
  )
QED

(* Abort case: when original aborts, transform also aborts with equiv state *)
Theorem ac_run_insts_sim_abort:
  !insts cands mp dfg fuel ctx s_o s_t sa V.
    run_insts fuel ctx insts s_o = Abort Revert_abort sa /\
    state_equiv V s_o s_t /\
    ac_sim_precond cands mp dfg insts s_t V /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s_t)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    ?sa'.
      run_insts fuel ctx
        (SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)) s_t =
        Abort Revert_abort sa' /\
      execution_equiv UNIV sa sa'
Proof
  Induct >- simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  (* Decompose run_insts for h::rest *)
  qpat_x_assum `run_insts _ _ (h::_) _ = _` mp_tac >>
  simp[Once run_insts_def] >>
  Cases_on `step_inst fuel ctx h s_o` >> simp[]
  >- (
    (* step_inst h = OK s1_o, abort is in the tail *)
    rename1 `step_inst fuel ctx h s_o = OK s1_o` >> strip_tac >>
    (* Derive (a) on s_o from (a) on s_t via no_redefine_transfer_equiv *)
    (Q.SUBGOAL_THEN `!i x. MEM i (h::insts) /\ MEM x i.inst_outputs ==>
        ~IS_SOME (lookup_var x s_o)` ASSUME_TAC >- (
      qspecl_then [`h::insts`, `s_t`, `s_o`, `V`]
        mp_tac no_redefine_transfer_equiv >>
      (impl_tac >- (
        rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- metis_tac[ac_sim_precond_outputs_notin_V]
        >- metis_tac[state_equiv_sym])) >>
      simp[])) >>
    drule_all ac_sim_step_ok >> simp[LET_THM] >>
    Cases_on `ac_apply_merge_step cands (mp,[]) h` >>
    rename1 `_ = (mp', contrib)` >> simp[] >> strip_tac >>
    qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
    simp[LET_THM] >> strip_tac >>
    pop_assum (fn th => REWRITE_TAC[th]) >>
    simp[run_insts_append] >>
    (* Maintain (a)+(b) for tail *)
    (Q.SUBGOAL_THEN `~is_terminator h.inst_opcode` ASSUME_TAC >-
      metis_tac[ac_sim_precond_head_facts]) >>
    (Q.SUBGOAL_THEN `(!i x. MEM i insts /\ MEM x i.inst_outputs ==>
        ~IS_SOME (lookup_var x s1_o)) /\
     ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts))` STRIP_ASSUME_TAC >-
      metis_tac[no_redefine_step_tail]) >>
    (* Transfer (a) from s1_o to s_c *)
    (Q.SUBGOAL_THEN `!i x. MEM i insts /\ MEM x i.inst_outputs ==>
        ~IS_SOME (lookup_var x s_c)` ASSUME_TAC >- (
      qspecl_then [`insts`, `s1_o`, `s_c`, `V`]
        mp_tac no_redefine_transfer_equiv >>
      impl_tac >- (
        rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- metis_tac[ac_sim_precond_outputs_notin_V]
        >- first_assum ACCEPT_TAC) >>
      simp[])) >>
    first_x_assum (drule_then (drule_then drule)) >>
    disch_then irule >>
    rpt strip_tac >> res_tac >>
    gvs[optionTheory.NOT_IS_SOME_EQ_NONE]
  )
  >- (
    (* step_inst h = Abort, abort at head *)
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    drule_all ac_sim_step_abort >> simp[LET_THM] >>
    Cases_on `ac_apply_merge_step cands (mp,[]) h` >>
    rename1 `_ = (mp', contrib)` >> simp[] >> strip_tac >>
    qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
    simp[LET_THM] >> strip_tac >>
    pop_assum (fn th => REWRITE_TAC[th]) >> simp[]
  )
QED

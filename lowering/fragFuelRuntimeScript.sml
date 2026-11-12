(*
 * Fuel bounds for the runtime entry prefix: the code compile_generate_runtime
 * (linear dispatch) and compile_generate_grouped_runtime emit before the
 * internal function bodies.  Each prefix satisfies
 *   fuel_okS (\st. T) UNIV {} {} prefix
 * so it starts in any state, starts no block a later part may jump to, and
 * jumps to no label outside itself.
 *
 * The grouped path's jobs are described by three per-job facts: the label
 * of its block (job_label), and, for its environment, cenv_ptrs_below 0 and
 * no constructor exit label, plus, for a common job, that its kwarg buffer
 * pointers are variables below the next fresh variable (job_ok).
 *
 * TOP-LEVEL:
 *   fuel_okS_runtime_entry_prefix, fuel_okS_grouped_runtime_entry_prefix,
 *   compile_generate_runtime_linear_split,
 *   compile_generate_grouped_runtime_split,
 *   fuel_ok_compile_group_entries, fuel_ok_compile_external_groups,
 *   compile_external_groups_result, fuel_ok_compile_group_dispatch_linear,
 *   compile_group_dispatch_linear_result, fuel_okS_compile_external_jobs
 *)

Theory fragFuelRuntime
Ancestors
  fragFuel fragFuelStmtBase fragFuelStmtGlue fragFuelRuntimeDispatch
  fragFuelRuntimeBody moduleLowering compileEnv emitHelper venomInst
  list pred_set pair
Libs
  fragFuelLib

val hstmts = ``!cenv' lctx ty ss Wv E.
    cenv_ptrs_in Wv cenv' /\ stmt_exits_in E cenv' lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv {} E
      (compile_stmts cenv' lctx ty ss)``

val hexpr = ``!c t e Wv E. fuel_ok Wv {} E (compile_expr c t e)``

(* Statements are beta-normalised so the per-group and per-job predicates
   below appear as plain case expressions. *)
fun bn t = rhs (concl (QCONV (DEPTH_CONV BETA_CONV) t))

(* The label of the block a group's code is reached at after dispatch. *)
val glabel = ``\g. case g of
    ExternalSingle sl pk => FST pk
  | ExternalDefaults cm ents specs hoff => cm.ec_common_label``

(* The label the dispatch jumps to for a group. *)
val gsel = ``\g. case g of
    ExternalSingle sl pk => FST (SND sl)
  | ExternalDefaults cm ents specs hoff => cm.ec_common_label``

val gstatic = ``\g. case g of
    ExternalSingle sl pk =>
      cenv_ptrs_below 0 (FST (SND pk)) /\
      (FST (SND pk)).ce_ctor_exit_label = NONE
  | ExternalDefaults cm ents specs hoff =>
      cenv_ptrs_below 0 cm.ec_env /\ cm.ec_env.ce_ctor_exit_label = NONE``

val jlabel = ``\j. case j of
    ExternalLegacyJob pk => FST pk
  | ExternalCommonJob cm kws => cm.ec_common_label``

val jok = ``\n:num j. case j of
    ExternalLegacyJob pk =>
      cenv_ptrs_below 0 (FST (SND pk)) /\
      (FST (SND pk)).ce_ctor_exit_label = NONE
  | ExternalCommonJob cm kws =>
      cenv_ptrs_below 0 cm.ec_env /\ cm.ec_env.ce_ctor_exit_label = NONE /\
      EVERY (\k. !x. FST (SND k) = Var x ==> var_below n x) kws``

val jobs_pre = bn ``\st:compile_state. EVERY (^jok st.cs_next_var) jobs``

val ok_tac = match_mp_tac fuel_okS_of_ok

val nb_tac = ok_tac >> MATCH_ACCEPT_TAC fuel_ok_new_block

(* Sequence two parts, the second under no precondition. *)
fun sq lm lf tac =
  match_mp_tac fuel_okS_seqQ >> qexistsl_tac [lm, lf, `\st. T`] >>
  rpt conj_tac
  >- simp[next_stable_def]
  >- simp[]
  >- simp[SUBSET_DEF]
  >- tac

(* ===== Helpers ===== *)

Theorem fuel_okS_assume[local]:
  !b P Wv L E m.
    (!st. P st ==> b) /\ (b ==> fuel_okS P Wv L E m) ==> fuel_okS P Wv L E m
Proof
  rpt strip_tac >> Cases_on `b` >> fs[fuel_okS_def] >> metis_tac[]
QED

val next_stable_jobs_st =
  bn ``!jobs. next_stable (\st:compile_state. EVERY (^jok st.cs_next_var) jobs)``

val jobs_mono_st =
  bn ``!n n' jobs. EVERY (^jok n) jobs /\ n <= n' ==> EVERY (^jok n') jobs``

Theorem jobs_mono[local]:
  ^jobs_mono_st
Proof
  rw[EVERY_MEM] >> first_x_assum drule >> Cases_on `j` >> simp[] >>
  rpt strip_tac >> irule var_below_le >> qexists_tac `n` >> simp[] >>
  first_x_assum irule >> qexists_tac `k` >> simp[]
QED

Theorem next_stable_jobs[local]:
  ^next_stable_jobs_st
Proof
  rw[next_stable_def] >> irule jobs_mono >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

(* ===== Grouped dispatch ===== *)

Theorem fuel_ok_compile_group_entries:
  ^hexpr ==>
  !entries mid common kw off Wv E.
    common.ec_common_label IN E ==>
    fuel_ok Wv {} E (compile_group_entries mid entries common kw off)
Proof
  strip_tac >>
  Induct >- simp[compile_group_entries_def, fuel_ok_return] >>
  PairCases >> rpt strip_tac >>
  `!mid kw off. fuel_ok Wv {} E (compile_group_entries mid entries common kw off)`
    by (rpt gen_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  PURE_ONCE_REWRITE_TAC [compile_group_entries_def] >>
  PURE_REWRITE_TAC [compile_entry_point_kwargs_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst_jmp,
             fuel_ok_compile_entry_checks,
             UNDISCH fuel_ok_compile_init_kwargs] >>
  simp[is_terminator_def]
QED

val ext_groups_st = bn ``^hexpr ==>
  !groups mid Wv E.
    EVERY (\g. ^gsel g IN E) groups ==>
    fuel_ok Wv {} E (compile_external_groups mid groups)``

Theorem fuel_ok_compile_external_groups:
  ^ext_groups_st
Proof
  strip_tac >>
  Induct >- simp[compile_external_groups_def, fuel_ok_return] >>
  rpt gen_tac >> simp_tac std_ss [EVERY_DEF] >> strip_tac >>
  `!mid. fuel_ok Wv {} E (compile_external_groups mid groups)`
    by (gen_tac >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  Cases_on `h`
  >- (rename1 `ExternalSingle sl pk` >> PairCases_on `sl` >> fs[] >>
      PURE_ONCE_REWRITE_TAC [compile_external_groups_def] >>
      fuel_auto [fuel_ok_compile_selector_checks, fuel_ok_return] >>
      simp[]) >>
  rename1 `ExternalDefaults cm ents specs hoff` >> fs[] >>
  PURE_ONCE_REWRITE_TAC [compile_external_groups_def] >>
  fuel_auto [fuel_ok_compile_create_kwarg_allocas, fuel_ok_return,
             UNDISCH fuel_ok_compile_group_entries]
QED

val groups_result_st = bn ``^hexpr ==>
  !groups mid st jobs st'.
    compile_external_groups mid groups st = (jobs, st') ==>
    st.cs_next_var <= st'.cs_next_var /\
    MAP ^jlabel jobs = MAP ^glabel groups /\
    (EVERY ^gstatic groups ==> EVERY (^jok st'.cs_next_var) jobs)``

Theorem compile_external_groups_result:
  ^groups_result_st
Proof
  strip_tac >>
  Induct >- simp[compile_external_groups_def, comp_return_def] >>
  Cases
  >- (rename1 `ExternalSingle sl pk` >> PairCases_on `sl` >> rpt gen_tac >>
      simp[compile_external_groups_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      rename1 `compile_selector_checks _ _ st = (_, s1)` >>
      rename1 `compile_external_groups _ groups s1 = (jobs0, s2)` >>
      `fuel_ok UNIV {} UNIV (compile_selector_checks mid [(sl0, sl1)])`
        by (irule fuel_ok_compile_selector_checks >> simp[]) >>
      drule_all fuel_ok_next >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  rename1 `ExternalDefaults cm ents specs hoff` >> rpt gen_tac >>
  simp[compile_external_groups_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_create_kwarg_allocas _ _ st = (kw, s1)` >>
  rename1 `compile_group_entries _ _ _ _ _ s1 = (_, s2)` >>
  rename1 `compile_external_groups _ groups s2 = (jobs0, s3)` >>
  drule compile_create_kwarg_allocas_ptrs >> strip_tac >>
  `fuel_ok UNIV {} UNIV (compile_group_entries mid ents cm kw hoff)`
    by (irule (UNDISCH fuel_ok_compile_group_entries) >> simp[]) >>
  drule_all fuel_ok_next >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `st.cs_next_var <= s3.cs_next_var /\ s1.cs_next_var <= s3.cs_next_var`
    by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  simp[] >> rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[var_below_le]
QED

val disp_st = bn ``^hexpr ==>
  !groups fb Wv E.
    fb IN E /\ EVERY (\g. ^gsel g IN E) groups ==>
    fuel_ok Wv {} E (compile_group_dispatch_linear groups fb)``

Theorem fuel_ok_compile_group_dispatch_linear:
  ^disp_st
Proof
  rpt strip_tac >>
  `!mid. fuel_ok Wv {} E (compile_external_groups mid groups)`
    by (gen_tac >> irule (UNDISCH fuel_ok_compile_external_groups) >>
        first_assum ACCEPT_TAC) >>
  PURE_REWRITE_TAC [compile_group_dispatch_linear_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst_jmp,
             fuel_ok_return] >>
  simp[is_terminator_def]
QED

val disp_result_st = bn ``^hexpr ==>
  !groups fb st jobs st'.
    compile_group_dispatch_linear groups fb st = (jobs, st') ==>
    MAP ^jlabel jobs = MAP ^glabel groups /\
    (EVERY ^gstatic groups ==> EVERY (^jok st'.cs_next_var) jobs)``

Theorem compile_group_dispatch_linear_result:
  ^disp_result_st
Proof
  strip_tac >> drule compile_external_groups_result >> strip_tac >>
  rpt gen_tac >>
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_external_groups _ groups s1 = (jobs0, s2)` >>
  rename1 `emit_inst JMP _ _ s2 = (_, s3)` >>
  first_x_assum drule >> strip_tac >>
  `fuel_ok UNIV {} UNIV (emit_inst JMP [Label fb] [])`
    by (irule fuel_ok_emit_inst_jmp >> simp[]) >>
  drule_all fuel_ok_next >> strip_tac >>
  simp[] >> strip_tac >> irule jobs_mono >>
  qexists_tac `s2.cs_next_var` >> simp[]
QED

(* ===== Grouped bodies ===== *)

val common_pre = bn ``\st:compile_state.
  EVERY (^jok st.cs_next_var) (ExternalCommonJob cm kws :: jobs)``

val jobs_st = bn ``^hstmts ==>
  !jobs.
    fuel_okS (\st. EVERY (^jok st.cs_next_var) jobs) UNIV
      (set (MAP ^jlabel jobs)) {} (compile_external_jobs jobs)``

Theorem fuel_okS_compile_external_jobs:
  ^jobs_st
Proof
  strip_tac >> Induct
  >- (simp[compile_external_jobs_def] >> ok_tac >>
      MATCH_ACCEPT_TAC fuel_ok_return) >>
  Cases
  >- (rename1 `ExternalLegacyJob pk` >>
      PURE_ONCE_REWRITE_TAC [compile_external_jobs_def] >>
      match_mp_tac fuel_okS_seqQ >>
      qexistsl_tac [`{FST pk}`, `set (MAP ^jlabel jobs)`, `^jobs_pre`] >>
      rpt conj_tac
      >- MATCH_ACCEPT_TAC next_stable_jobs
      >- simp[]
      >- simp[SUBSET_DEF]
      >- (match_mp_tac fuel_okS_assume >>
          qexists_tac `cenv_ptrs_below 0 (FST (SND pk)) /\
                       (FST (SND pk)).ce_ctor_exit_label = NONE` >>
          conj_tac >- simp[] >> strip_tac >>
          match_mp_tac fuel_okS_mono >>
          qexistsl_tac [`\st. T`, `UNIV`, `set (MAP FST [pk])`, `{}`] >>
          rpt conj_tac
          >- (match_mp_tac (UNDISCH fuel_okS_compile_external_fn_bodies) >>
              simp[]) >>
          simp[SUBSET_DEF]) >>
      first_assum ACCEPT_TAC) >>
  rename1 `ExternalCommonJob cm kws` >>
  PURE_ONCE_REWRITE_TAC [compile_external_jobs_def] >>
  match_mp_tac fuel_okS_seqQ >>
  qexistsl_tac [`{cm.ec_common_label}`, `set (MAP ^jlabel jobs)`,
                `^common_pre`] >>
  rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_jobs
  >- simp[]
  >- simp[SUBSET_DEF]
  >- nb_tac >>
  match_mp_tac fuel_okS_seqQ >>
  qexistsl_tac [`{}`, `set (MAP ^jlabel jobs)`, `^jobs_pre`] >>
  rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_jobs
  >- simp[]
  >- simp[]
  >- (match_mp_tac fuel_okS_assume >>
      qexists_tac `cenv_ptrs_below 0 cm.ec_env /\
                   cm.ec_env.ce_ctor_exit_label = NONE` >>
      conj_tac >- simp[] >> strip_tac >>
      match_mp_tac fuel_okS_mono >>
      qexistsl_tac [`\st. cenv_ptrs_below st.cs_next_var
                            (compile_register_kwarg_vars cm.ec_env kws)`,
                    `UNIV`, `{}`, `{}`] >>
      rpt conj_tac
      >- (match_mp_tac fuel_okS_compile_common_function_body >>
          conj_tac >> first_assum ACCEPT_TAC)
      >- (simp[] >> rpt strip_tac >>
          irule (GEN_ALL (CONJUNCT2 (SPEC_ALL compile_register_kwarg_vars_ptrs))) >>
          simp[] >> irule cenv_ptrs_below_le >> qexists_tac `0` >> simp[]) >>
      simp[]) >>
  first_assum ACCEPT_TAC
QED

(* ===== Fallback ===== *)

Theorem fuel_okS_fallback_case[local]:
  ^hstmts ==>
  !fallback_fn.
    (!fbc. fallback_fn = SOME fbc ==>
           cenv_ptrs_below 0 (FST fbc) /\ (FST fbc).ce_ctor_exit_label = NONE) ==>
    fuel_okS (\st. T) UNIV {} {}
      (case fallback_fn of
         NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
       | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
               fb_ty) =>
           compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view
             fb_body fb_ty)
Proof
  strip_tac >> Cases >> simp[]
  >- (ok_tac >> irule fuel_ok_emit_inst_halt >> simp[]) >>
  PairCases_on `x` >> simp[] >> strip_tac >>
  match_mp_tac fuel_okS_mono >>
  qexistsl_tac [`\st. cenv_ptrs_below st.cs_next_var x0`, `UNIV`, `{}`, `{}`] >>
  rpt conj_tac
  >- (match_mp_tac fuel_okS_compile_fallback_body >> conj_tac >>
      first_assum ACCEPT_TAC)
  >- (rw[] >> irule cenv_ptrs_below_le >> qexists_tac `0` >> simp[]) >>
  simp[]
QED

(* ===== The prefixes ===== *)

Theorem fuel_okS_runtime_entry_prefix:
  ^hstmts ==>
  !selectors external_fns fallback_fn.
    EVERY (\f. cenv_ptrs_below 0 (FST (SND f)) /\
               (FST (SND f)).ce_ctor_exit_label = NONE) external_fns /\
    EVERY (\s. MEM (FST (SND s)) (MAP FST external_fns)) selectors /\
    (!fbc. fallback_fn = SOME fbc ==>
           cenv_ptrs_below 0 (FST fbc) /\ (FST fbc).ce_ctor_exit_label = NONE) ==>
    fuel_okS (\st. T) UNIV {} {}
      (do fallback_lbl <- fresh_label "fallback";
          compile_selector_dispatch_linear
            (MAP (\(sel, lbl, z). (sel, lbl)) selectors) fallback_lbl;
          compile_external_fn_bodies external_fns;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                   fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                 fb_view fb_body fb_ty)
       od)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- simp[next_stable_def]
  >- (ok_tac >> fuel_auto []) >>
  qx_gen_tac `fb` >> BETA_TAC >>
  sq `{}` `fb INSERT set (MAP FST external_fns)`
    (ok_tac >> match_mp_tac fuel_ok_compile_selector_dispatch_linear >>
     fs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  sq `set (MAP FST external_fns)` `{fb}`
    (match_mp_tac fuel_okS_mono >>
     qexistsl_tac [`\st. T`, `UNIV`, `set (MAP FST external_fns)`, `{}`] >>
     rpt conj_tac
     >- (match_mp_tac (UNDISCH fuel_okS_compile_external_fn_bodies) >>
         first_assum ACCEPT_TAC) >>
     simp[]) >>
  sq `{fb}` `{}` nb_tac >>
  match_mp_tac (UNDISCH fuel_okS_fallback_case) >> first_assum ACCEPT_TAC
QED

val grouped_post =
  bn ``\jobs:external_job list. \st:compile_state.
         EVERY (^jok st.cs_next_var) jobs /\
         MAP ^jlabel jobs = MAP ^glabel groups``

val grouped_st = bn ``^hexpr /\ ^hstmts ==>
  !groups fallback_fn.
    EVERY ^gstatic groups /\ EVERY (\g. ^gsel g = ^glabel g) groups /\
    (!fbc. fallback_fn = SOME fbc ==>
           cenv_ptrs_below 0 (FST fbc) /\ (FST fbc).ce_ctor_exit_label = NONE) ==>
    fuel_okS (\st. T) UNIV {} {}
      (do fallback_lbl <- fresh_label "fallback";
          jobs <- compile_group_dispatch_linear groups fallback_lbl;
          compile_external_jobs jobs;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                   fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                 fb_view fb_body fb_ty)
       od)``

Theorem fuel_okS_grouped_runtime_entry_prefix:
  ^grouped_st
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- simp[next_stable_def]
  >- (ok_tac >> fuel_auto []) >>
  qx_gen_tac `fb` >> BETA_TAC >>
  match_mp_tac fuel_okS_mono >>
  qexistsl_tac [`\st. T`, `UNIV`,
                `{} UNION (fb INSERT set (MAP ^glabel groups))`, `{}`] >>
  rpt conj_tac
  >- (match_mp_tac fuel_okS_bind >>
      qexistsl_tac [`^grouped_post`, `fb INSERT set (MAP ^glabel groups)`,
                    `{}`] >>
      rpt conj_tac
      (* the dispatch *)
      >- (ok_tac >>
          match_mp_tac (UNDISCH fuel_ok_compile_group_dispatch_linear) >>
          simp_tac std_ss [IN_INSERT] >>
          qpat_x_assum `EVERY (\g. _ = _) groups` mp_tac >>
          simp[EVERY_MEM, MEM_MAP] >> metis_tac[])
      (* what the dispatch establishes *)
      >- (rpt strip_tac >>
          drule (UNDISCH compile_group_dispatch_linear_result) >>
          strip_tac >> simp[])
      (* the bodies and the fallback *)
      >- (qx_gen_tac `jobs` >> BETA_TAC >>
          match_mp_tac fuel_okS_assume >>
          qexists_tac `MAP ^jlabel jobs = MAP ^glabel groups` >>
          conj_tac >- simp[] >> strip_tac >>
          match_mp_tac fuel_okS_seqQ >>
          qexistsl_tac [`set (MAP ^jlabel jobs)`, `{fb}`, `\st. T`] >>
          rpt conj_tac
          >- simp[next_stable_def]
          >- simp[]
          >- (pop_assum (SUBST1_TAC o SYM) >> simp[SUBSET_DEF])
          >- (match_mp_tac fuel_okS_mono >>
              qexistsl_tac [`^jobs_pre`, `UNIV`, `set (MAP ^jlabel jobs)`,
                            `{}`] >>
              rpt conj_tac
              >- MATCH_ACCEPT_TAC (UNDISCH fuel_okS_compile_external_jobs) >>
              simp[]) >>
          sq `{fb}` `{}` nb_tac >>
          match_mp_tac (UNDISCH fuel_okS_fallback_case) >>
          first_assum ACCEPT_TAC) >>
      simp[SUBSET_DEF]) >>
  simp[SUBSET_DEF]
QED

(* ===== The generators split at the internal function bodies ===== *)

Theorem compile_generate_runtime_linear_split:
  !selectors external_fns internal_fns fallback_fn bc fmb db ei.
    compile_generate_runtime selectors external_fns internal_fns fallback_fn
      Linear bc fmb db ei =
    comp_ignore_bind
      (do fallback_lbl <- fresh_label "fallback";
          compile_selector_dispatch_linear
            (MAP (\(sel, lbl, z). (sel, lbl)) selectors) fallback_lbl;
          compile_external_fn_bodies external_fns;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                   fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                 fb_view fb_body fb_ty)
       od)
      (comp_bind (compile_internal_fn_bodies internal_fns)
         (\x. comp_return ()))
Proof
  simp[compile_generate_runtime_def, comp_ignore_bind_def, comp_bind_assoc]
QED

Theorem compile_generate_grouped_runtime_split:
  !groups internal_fns fallback_fn.
    compile_generate_grouped_runtime groups internal_fns fallback_fn =
    comp_ignore_bind
      (do fallback_lbl <- fresh_label "fallback";
          jobs <- compile_group_dispatch_linear groups fallback_lbl;
          compile_external_jobs jobs;
          new_block fallback_lbl;
          (case fallback_fn of
             NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
           | SOME (fb_cenv, fb_pay, fb_nr, fb_key, fb_trans, fb_view, fb_body,
                   fb_ty) =>
               compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans
                 fb_view fb_body fb_ty)
       od)
      (comp_bind (compile_internal_fn_bodies internal_fns)
         (\x. comp_return ()))
Proof
  simp[compile_generate_grouped_runtime_def, comp_ignore_bind_def,
       comp_bind_assoc]
QED

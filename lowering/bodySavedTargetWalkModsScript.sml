(* Source-side frame for a target walk with a callback at each actual
   internal call key, including calls into imported modules. *)
Theory bodySavedTargetWalkMods
Ancestors
  targetPureWalkTraversal vyperReadOnlyBranches vyperReadOnlyTargets
  vyperReadOnlyCalls vyperTypeEvalProofs
  vyperMachineFrame vyperCallOutcomeFrame vyperInterpreter vyperState
  stmtLowering exprLowering vyperTypeCallGraph rich_list vyperEvalFrame
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem saved_walk_exprs_nonmutating[local]:
  !es cenv. ~exprs_can_mutate cenv es <=>
    EVERY (\e. ~expr_can_mutate cenv e) es
Proof
  Induct >> simp[expr_can_mutate_def]
QED

Theorem saved_walk_named_nonmutating[local]:
  !kes cenv. named_exprs_can_mutate cenv kes =
    exprs_can_mutate cenv (MAP SND kes)
Proof
  Induct >> simp[expr_can_mutate_def, pairTheory.FORALL_PROD]
QED

Theorem saved_walk_calls_slices[local]:
  !es P n. EVERY P (int_calls_exprs es) ==>
    EVERY P (int_calls_exprs (TAKE n es)) /\
    EVERY P (int_calls_exprs (DROP n es))
Proof
  Induct >> Cases_on `n` >> simp[int_calls_expr_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem saved_walk_bind_guarded[local]:
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) f /\
  (!s v t. f s = (INL v,t) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) (g v)) ==>
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (vyperState$bind f g)
Proof
  strip_tac >> match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> metis_tac[]
QED

val machine_leaf = irule state_rel_frame_machine >>
  conj_tac >- simp[machine_frame_def];

Theorem saved_walk_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tv:type_value) (id:string)
    (body:stmt list) (vs:eval_result list). T) /\
  (!cx e cenv P.
    (!ty key actuals fallback.
      P key /\ ~call_can_mutate cenv (IntCall key) /\
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_exprs cx actuals) ==>
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
    ~expr_can_mutate cenv e /\ EVERY P (int_calls_expr e) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) (eval_expr cx e)) /\
  (!cx es cenv P.
    (!ty key actuals fallback.
      P key /\ ~call_can_mutate cenv (IntCall key) /\
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_exprs cx actuals) ==>
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
    ~exprs_can_mutate cenv es /\ EVERY P (int_calls_exprs es) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) (eval_exprs cx es)) /\
  (!cx bt cenv P.
    (!ty key actuals fallback.
      P key /\ ~call_can_mutate cenv (IntCall key) /\
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_exprs cx actuals) ==>
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
    ~expr_can_mutate cenv (target_to_expr bt) /\ EVERY P (int_calls_target bt) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t) (eval_base_place cx bt)) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[expr_can_mutate_def, target_to_expr_def, call_can_mutate_def] >>
  all_tac
  >- suspend "name"
  >- suspend "global"
  >- suspend "flag"
  >- suspend "ifexp"
  >- (rpt strip_tac >> machine_leaf >> simp[Once evaluate_def, machine_frame_primitives])
  >- suspend "struct"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "extcall"
  >- suspend "intcall"
  >- suspend "rawcall"
  >- suspend "rawcalldata"
  >- suspend "rawlog"
  >- suspend "rawrevert"
  >- (rpt strip_tac >> machine_leaf >> simp[Once evaluate_def, machine_frame_primitives])
  >- suspend "exprs_cons"
  >- suspend "base_name"
  >- suspend "base_global"
  >- suspend "base_attribute"
  >- suspend "base_subscript"
QED

Resume saved_walk_mutual[name]:
  rpt strip_tac >> machine_leaf >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_primitives] >>
  gen_tac >> BETA_TAC >> irule machine_frame_sequence >> simp[machine_frame_primitives]
QED
Resume saved_walk_mutual[global]:
  rpt strip_tac >> machine_leaf >> simp[Once evaluate_def, machine_frame_lookup_global]
QED
Resume saved_walk_mutual[flag]:
  rpt strip_tac >> machine_leaf >> simp[Once evaluate_def, machine_frame_reads]
QED
Resume saved_walk_mutual[base_name]:
  rpt strip_tac >> machine_leaf >> simp[Once evaluate_def] >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_primitives] >>
  gen_tac >> BETA_TAC >> irule machine_frame_sequence >> simp[machine_frame_primitives]
QED
Resume saved_walk_mutual[base_global]:
  rpt strip_tac >> machine_leaf >> simp[Once evaluate_def, machine_frame_lookup_global]
QED

Resume saved_walk_mutual[attribute]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> simp[machine_frame_select_result]
QED
Resume saved_walk_mutual[base_attribute]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> simp[machine_frame_extend_place]
QED

Resume saved_walk_mutual[exprs_cons]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac saved_walk_bind_guarded >>
  conj_tac >- (machine_leaf >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> simp[machine_frame_primitives, machine_frame_unchanged_reads]
QED
Resume saved_walk_mutual[subscript]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac saved_walk_bind_guarded >>
  conj_tac
  >- (Cases_on `subscript_reads_base cx e e'` >> machine_leaf >>
      simp[machine_frame_primitives] >>
      match_mp_tac machine_frame_bind >>
      simp[machine_frame_read_result, machine_frame_primitives]) >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  match_mp_tac machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_select_result]
QED
Resume saved_walk_mutual[base_subscript]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  match_mp_tac machine_frame_bind >>
  simp[machine_frame_read_result, machine_frame_extend_place]
QED

Resume saved_walk_mutual[intcall]:
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  (* The callback owns the callee; only the actual-argument IH is used here. *)
  Cases_on `MEM (src_id_opt,fn) cx.stk`
  >- (once_rewrite_tac[evaluate_def] >> simp[ignore_bind_def, type_check_def, assert_def,
           raise_def, bind_def, state_rel_frame_def, machine_frame_def]) >>
  Cases_on `get_module_code cx src_id_opt`
  >- (once_rewrite_tac[evaluate_def] >> simp[ignore_bind_def, type_check_def, assert_def,
           lift_option_type_def, lift_option_def, return_def, raise_def, bind_def,
           state_rel_frame_def, machine_frame_def]) >>
  rename1 `get_module_code cx src_id_opt = SOME tops` >>
  Cases_on `lookup_callable_function cx.in_deploy fn tops`
  >- (once_rewrite_tac[evaluate_def] >> simp[ignore_bind_def, type_check_def, assert_def,
           lift_option_type_def, lift_option_def, return_def, raise_def, bind_def,
           state_rel_frame_def, machine_frame_def]) >>
  PairCases_on `x` >>
  rename1 `lookup_callable_function cx.in_deploy fn tops = SOME (mut,nr,args,dflts,ret,ss)` >>
  Cases_on `LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH es + LENGTH dflts`
  >- (qpat_assum `!ty key actuals fallback. _ ==> state_rel_frame _ (eval_expr cx (Call ty (IntCall key) actuals fallback))` irule >>
      simp[] >>
      gvs[type_check_def, assert_def, lift_option_type_def, lift_option_def, return_def] >>
      metis_tac[]) >>
  once_rewrite_tac[evaluate_def] >>
  simp[ignore_bind_def, type_check_def, assert_def,
       lift_option_type_def, lift_option_def, return_def, raise_def, bind_def,
       state_rel_frame_def, machine_frame_def]
QED

Resume saved_walk_mutual[struct]:
  rpt strip_tac >>
  gvs[int_calls_expr_def, saved_walk_named_nonmutating, GSYM int_calls_exprs_MAP_SND] >>
  simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> simp[machine_frame_primitives, machine_frame_unchanged_reads]
QED

Resume saved_walk_mutual[ifexp]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- (simp[switch_BoolV_def] >> match_mp_tac walk_bind >>
    conj_tac >- (machine_leaf >> simp[machine_frame_read_result]) >>
    gen_tac >> BETA_TAC >> IF_CASES_TAC >- (simp[] >> metis_tac[]) >>
    IF_CASES_TAC >- (simp[] >> metis_tac[]) >>
    simp[] >> machine_leaf >> simp[machine_frame_primitives]) >>
  gen_tac >> BETA_TAC >> machine_leaf >> simp[machine_frame_primitives, machine_frame_unchanged_reads]
QED

Resume saved_walk_mutual[typebuiltin]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac saved_walk_bind_guarded >>
  conj_tac >- (machine_leaf >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> Cases_on `v` >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_primitives]
QED
Resume saved_walk_mutual[builtin]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[int_calls_expr_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac saved_walk_bind_guarded >>
  conj_tac >- (machine_leaf >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> Cases_on `v` >> BETA_TAC >>
  match_mp_tac walk_bind >> reverse conj_tac
  >- (gen_tac >> BETA_TAC >> machine_leaf >> simp[machine_frame_primitives]) >>
  IF_CASES_TAC >- suspend "builtin_len" >>
  IF_CASES_TAC
  >- (machine_leaf >> simp[state_rel_frame_def, next_gas_reading_def] >>
      gen_tac >> Cases_on `st.gas_obs` >> simp[raise_def, return_def, machine_frame_def, bind_def]) >>
  match_mp_tac walk_bind >> reverse conj_tac
  >- (gen_tac >> BETA_TAC >> Cases_on `is_self_codesize bt es` >> simp[] >>
      machine_leaf >>
      rpt (match_mp_tac machine_frame_bind >>
        conj_tac >- simp[machine_frame_primitives, machine_frame_reads,
                         machine_frame_precompile_call_success] >> gen_tac >> BETA_TAC) >>
      simp[machine_frame_primitives, machine_frame_reads,
           machine_frame_precompile_call_success]) >>
  Cases_on `code_slice_source bt es` >> simp[]
  >- metis_tac[] >>
  rename1 `_ = SOME p` >> PairCases_on `p` >> simp[] >>
  gvs[code_slice_source_SOME, expr_can_mutate_def, int_calls_expr_def] >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >> match_mp_tac walk_bind >>
  conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  rpt (match_mp_tac machine_frame_bind >>
    conj_tac >- simp[machine_frame_primitives, machine_frame_reads] >>
    gen_tac >> BETA_TAC) >>
  simp[machine_frame_primitives, machine_frame_reads]
QED

Resume saved_walk_mutual[builtin_len]:
  match_mp_tac walk_bind >> conj_tac
  >- (Cases_on `es` >> gvs[vyperContextTheory.builtin_args_length_ok_def, type_check_def, assert_def, raise_def, return_def] >>
      gvs[saved_walk_exprs_nonmutating, int_calls_expr_def] >> metis_tac[]) >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  match_mp_tac machine_frame_bind >> simp[machine_frame_reads, machine_frame_primitives]
QED

Resume saved_walk_mutual[rawrevert]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> rewrite_tac[ignore_bind_def] >>
  rpt (match_mp_tac machine_frame_bind >>
    conj_tac >- simp[machine_frame_primitives] >> gen_tac >> BETA_TAC) >>
  simp[machine_frame_primitives]
QED

Resume saved_walk_mutual[rawlog]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> simp[state_rel_frame_def, ignore_bind_def, bind_def, type_check_def,
    assert_def, lift_option_type_def, lift_option_def, return_def, raise_def,
    check_not_static_def, check_def, push_log_def] >>
  rpt gen_tac >> Cases_on `LENGTH v = 2` >> simp[] >>
  Cases_on `dest_ArrayV (HD v)` >> simp[return_def, raise_def] >>
  Cases_on `dest_BytesV (EL 1 v)` >> simp[return_def, raise_def] >>
  rpt IF_CASES_TAC >> simp[machine_frame_def]
QED
Resume saved_walk_mutual[rawcalldata]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> rewrite_tac[ignore_bind_def] >>
  rpt (match_mp_tac machine_frame_bind >>
    conj_tac >- simp[machine_frame_primitives] >> gen_tac >> BETA_TAC) >>
  rw[state_rel_frame_def] >>
  qmatch_goalsub_abbrev_tac `SND call` >> Cases_on `call` >>
  fs[markerTheory.Abbrev_def] >>
  metis_tac[machine_frame_raw_call, pairTheory.SND]
QED

Resume saved_walk_mutual[rawcall]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >> rewrite_tac[ignore_bind_def] >>
  rpt (match_mp_tac machine_frame_bind >>
    conj_tac >- simp[machine_frame_primitives] >> gen_tac >> BETA_TAC) >>
  rw[state_rel_frame_def] >>
  qmatch_goalsub_abbrev_tac `SND call` >> Cases_on `call` >>
  fs[markerTheory.Abbrev_def] >>
  metis_tac[machine_frame_raw_call, pairTheory.SND]
QED
Resume saved_walk_mutual[extcall]:
  rpt strip_tac >> gvs[int_calls_expr_def] >> simp[Once evaluate_def] >>
  `!n. EVERY P (int_calls_exprs (TAKE n es)) /\
       EVERY P (int_calls_exprs (DROP n es))` by metis_tac[saved_walk_calls_slices] >>
  `!n. EVERY P (int_calls_exprs (TAKE n (DROP 1 es)))` by metis_tac[saved_walk_calls_slices] >>
  `!n. ~exprs_can_mutate cenv (TAKE n es) /\
       ~exprs_can_mutate cenv (DROP n es)` by
    metis_tac[saved_walk_exprs_nonmutating, EVERY_TAKE, EVERY_DROP] >>
  `!n. ~exprs_can_mutate cenv (TAKE n (DROP 1 es))` by
    metis_tac[saved_walk_exprs_nonmutating, EVERY_TAKE] >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >>
  match_mp_tac saved_walk_bind_guarded >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> BETA_TAC >>
  match_mp_tac walk_bind >> conj_tac >- metis_tac[] >>
  gen_tac >> BETA_TAC >> machine_leaf >>
  rw[state_rel_frame_def] >>
  qmatch_goalsub_abbrev_tac `SND call` >> Cases_on `call` >>
  fs[markerTheory.Abbrev_def] >>
  metis_tac[machine_frame_ext_call, pairTheory.SND]
QED

Finalise saved_walk_mutual[local]

Theorem saved_target_walk_from_calls_mods:
  (!ty key actuals fallback.
    P key /\ ~call_can_mutate cenv (IntCall key) /\
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_exprs cx actuals) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  EVERY P (int_calls_target bt) ==>
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (eval_base_place cx bt)
Proof
  metis_tac[cj 7 saved_walk_mutual]
QED

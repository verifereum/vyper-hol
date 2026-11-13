(* Access-analysis frame for the value of one queried immutable root. *)
Theory popNestedImmutableFrame
Ancestors
  popNestedImmutablePlaceOrigin popNestedImmutableMutationFrame
  vyperStorageAccessFrame vyperMachineFrame vyperEvalFrame
  vyperReadOnlyBranches vyperStatePreservation
  vyperCallOutcomeFrame vyperInterpreter vyperState vyperMisc
  vyperSubscriptOverlap list alist finite_map

val lookup = ``\cx src id (st:evaluation_state).
  FLOOKUP (case ALOOKUP st.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id``;
val frame = ``\cx src id (st:evaluation_state) st'.
  ^lookup cx src id st' = ^lookup cx src id st``;
val safe = ``\A (R:(num option # string) list) xs cs.
  (!ns. MEM (WriteAcc (StateRef ns)) xs ==> MEM (WriteAcc (StateRef ns)) A) /\
  ~MEM RiskyAcc xs /\ (!c. MEM c cs ==> MEM c R)``;
val closed = ``\cx A R.
  !ms fn ts mut nr args dflts ret body.
    MEM (ms,fn) R /\ get_module_code cx ms = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
    ^safe A R (accesses_exprs dflts ++ accesses_stmts body)
      (function_int_calls dflts body)``;

Theorem immutable_lookup_machine_frame[local]:
  machine_frame s t ==> ^frame cx src id s t
Proof
  simp[machine_frame_def]
QED

Theorem immutable_lookup_frame_machine[local]:
  state_rel_frame machine_frame f ==> state_rel_frame (^frame cx src id) f
Proof
  strip_tac >> irule state_rel_frame_machine >>
  simp[immutable_lookup_machine_frame]
QED

(* Apply only operational guards forward; semantic access guards remain goals. *)
fun immutable_guard_ih_tac (asl,w) =
  let
    fun normalise raw =
      let val th = SPEC_ALL (REWRITE_RULE [ignore_bind_def] raw) in
        if is_imp (concl th) andalso is_conj (fst (dest_imp (concl th)))
        then normalise (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th)
        else th
      end
    fun unit_var tm =
      if is_var tm andalso type_of tm = ``:unit`` then
        REWR_CONV oneTheory.one tm else NO_CONV tm
    val facts = List.concat (map (CONJUNCTS o
      REWRITE_RULE [ignore_bind_def] o CONV_RULE (DEPTH_CONV unit_var) o ASSUME)
      (List.filter (not o is_forall) asl))
    fun discharge raw =
      let val th = SPEC_ALL (normalise raw)
          val body = concl th
      in if is_imp body andalso is_eq (fst (dest_imp body)) then
           discharge (tryfind (MATCH_MP th) facts
             handle HOL_ERR _ => raise Fail ("unmatched guard: " ^
               term_to_string (fst (dest_imp body))))
         else th
      end
    fun terminal t =
      if is_forall t then terminal (snd (dest_forall t))
      else if is_imp t then terminal (snd (dest_imp t))
      else t
    val computation = rand w
    fun relevant a = is_forall a andalso
      same_const (fst (strip_comb (rand (terminal a))))
        (fst (strip_comb computation))
    val candidates = List.filter relevant asl
    val target_eqs = List.filter (fn th => is_eq (concl th) andalso
      type_of (lhs (concl th)) = ``:address``) facts
  in FIRST (map (fn a => fn g => irule
    (REWRITE_RULE target_eqs (discharge (ASSUME a))) g) candidates) (asl,w) end;

Theorem immutable_safe_accesses_drop[local]:
  !n ds A R. ^safe A R (accesses_exprs ds) (int_calls_exprs ds) ==>
    ^safe A R (accesses_exprs (DROP n ds)) (int_calls_exprs (DROP n ds))
Proof
  Induct >> Cases_on `ds` >>
  simp[accesses_expr_def, vyperTypeCallGraphTheory.int_calls_expr_def, MEM_APPEND] >>
  metis_tac[]
QED

Theorem evaluate_immutable_lookup_frame[local]:
  (!cx s. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_stmt s) (int_calls_stmt s) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_stmt cx s)) /\
  (!cx ss. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_stmts ss) (int_calls_stmts ss) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_stmts cx ss)) /\
  (!cx it. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_iterator it) (int_calls_iterator it) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_iterator cx it)) /\
  (!cx tyv nm body vs. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_stmts body) (int_calls_stmts body) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_for cx tyv nm body vs)) /\
  (!cx e. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_expr e) (int_calls_expr e) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_expr cx e)) /\
  (!cx es. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_exprs es) (int_calls_exprs es) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_exprs cx es)) /\
  (!cx bt. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_target bt) (int_calls_target bt) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_base_place cx bt)) /\
  (!cx bt. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_target bt) (int_calls_target bt) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_target_place cx bt)) /\
  (!cx g v. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_atarget g) (int_calls_atarget g) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (assign_tuple_targets cx g v)) /\
  (!cx gs vs. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_atargets gs) (int_calls_atargets gs) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (assign_tuple_target_list cx gs vs)) /\
  (!cx es. !A R src id. ^closed cx A R /\
    ^safe A R (accesses_exprs es) (int_calls_exprs es) /\
    ~MEM (WriteAcc (StateRef (src,id))) A ==>
    state_rel_frame (^frame cx src id) (eval_expr_results cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac
  >- suspend "pass" >- suspend "break" >- suspend "continue"
  >- suspend "return_none" >- suspend "return_some"
  >- suspend "raise_bare" >- suspend "raise_unreachable"
  >- suspend "raise_reason" >- suspend "raise_custom"
  >- suspend "assert_bare" >- suspend "assert_unreachable"
  >- suspend "assert_reason" >- suspend "assert_custom"
  >- suspend "log" >- suspend "annassign" >- suspend "append"
  >- suspend "assign" >- suspend "assign_tuple" >- suspend "augassign"
  >- suspend "if_stmt" >- suspend "for_stmt" >- suspend "expr_stmt"
  >- suspend "stmts_nil" >- suspend "stmts_cons"
  >- suspend "iterator_array" >- suspend "iterator_range"
  >- suspend "for_nil" >- suspend "for_cons"
  >- suspend "expr_name" >- suspend "expr_toplevel" >- suspend "expr_flag"
  >- suspend "expr_if" >- suspend "expr_literal" >- suspend "expr_struct"
  >- suspend "expr_subscript" >- suspend "expr_attribute"
  >- suspend "expr_builtin" >- suspend "expr_pop" >- suspend "expr_type_builtin"
  >- suspend "expr_send" >- suspend "expr_extcall" >- suspend "expr_intcall"
  >- suspend "expr_rawcall" >- suspend "expr_rawcalldata" >- suspend "expr_rawlog"
  >- suspend "expr_rawrevert" >- suspend "expr_selfdestruct" >- suspend "expr_create"
  >- suspend "exprs_nil" >- suspend "exprs_cons"
  >- suspend "base_name" >- suspend "base_toplevel"
  >- suspend "base_attribute" >- suspend "base_subscript"
  >- suspend "target_place" >- suspend "target_base" >- suspend "target_tuple"
  >- suspend "targets_nil" >- suspend "targets_cons"
  >- suspend "targets_error1" >- suspend "targets_error2"
  >- suspend "expr_results_nil" >> suspend "expr_results_cons"
QED

Resume evaluate_immutable_lookup_frame[pass]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, return_def]
QED

Resume evaluate_immutable_lookup_frame[break]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[continue]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[return_none]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[raise_bare]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[raise_unreachable]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[stmts_nil]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, return_def]
QED
Resume evaluate_immutable_lookup_frame[for_nil]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, return_def]
QED
Resume evaluate_immutable_lookup_frame[expr_literal]:
  rpt strip_tac >> irule immutable_lookup_frame_machine >>
  simp[Once evaluate_def, machine_frame_primitives]
QED
Resume evaluate_immutable_lookup_frame[exprs_nil]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, return_def]
QED
Resume evaluate_immutable_lookup_frame[targets_nil]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, return_def]
QED
Resume evaluate_immutable_lookup_frame[targets_error1]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[targets_error2]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, raise_def]
QED
Resume evaluate_immutable_lookup_frame[expr_results_nil]:
  rpt strip_tac >> simp[Once evaluate_def, state_rel_frame_def, return_def]
QED
Resume evaluate_immutable_lookup_frame[expr_send]:
  rpt strip_tac >> gvs[accesses_expr_def, risky_call_target_def]
QED
Resume evaluate_immutable_lookup_frame[expr_extcall]:
  rpt strip_tac >> gvs[accesses_expr_def, risky_call_target_def]
QED
Resume evaluate_immutable_lookup_frame[expr_rawcall]:
  rpt strip_tac >> gvs[accesses_expr_def, risky_call_target_def]
QED
Resume evaluate_immutable_lookup_frame[expr_rawcalldata]:
  rpt strip_tac >> gvs[accesses_expr_def, risky_call_target_def]
QED
Resume evaluate_immutable_lookup_frame[expr_create]:
  rpt strip_tac >> gvs[accesses_expr_def, risky_call_target_def]
QED
Resume evaluate_immutable_lookup_frame[base_toplevel]:
  rpt strip_tac >> irule immutable_lookup_frame_machine >>
  simp[Once evaluate_def, machine_frame_lookup_global]
QED
Resume evaluate_immutable_lookup_frame[expr_toplevel]:
  rpt strip_tac >> irule immutable_lookup_frame_machine >>
  simp[Once evaluate_def, machine_frame_reads]
QED
Resume evaluate_immutable_lookup_frame[expr_flag]:
  rpt strip_tac >> irule immutable_lookup_frame_machine >>
  simp[Once evaluate_def, machine_frame_reads]
QED

Resume evaluate_immutable_lookup_frame[return_some]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_read_result, machine_frame_primitives,
    machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[expr_name]:
  rpt strip_tac >> simp[] >> irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[evaluate_def, state_rel_frame_def, bind_def, get_scopes_def,
    type_check_def, assert_def, ignore_bind_def, return_def, raise_def, machine_frame_def] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED
Resume evaluate_immutable_lookup_frame[base_name]:
  rpt strip_tac >> simp[] >> irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[evaluate_def, state_rel_frame_def, bind_def, get_scopes_def,
    type_check_def, assert_def, ignore_bind_def, return_def, raise_def, machine_frame_def] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED
Resume evaluate_immutable_lookup_frame[expr_stmt]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[machine_frame_primitives]
QED
Resume evaluate_immutable_lookup_frame[iterator_array]:
  rpt strip_tac >> gvs[accesses_iterator_def,
    vyperTypeCallGraphTheory.int_calls_iterator_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[machine_frame_array_iterator_results]
QED

Resume evaluate_immutable_lookup_frame[exprs_cons]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >>
      simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> conj_tac
      >- (qexistsl [`A`, `R`] >> metis_tac[]) >> metis_tac[]) >>
  simp[state_rel_frame_def, return_def]
QED
Resume evaluate_immutable_lookup_frame[stmts_cons]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  Cases_on `v` >> gvs[] >>
  first_x_assum irule >> conj_tac
  >- (qexistsl [`A`, `R`] >> metis_tac[]) >> metis_tac[]
QED
Resume evaluate_immutable_lookup_frame[expr_results_cons]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> conj_tac
      >- (qexistsl [`A`, `R`] >> metis_tac[]) >> metis_tac[]) >>
  simp[state_rel_frame_def, return_def]
QED


Resume evaluate_immutable_lookup_frame[expr_attribute]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[machine_frame_select_result]
QED
Resume evaluate_immutable_lookup_frame[base_attribute]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[machine_frame_extend_place]
QED

Resume evaluate_immutable_lookup_frame[expr_subscript]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> conj_tac
      >- (qexistsl [`A`, `R`] >> metis_tac[]) >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result, machine_frame_select_result]
QED
Resume evaluate_immutable_lookup_frame[base_subscript]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> conj_tac
      >- (qexistsl [`A`, `R`] >> metis_tac[]) >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_def, machine_frame_read_result, machine_frame_extend_place]
QED

Resume evaluate_immutable_lookup_frame[target_place]:
  rpt strip_tac >> gvs[] >> simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_get_place]
QED
Resume evaluate_immutable_lookup_frame[target_tuple]:
  rpt strip_tac >> gvs[] >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[state_rel_frame_def, raise_def] >>
  Cases_on `a` >> simp[state_rel_frame_def, raise_def] >>
  gvs[accesses_atarget_def, vyperTypeCallGraphTheory.int_calls_atarget_def,
    state_rel_frame_def] >>
  first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[expr_pop]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  `!path. v <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >> drule eval_target_place_immutable_access >> metis_tac[]) >>
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule (BETA_RULE pop_place_unwritten_immutable) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume evaluate_immutable_lookup_frame[target_base]:
  rpt strip_tac >> gvs[accesses_atarget_def,
    vyperTypeCallGraphTheory.int_calls_atarget_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  `!path. v' <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >> drule eval_target_place_immutable_access >> metis_tac[]) >>
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule (BETA_RULE write_place_unwritten_immutable) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume evaluate_immutable_lookup_frame[targets_cons]:
  rpt strip_tac >> gvs[accesses_atarget_def,
    vyperTypeCallGraphTheory.int_calls_atarget_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >> Cases_on `v'` >> gvs[] >>
  first_x_assum irule >> conj_tac
  >- (qexistsl [`A`, `R`] >> metis_tac[]) >> metis_tac[]
QED
Resume evaluate_immutable_lookup_frame[expr_struct]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperLocalAccessFrameTheory.accesses_named_exprs_map,
    GSYM vyperTypeEvalSoundnessTheory.int_calls_exprs_MAP_SND,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  simp[state_rel_frame_def, return_def]
QED

Resume evaluate_immutable_lookup_frame[expr_intcall]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!c. c = _ \/ _ ==> _` irule >> simp[]) >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!ns. (_ \/ _) \/ _ ==> _` irule >> simp[]) >> simp[]) >>
  suspend "call_after_args"
QED

Resume evaluate_immutable_lookup_frame[call_after_args]:
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (match_mp_tac state_rel_frame_finally >>
      conj_tac >- metis_tac[] >> reverse conj_tac
      >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
      simp[ignore_bind_def] >> match_mp_tac state_rel_frame_bind_guarded >>
      conj_tac >- metis_tac[] >> conj_tac
      >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
      rpt strip_tac >> simp[] >> immutable_guard_ih_tac >>
      suspend "call_defaults_semantic") >>
  suspend "call_after_defaults"
QED

Resume evaluate_immutable_lookup_frame[call_defaults_semantic]:
  `MEM (src_id_opt,fn) R` by simp[] >>
  qpat_assum `lift_option_type (get_module_code _ _) _ _ = _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeEvalSoundnessTheory.lift_option_type_INL_eq]) >>
  qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeEvalSoundnessTheory.lift_option_type_INL_eq]) >>
  PairCases_on `v''` >>
  qpat_assum `!ms fn' ts mut nr args dflts ret body. _` drule >>
  disch_then drule >> disch_then drule >>
  simp[vyperTypeCallGraphTheory.function_int_calls_def] >> strip_tac >>
  `^safe A R (accesses_exprs v''3) (int_calls_exprs v''3)` by
    (simp[] >> metis_tac[]) >>
  drule immutable_safe_accesses_drop >>
  disch_then (qspec_then `LENGTH v''3 - (LENGTH v''2 - LENGTH es)` (strip_assume_tac o BETA_RULE)) >>
  conj_tac >- first_assum ACCEPT_TAC >> qexistsl [`A`, `R`] >>
  reverse (rpt conj_tac) >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  simp[vyperContextTheory.get_module_code_def] >>
  qpat_assum `!ms fn' ts mut nr args dflts ret body. _` mp_tac >>
  simp[vyperTypeCallGraphTheory.function_int_calls_def,
    vyperContextTheory.get_module_code_def]
QED

Resume evaluate_immutable_lookup_frame[call_after_defaults]:
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> irule machine_frame_read_results) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  suspend "call_lock"
QED

Resume evaluate_immutable_lookup_frame[call_lock]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (Cases_on `FST (SND v'')` >> simp[]
      >- (Cases_on `cx.nonreentrant_slot`
          >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
          simp[ignore_bind_def] >> match_mp_tac state_rel_frame_bind_guarded >>
          conj_tac >- metis_tac[] >> conj_tac
          >- (simp[state_rel_frame_def] >> gen_tac >>
              Cases_on `acquire_nonreentrant_lock cx.txn.target x
                ((FST v'' = View \/ FST v'' = Pure) \/ cx.txn.is_static) st` >>
              drule acquire_nonreentrant_lock_immutables >> simp[]) >>
          rpt strip_tac >> simp[] >>
          irule (BETA_RULE immutable_lookup_frame_machine) >>
          Cases_on `FST v'' = View \/ FST v'' = Pure` >>
          simp[check_not_static_def, machine_frame_primitives]) >>
      irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> irule machine_frame_push_function) >>
  rpt strip_tac >> simp[] >> suspend "call_body_cleanup"
QED

Resume evaluate_immutable_lookup_frame[call_body_cleanup]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (match_mp_tac state_rel_frame_finally_unless_halt >>
      conj_tac >- metis_tac[] >> reverse conj_tac
      >- (Cases_on `FST (SND v'') /\ FST v'' <> View /\ FST v'' <> Pure` >> simp[]
          >- (Cases_on `cx.nonreentrant_slot` >> simp[]
              >- simp[state_rel_frame_def, return_def] >>
              simp[state_rel_frame_def] >> gen_tac >>
              Cases_on `release_nonreentrant_lock cx.txn.target x st` >>
              drule release_nonreentrant_lock_immutables >> simp[]) >>
          simp[state_rel_frame_def, return_def]) >>
      match_mp_tac state_rel_frame_finally >>
      conj_tac >- metis_tac[] >> reverse conj_tac
      >- (irule (BETA_RULE immutable_lookup_frame_machine) >> irule machine_frame_pop_function) >>
      match_mp_tac state_rel_frame_try >>
      conj_tac >- metis_tac[] >> reverse conj_tac
      >- (gen_tac >> irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_handlers]) >>
      simp[ignore_bind_def] >> match_mp_tac state_rel_frame_bind_guarded >>
      conj_tac >- metis_tac[] >> reverse conj_tac
      >- (simp[state_rel_frame_def, return_def]) >>
      rename1 `push_function _ _ _ _ = (INL cxf,_)` >>
      `cxf.txn.target = cx.txn.target` by
        (qpat_x_assum `push_function _ _ _ _ = _` mp_tac >>
         simp[push_function_def, return_def] >>
         disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[]) >>
      immutable_guard_ih_tac >> suspend "call_body_semantic") >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  simp[state_rel_frame_def, return_def]
QED

Resume evaluate_immutable_lookup_frame[call_body_semantic]:
  `MEM (src_id_opt,fn) R` by simp[] >>
  qpat_assum `lift_option_type (get_module_code _ _) _ _ = _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeEvalSoundnessTheory.lift_option_type_INL_eq]) >>
  qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeEvalSoundnessTheory.lift_option_type_INL_eq]) >>
  PairCases_on `v''` >>
  qpat_assum `!ms fn' ts mut nr args dflts ret body. _` drule >>
  disch_then drule >> disch_then drule >>
  simp[vyperTypeCallGraphTheory.function_int_calls_def] >> strip_tac >>
  qexistsl [`A`, `R`] >>
  reverse (rpt conj_tac)
  >- first_assum ACCEPT_TAC >- simp[] >- simp[] >>
  qpat_assum `push_function _ _ _ _ = _`
    (SUBST1_TAC o SYM o CONJUNCT1 o REWRITE_RULE [push_function_def, return_def, pairTheory.PAIR_EQ, sumTheory.INL_11]) >>
  simp[vyperContextTheory.get_module_code_def] >>
  qpat_assum `!ms fn' ts mut nr args dflts ret body. _` mp_tac >>
  simp[vyperContextTheory.get_module_code_def, vyperTypeCallGraphTheory.function_int_calls_def]
QED

Resume evaluate_immutable_lookup_frame[expr_rawlog]:
  rpt strip_tac >> gvs[accesses_expr_def, risky_call_target_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >> suspend "rawlog_tail"
QED

Resume evaluate_immutable_lookup_frame[rawlog_tail]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  simp[ignore_bind_def, check_not_static_def] >>
  rpt (BETA_TAC >> match_mp_tac state_rel_frame_bind_guarded >>
    conj_tac >- metis_tac[] >> conj_tac
    >- (irule (BETA_RULE immutable_lookup_frame_machine) >>
        simp[machine_frame_primitives]) >> rpt strip_tac >> simp[]) >>
  simp[state_rel_frame_def, bind_def, push_log_def, return_def]
QED

Resume evaluate_immutable_lookup_frame[expr_rawrevert]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac machine_frame_bind >> conj_tac
    >- simp[machine_frame_primitives] >> gen_tac) >>
  simp[machine_frame_primitives]
QED

Resume evaluate_immutable_lookup_frame[expr_selfdestruct]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >> suspend "selfdestruct_tail"
QED
Resume evaluate_immutable_lookup_frame[selfdestruct_tail]:
  simp[ignore_bind_def, check_not_static_def] >>
  rpt (BETA_TAC >> match_mp_tac state_rel_frame_bind_guarded >>
    conj_tac >- metis_tac[] >> conj_tac
    >- (irule (BETA_RULE immutable_lookup_frame_machine) >>
        simp[machine_frame_primitives]) >> rpt strip_tac >> simp[]) >>
  suspend "selfdestruct_transfer"
QED

Resume evaluate_immutable_lookup_frame[selfdestruct_transfer]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (simp[state_rel_frame_def] >> gen_tac >>
      qmatch_goalsub_abbrev_tac `SND tr` >>
      Cases_on `tr` >> fs[markerTheory.Abbrev_def] >>
      qpat_x_assum `(_,_) = transfer_value _ _ _ _` (assume_tac o SYM) >>
      drule transfer_value_immutables >> simp[]) >>
  rpt strip_tac >> simp[] >>
  Cases_on `cx.txn.created_in_tx` >>
  simp[state_rel_frame_def, bind_def, update_accounts_def,
    update_pending_deletions_def, return_def, raise_def, ignore_bind_def]
QED

Resume evaluate_immutable_lookup_frame[expr_if]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >> suspend "expr_if_tail"
QED
Resume evaluate_immutable_lookup_frame[expr_if_tail]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> reverse conj_tac
  >- (rpt strip_tac >> simp[] >>
      irule (BETA_RULE immutable_lookup_frame_machine) >>
      simp[state_rel_frame_def] >> gen_tac >>
      qmatch_goalsub_abbrev_tac `SND cr` >> Cases_on `cr` >>
      fs[markerTheory.Abbrev_def] >>
      qpat_x_assum `(_,_) = conditional_result _ _ _` (mp_tac o SYM) >>
      disch_then (mp_tac o MATCH_MP conditional_result_state) >>
      simp[machine_frame_def]) >>
  simp[switch_BoolV_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >> suspend "expr_if_switch"
QED

Resume evaluate_immutable_lookup_frame[expr_if_switch]:
  Cases_on `v'` >> simp[] >>~-
  ([`state_rel_frame _ (raise _)`], simp[state_rel_frame_def, raise_def]) >>
  Cases_on `b` >> simp[] >> immutable_guard_ih_tac >>
  qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[raise_reason]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_raise_reason_def,
    vyperTypeCallGraphTheory.int_calls_raise_reason_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_read_result] >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[expr_type_builtin]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[assert_bare]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_assert_reason_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def,
    vyperTypeCallGraphTheory.int_calls_assert_reason_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[switch_BoolV_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_read_result] >>
  rpt strip_tac >> simp[] >> Cases_on `v'` >>
  simp[state_rel_frame_def, return_def, raise_def, machine_frame_def] >>
  Cases_on `b` >> simp[return_def, raise_def, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[assert_unreachable]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_assert_reason_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def,
    vyperTypeCallGraphTheory.int_calls_assert_reason_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[switch_BoolV_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_read_result] >>
  rpt strip_tac >> simp[] >> Cases_on `v'` >>
  simp[state_rel_frame_def, return_def, raise_def, machine_frame_def] >>
  Cases_on `b` >> simp[return_def, raise_def, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[annassign]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_read_result, machine_frame_new_variable, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[assign_tuple]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[iterator_range]:
  rpt strip_tac >> gvs[accesses_iterator_def,
    vyperTypeCallGraphTheory.int_calls_iterator_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_read_result] >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[append]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  `!path. v <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >> drule eval_target_place_immutable_access >> metis_tac[]) >>
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule (BETA_RULE append_place_unwritten_immutable) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume evaluate_immutable_lookup_frame[assign]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_atarget_def,
    vyperTypeCallGraphTheory.int_calls_atarget_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  `!path. v'' <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >> drule eval_target_place_immutable_access >> metis_tac[]) >>
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule (BETA_RULE write_place_unwritten_immutable) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume evaluate_immutable_lookup_frame[log]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >>
      simp[check_not_static_def, machine_frame_primitives]) >>
  rpt strip_tac >> simp[state_rel_frame_def, push_log_def, return_def]
QED

Resume evaluate_immutable_lookup_frame[augassign]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_place]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_place_type_value]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >> suspend "augassign_tail"
QED

Resume evaluate_immutable_lookup_frame[augassign_tail]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  `!path. v <> ImmutablePlace src id path` by
    (rpt strip_tac >> gvs[] >> drule eval_target_place_immutable_access >> metis_tac[]) >>
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule (BETA_RULE write_place_unwritten_immutable) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume evaluate_immutable_lookup_frame[for_stmt]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[if_stmt]:
  rpt strip_tac >> gvs[accesses_stmt_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_scopes, machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_finally >>
  conj_tac >- metis_tac[] >> reverse conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_scopes, machine_frame_primitives]) >>
  simp[switch_BoolV_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >> Cases_on `v''` >> simp[] >>~-
  ([`state_rel_frame _ (raise _)`], simp[state_rel_frame_def, raise_def]) >>
  Cases_on `b` >> simp[] >> immutable_guard_ih_tac >>
  qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[for_cons]:
  rpt strip_tac >> gvs[] >> simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- suspend "for_cons_body" >>
  rpt strip_tac >> simp[] >> IF_CASES_TAC
  >- simp[state_rel_frame_def, return_def] >>
  gvs[] >> immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[for_cons_body]:
  match_mp_tac state_rel_frame_finally >>
  conj_tac >- metis_tac[] >> reverse conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  match_mp_tac state_rel_frame_try >>
  conj_tac >- metis_tac[] >> reverse conj_tac
  >- (gen_tac >> irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_handlers]) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> reverse conj_tac
  >- simp[state_rel_frame_def, return_def] >>
  immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[assert_reason]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_assert_reason_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def,
    vyperTypeCallGraphTheory.int_calls_assert_reason_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[switch_BoolV_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >> Cases_on `v'` >> simp[] >>~-
  ([`state_rel_frame _ (raise _)`], simp[state_rel_frame_def, raise_def]) >>
  Cases_on `b` >> simp[]
  >- simp[state_rel_frame_def, return_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_read_result] >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[raise_custom]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_raise_reason_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def,
    vyperTypeCallGraphTheory.int_calls_raise_reason_def] >>
  Cases_on `err` >> simp[Once evaluate_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[] >>~-
  ([`state_rel_frame _ (raise _)`], simp[state_rel_frame_def, raise_def]) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- suspend "raise_custom_access" >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[raise_custom_access]:
  gvs[] >> immutable_guard_ih_tac >>
  gvs[vyperASTTheory.order_custom_error_args_def,
    vyperASTTheory.custom_error_exprs_def, AllCaseEqs()] >>
  imp_res_tac vyperASTTheory.order_custom_error_kwargs_SOME >> gvs[NULL_EQ] >>
  qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[assert_custom]:
  rpt strip_tac >> gvs[accesses_stmt_def, accesses_assert_reason_def,
    vyperTypeCallGraphTheory.int_calls_stmt_def,
    vyperTypeCallGraphTheory.int_calls_assert_reason_def] >>
  simp[Once evaluate_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (first_x_assum irule >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[switch_BoolV_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_read_result]) >>
  rpt strip_tac >> simp[] >> Cases_on `v'` >> simp[] >>~-
  ([`state_rel_frame _ (raise _)`], simp[state_rel_frame_def, raise_def]) >>
  Cases_on `b` >> simp[] >>~-
  ([`state_rel_frame _ (return _)`], simp[state_rel_frame_def, return_def]) >>
  Cases_on `err` >> rpt BasicProvers.TOP_CASE_TAC >> simp[] >>~-
  ([`state_rel_frame _ (raise _)`], simp[state_rel_frame_def, raise_def]) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- suspend "assert_custom_access" >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[assert_custom_access]:
  gvs[] >> immutable_guard_ih_tac >>
  gvs[vyperASTTheory.order_custom_error_args_def,
    vyperASTTheory.custom_error_exprs_def, AllCaseEqs()] >>
  imp_res_tac vyperASTTheory.order_custom_error_kwargs_SOME >> gvs[NULL_EQ] >>
  qexistsl [`A`, `R`] >> metis_tac[]
QED

Resume evaluate_immutable_lookup_frame[expr_builtin]:
  rpt strip_tac >> gvs[accesses_expr_def,
    vyperTypeCallGraphTheory.int_calls_expr_def] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (irule (BETA_RULE immutable_lookup_frame_machine) >> simp[machine_frame_primitives]) >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> reverse conj_tac
  >- simp[state_rel_frame_def, return_def] >>
  Cases_on `bt = Len` >- suspend "builtin_len" >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn` >- suspend "builtin_membership" >>
  Cases_on `bt = Env MsgGas` >- suspend "builtin_gas" >>
  simp[] >> suspend "builtin_general"
QED

Resume evaluate_immutable_lookup_frame[builtin_len]:
  gvs[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (immutable_guard_ih_tac >> suspend "builtin_len_access") >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_reads, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[builtin_gas]:
  gvs[] >> irule (BETA_RULE immutable_lookup_frame_machine) >>
  simp[machine_frame_next_gas_reading]
QED

Resume evaluate_immutable_lookup_frame[builtin_membership]:
  simp[] >> match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (gvs[] >> immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_primitives] >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[builtin_general]:
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (gvs[] >> immutable_guard_ih_tac >> qexistsl [`A`, `R`] >> metis_tac[]) >>
  rpt strip_tac >> simp[] >>
  irule (BETA_RULE immutable_lookup_frame_machine) >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_primitives] >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  conj_tac >- simp[machine_frame_def] >> conj_tac
  >- simp[machine_frame_primitives] >>
  rpt strip_tac >> simp[] >>
  match_mp_tac state_rel_frame_bind_guarded >>
  simp[machine_frame_primitives, machine_frame_precompile_call_success, machine_frame_def]
QED

Resume evaluate_immutable_lookup_frame[builtin_len_access]:
  gvs[type_check_def, assert_def, bind_def, ignore_bind_def,
    return_def, raise_def, AllCaseEqs()] >>
  Cases_on `es` >> gvs[vyperContextTheory.builtin_args_length_ok_def] >>
  gvs[accesses_expr_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  qexistsl [`A`, `R`] >> metis_tac[]
QED

Finalise evaluate_immutable_lookup_frame

Theorem eval_expr_unwritten_immutable:
  !cx e st res st' env mods src id.
    eval_expr cx e st = (res,st') /\
    well_typed_expr env e /\ env_consistent env cx st /\
    state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    (!ms fn ts mut nr args dflts ret body.
       MEM (ms,fn) (reached_functions mods e) /\
       get_module_code cx ms = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts =
         SOME (mut,nr,args,dflts,ret,body) ==>
       ALOOKUP mods ms = SOME ts /\
       (find_function fn ts = SOME (dflts,body) \/
        (dflts = [] /\ body = []))) /\
    ~MEM RiskyAcc (expr_accesses mods e) /\
    ~MEM (WriteAcc (StateRef (src,id))) (expr_accesses mods e) ==>
    ^lookup cx src id st' = ^lookup cx src id st
Proof
  rpt strip_tac >>
  drule_all callable_closed_initial >> strip_tac >>
  drule safe_accesses_expr_initial >> strip_tac >>
  `state_rel_frame (^frame cx src id) (eval_expr cx e)` by
    (BETA_TAC >> irule (BETA_RULE (cj 5 evaluate_immutable_lookup_frame)) >>
     conj_tac >- gvs[] >>
     qexistsl [`expr_accesses mods e`, `reached_functions mods e`] >>
     gvs[] >> metis_tac[]) >>
  gvs[state_rel_frame_def] >> first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

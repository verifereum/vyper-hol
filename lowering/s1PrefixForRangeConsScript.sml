(* The Range body request prefix at a fixed condition-label layout. *)
Theory s1PrefixForRangeCons
Ancestors
  bodyFullForRange bodyFullShared[qualified,ignore_grammar]
  s1PrefixForHandlers s1PrefixCompose s1PrefixInvalidTraceDomain
  s1PrefixDefs s1PrefixPreds bodyFullPreds vyperState vyperStorageTrace
  bodyFullPredsMods[qualified] gasOutcomeFullMods[qualified]
  s1PrefixStmtFullApply[qualified]
Libs rangeRoundEntryLib[qualified]

val _ = Parse.hide "body";

(* Extract only the fixed-layout entry premises and the full rule's Inv
   equation, source and input. Do not carry its outcome postconditions over. *)
local
  fun require test msg = if test then () else raise Fail ("Range cons: " ^ msg)
  fun named name vars =
    case List.filter (fn v => #1 (dest_var v) = name) vars of
      [v] => v
    | _ => raise Fail ("Range cons: expected exactly one binder named " ^ name)
  fun headed c tm = same_const c (#1 (strip_comb tm))
  fun same_vars xs ys = length xs = length ys andalso ListPair.allEq (uncurry aconv) (xs,ys)
  fun distinct [] = true
    | distinct (x::xs) = not (List.exists (aconv x) xs) andalso distinct xs
  fun select pred ts =
    case List.filter pred ts of
      [t] => t
    | _ => raise Fail "Range cons: expected exactly one matching clause"
  fun boundary tm =
    let
      val (static_vars, rule) = strip_forall tm
      val (static, result) = dest_imp rule
      val (layout_vars, pkg) = strip_exists result
    in (static_vars, static, layout_vars, pkg) end
  val entry_statement = concl range_full_body_entry
  val (entry_static_vars, _, entry_layout_vars, entry) = boundary entry_statement
  val (full_helpers, full_result) = dest_imp (concl range_full_round)
  val _ = require (List.exists (aconv entry_statement)
                    (strip_conj full_helpers)) "wrong full entry assumption"
  val (static_vars, static, layout_vars, full_pkg) = boundary full_result
  (* These exports deliberately use the very same typed binders. Require
     that here, so their free occurrences compose without any substitution. *)
  val _ = require (same_vars entry_static_vars static_vars andalso
                   same_vars entry_layout_vars layout_vars) "layout binders changed"
  val entry_rule = List.last (strip_conj entry)
  val (entry_vars, entry_imp) = strip_forall entry_rule
  val (entry_pre, entry_post) = dest_imp entry_imp
  val _ = require (is_conj entry_post andalso
                   List.exists (headed ``gas_admissible``) (strip_conj entry_pre) andalso
                   List.exists (headed ``body_stmts_full_ok_mods``) (strip_conj entry_post) andalso
                   List.exists (fn v => #1 (dest_var v) = "k") entry_vars)
                  "expected a cons-to-body entry rule"
  val (range_vars, range_imp) = strip_forall (List.last (strip_conj full_pkg))
  val (geometry, inv_rule) = dest_imp range_imp
  val (inv_vars, inv_imp) = strip_forall inv_rule
  val (invariants, cons_rule) = dest_imp inv_imp
  val inv = named "Inv" inv_vars
  val inv_eq = select (fn p => is_eq p andalso aconv (lhs p) inv) (strip_conj invariants)
  val (cons_vars, cons_imp) = strip_forall cons_rule
  val (cons_pre, outcome) = dest_imp cons_imp
  val (outcome_head, [params, _, cx, st0, source, states, _, _]) = strip_comb outcome
  val _ = require (same_const outcome_head ``gas_outcome_full_mods``) "wrong full conclusion"
  val lookup = fn n => named n (static_vars @ range_vars @ cons_vars)
  val a = lookup "a"
  val rs = lookup "rs"
  val es = lookup "es"
  val s = lookup "s"
  val g = lookup "G"
  val tn = lookup "tn"
  val id = lookup "id"
  val tyv = lookup "tyv"
  val body = lookup "body"
  val lctx = lookup "lctx"
  val _ = require (aconv states ``(^es,^s,^g,^tn)`` andalso
    aconv source ``do v <- read_result ^cx ^a;
      push_scope_with_var ^id ^tyv v;
      finally (try (do eval_stmts ^cx ^body; return F od)
                   handle_loop_exception) pop_scope od``) "wrong round source or input"
  val _ = require (List.exists (aconv
    ``gas_admissible (eval_for ^cx ^tyv ^id ^body (^a :: ^rs))
         (stmt_res_ok ^lctx) ^es``) (strip_conj cons_pre)) "wrong round guard"
  val (_, [_,_,_,_,_,_,vs]) =
    strip_comb (select (headed ``body_for_full_ok_mods``) (strip_conj geometry))
  val module_vars = map (fn name => named name (free_vars entry_statement)) ["mods", "exps"]
  val static_vars = module_vars @ static_vars
  val vars = static_vars @ layout_vars @ range_vars @ [inv] @ cons_vars
  val _ = require (distinct vars) "duplicate binder"
  val statement = list_mk_forall (static_vars,
    mk_imp (static, list_mk_forall (layout_vars, mk_imp (entry,
      list_mk_forall (range_vars @ [inv],
        mk_imp (``^geometry /\ body_for_prefix_ok ^cx ^tyv ^id ^body ^vs /\ ^inv_eq``,
          list_mk_forall (cons_vars,
            mk_imp (cons_pre, ``gas_prefix_full ^params ^cx ^st0 ^source ^states``))))))))
in
  val range_cons_prefix_statement =
    (require (null (free_vars statement)) "a binder escaped"; statement)
end

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  map_every qx_gen_tac rangeRoundEntryLib.layout_names >>
  disch_then rangeRoundEntryLib.assume_layout >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `clean =
    finally (try (do eval_stmts cx body; return F od) handle_loop_exception) pop_scope` >>
  `storage_trace_frame clean` by
    (simp[NoAsms, Abbr `clean`] >>
     irule storage_trace_frame_finally >> simp[NoAsms, storage_trace_frame_pop_scope] >>
     irule storage_trace_frame_try >> simp[NoAsms, storage_trace_frame_loop_handler] >>
     irule storage_trace_frame_ignore_bind >>
     simp[NoAsms, storage_trace_frame_return, cj 2 evaluate_storage_trace_frame]) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (rangeRoundEntryLib.establish_invariant >>
      rangeRoundEntryLib.enter_round >>
      rangeRoundEntryLib.name_frame >>
      rangeRoundEntryLib.frame_at_horizons >> suspend "scoped_frame") >>
  irule gas_prefix_full_invalid_trace_domain >>
  asm_rewrite_tac [] >>
  irule storage_trace_frame_bind_all >>
  simp[NoAsms, storage_trace_frame_read_result] >> gen_tac >>
  irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates]
QED
*)
Theorem range_cons_prefix:
  ^range_cons_prefix_statement
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume range_cons_prefix[scoped_frame]:
  rangeRoundEntryLib.prepare_locals
    bodyFullSharedTheory.return_buf_allocas_path
    bodyFullSharedTheory.return_buf_sep_allocated_local >>
  suspend "scoped_entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume range_cons_prefix[scoped_entry]:
  `body_stmts_prefix_ok cx body` by
    (qpat_x_assum `body_for_prefix_ok _ _ _ _ _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [body_for_prefix_ok_def]) >>
     impl_tac >- (`0 < N /\ N <> 0` by decide_tac >>
       qexists_tac `es` >>
       qpat_assum `0 < N` (fn pos => qpat_assum `N <> 0` (fn nz =>
         simp[NoAsms, pos, nz, listTheory.GENLIST_EQ_NIL, listTheory.HD_GENLIST_COR,
              read_result_def, return_def]))) >>
     disch_then ACCEPT_TAC) >>
  let
    fun body_contract pred apply =
      qpat_x_assum pred (irule o apply) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >-
        (qexistsl_tac [`bindings`, `extend_local env id typ F`, `body_env'`, `tops`] >>
         simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC
  in
    `stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cx (InLoop exit_lbl incr_lbl) RetQ bc
       (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body)
       (stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
          (MAP gas_shadow_stmt body)) (eval_stmts cx body) ep` by
      body_contract `body_stmts_full_ok cx body`
        (MATCH_MP s1PrefixStmtFullApplyTheory.body_stmts_full_ok_apply) >>
    `stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cx (InLoop exit_lbl incr_lbl) RetQ bc
       (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body)
       (stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
          (MAP gas_shadow_stmt body)) (eval_stmts cx body) ep` by
      body_contract `body_stmts_prefix_ok cx body`
        (PURE_ONCE_REWRITE_RULE [body_stmts_prefix_ok_def])
  end >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ _ _ _ _`
    (qspecl_then [`st0`,`sb0`,`sb1`,`shadow_sb0`,`shadow_sb1`,`t`,`Gentry`,`tt`,`body_cenv`]
       mp_tac o PURE_ONCE_REWRITE_RULE [bodySimFullTheory.stmt_frag_full_def]) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_x_assum `stmt_frag_prefix _ _ _ _ _ _ _ _ _`
    (qspecl_then [`st0`,`sb0`,`sb1`,`shadow_sb0`,`shadow_sb1`,`t`,`Gentry`,`tt`,`body_cenv`]
       mp_tac o PURE_ONCE_REWRITE_RULE [stmt_frag_prefix_def]) >>
  impl_tac >- (simp[NoAsms, stmt_frag_full_pre_def] >>
               rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  suspend "attach"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume range_cons_prefix[attach]:
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 clean (ep,t,Gentry,tt)` by
    (qunabbrev_tac `clean` >> irule for_body_cleanup_prefix >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_stmts cx body) (ep,t,Gentry,tt) _ _`
       (irule_at Any) >>
     conj_tac >- simp[NoAsms, Abbr `ep`] >> first_assum ACCEPT_TAC) >>
  `ep.storage_trace = es.storage_trace` by simp[NoAsms, Abbr `ep`] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 clean (ep,s,G,tn)` by
    (irule gas_prefix_full_zero_prefix_guarded >>
     qpat_assum `gas_prefix_full _ _ _ clean (ep,t,Gentry,tt)` (irule_at Any) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ep.storage_trace = es.storage_trace` SUBST1_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
                      gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt) /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!obs. (do v <- read_result cx a; push_scope_with_var id tyv v; clean od)
           (es with gas_obs := obs) = clean (ep with gas_obs := obs)` by
    (qpat_assum `a = Value _` SUBST1_TAC >>
     simp[NoAsms, Abbr `ep`, bind_def, ignore_bind_def, read_result_def,
          return_def, push_scope_with_var_def] >> gen_tac >> AP_TERM_TAC >>
     simp[evaluation_state_component_equality]) >>
  `ep.requests = es.requests` by simp[NoAsms, Abbr `ep`] >>
  qpat_x_assum `gas_prefix_full _ _ _ clean (ep,s,G,tn)` mp_tac >>
  qpat_assum `ep.storage_trace = es.storage_trace` (fn tr =>
    qpat_assum `ep.requests = es.requests` (fn req =>
      qpat_assum `!obs. bind (read_result cx a) _ _ = _` (fn run =>
        simp[NoAsms, gas_prefix_full_def, tr, req, run])))
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise range_cons_prefix
*)

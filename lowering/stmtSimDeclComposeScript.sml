(* Full-post continuation boundaries for counted declarations. *)
Theory stmtSimDeclCompose
Ancestors
  stmtSimDeclPath stmtSimDeclGas stmtSimDeclSource gasSummary
  gasSummaryCompose gasOutcome gasExemptCert fragGasMode
  stmtSimDefs exprSimDefs loweringPosts vyperInterpreter vyperState
  venomState compileEnv loweringStateRelDefs valueEncoding list finite_map stmtLowering
  emitHelperProps exprLoweringProps fragGasPath stmtSimProps
Libs monadsyntax

Theorem annassign_store_continuation:
  !ctx func old cenv cx lctx e es es1 s0 s sa sb sf op id p sz w inst
    v etv tyv sc rest.
    expr_post ctx func cenv cx e es sa sb s0 es1 v op s /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    store_lays_out etv tyv v /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\ fn_inst_ids_distinct func /\
    es1.scopes = sc :: rest /\ lookup_scopes id es1.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es1.scopes p /\ not_fresh_at sa p /\
    lookup_var p s0 = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s0.vs_allocas inst.inst_id = SOME (w2n w, sz) /\ 32 <= sz /\
    ~block_is_terminated sf /\
    cenv_top_ext old cenv
      ((sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) /\
    (!tail. new_variable id tyv v (es1 with gas_obs := tail) =
      (INL (), (es1 with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
        with gas_obs := tail)) ==>
    ?ee t.
      gas_marked_exec F (ctx,func) (new_variable id tyv v) (es1,s)
        [] (INL ()) ee (OK t) /\
      stmt_post ctx func cx lctx old cenv sa sf s0 (INL ()) ee t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_word_store_post_path >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  qexistsl_tac [`es1 with scopes :=
    (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`, `t`] >>
  conj_tac
  >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def] >>
  qexists_tac `cenv` >> simp[]
QED

Theorem gas_marked_exec_end_gas_obs:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r ==>
  gas_marked_exec memory (ctx,func) source (es,s0) marks res
    (ee with gas_obs := gs) r
Proof
  simp[gas_marked_exec_def]
QED

Theorem annassign_rhs_outcome:
  !ctx func cx lctx RetQ id typ tyv es salloc old c sa sf s0 Q.
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,salloc) Q
      (\res ee r. expr_exit res r) /\
    (!res ee t. Q res ee t ==> ?v. res = INL v) /\
    (!marks v ee t.
      gas_marked_exec F (ctx,func)
        (bind (eval_expr cx e) (read_result cx)) (es,salloc)
        marks (INL v) ee (OK t) /\
      Q (INL v) (ee with gas_obs := []) t ==>
      ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
        stmt_post ctx func cx lctx old c sa sf s0 (INL ())
          (ff with gas_obs := []) u) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,salloc)
      (stmt_post ctx func cx lctx old c sa sf s0)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule eval_annassign_action >>
      disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
      >- (gvs[] >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          qpat_x_assum `!marks v ee t. _` (drule_then mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end with gas_obs := []`, `t`, `v`] >>
          simp[] >> irule gas_marked_exec_end_gas_obs >> simp[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> gen_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  simp[ignore_bind_def]
QED

Theorem cenv_top_ext_declare_local:
  !cenv id ty st c st1 sc rest.
    declare_local cenv id ty st = (c, st1) /\ cenv.ce_alloca_locals /\
    lookup_scopes id rest = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) ==>
    cenv_top_ext cenv c (sc :: rest)
Proof
  rpt strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  simp[cenv_top_ext_def] >> rpt strip_tac >>
  `n = id` by metis_tac[] >> gvs[]
QED

Theorem annassign_normal_continuation:
  !ctx func old c cx lctx id typ tyv e es etv sa0 st sa sb sf salloc
    marks v ee s op p sz w inst.
    declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
    (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==> store_lays_out etv tyv v) /\
    local_ptrs_reserved c sa /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\ 32 <= sz /\
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,salloc) marks (INL v) ee (OK s) /\
    expr_post ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op s /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
      (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
      stmt_post ctx func cx lctx old c sa sf salloc (INL ()) ff u
Proof
  rpt gen_tac >> strip_tac >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks salloc.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  `store_lays_out etv tyv v` by
    (first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  `not_local_ptr c (ee with gas_obs := []).scopes p` by
    (irule local_ptrs_reserved_not_live >> simp[] >> metis_tac[]) >>
  `cenv_top_ext old c
    ((sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)` by
    (irule cenv_top_ext_declare_local >> simp[] >>
     qexistsl_tac [`id`, `sa0`, `st`, `typ`] >>
     gvs[lookup_scopes_def, AllCaseEqs()]) >>
  drule annassign_store_continuation >> disch_then irule >>
  gvs[] >> qexists_tac `inst` >> simp[]
QED

Theorem stmt_post_end_gas_obs:
  stmt_post ctx func cx lctx old c sa sf s0 res (ee with gas_obs := gs) t =
  stmt_post ctx func cx lctx old c sa sf s0 res ee t
Proof
  simp[stmt_post_def, stmt_state_rel_def, state_rel_gas_obs,
       immutable_alloca_sep_def]
QED

Theorem annassign_concrete_rhs_outcome:
  !ctx func old c cx lctx RetQ id typ tyv e es etv sa0 st sa sb sf salloc
    op p sz w inst.
    declare_local old id typ sa0 = (c,st) /\ old.ce_alloca_locals /\
    (!l. FLOOKUP old.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    (!gs v es1. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,es1) ==> store_lays_out etv tyv v) /\
    local_ptrs_reserved c sa /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\ 32 <= sz /\
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,salloc)
      (\res ee t. ?v. res = INL v /\
        expr_post ctx func c cx e es sa sb salloc ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,salloc)
      (stmt_post ctx func cx lctx old c sa sf salloc)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule annassign_rhs_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_all annassign_normal_continuation >> strip_tac >>
  qexistsl_tac [`ff`, `u`] >> simp[stmt_post_end_gas_obs]
QED

Theorem gas_outcome_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_outcome F tops (ctx,func) source (es,s1) Q R ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_exec_zero_prefix]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_zero_prefix >> qexists_tac `s1` >> simp[]
QED

Theorem stmt_post_entry_frame:
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
     not_fresh_at sa x /\ lookup_var x s1 = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP s1.vs_allocas aid = SOME b) /\
  stmt_post ctx func cx lctx old c sa sf s1 res ee t ==>
  stmt_post ctx func cx lctx old c sa0 sf s0 res ee t
Proof
  simp[stmt_post_def] >> strip_tac >>
  qexists_tac `cenv''` >> simp[] >> conj_tac >> metis_tac[]
QED

Theorem annassign_outcome_entry_prefix:
  gas_marked_path F ctx func s0 0 (OK salloc) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
     not_fresh_at sa x /\ lookup_var x salloc = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP salloc.vs_allocas aid = SOME b) /\
  gas_outcome F tops (ctx,func) source (es,salloc)
    (stmt_post ctx func cx lctx old c sa sf salloc) R ==>
  gas_outcome F tops (ctx,func) source (es,s0)
    (stmt_post ctx func cx lctx old c sa0 sf s0) R
Proof
  strip_tac >> drule_all gas_outcome_zero_prefix >>
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      disj1_tac >> irule stmt_post_entry_frame >>
      qexistsl_tac [`salloc`, `sa`] >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

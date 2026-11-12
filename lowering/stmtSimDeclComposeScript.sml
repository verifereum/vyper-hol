(* Full-post continuation boundaries for counted declarations. *)
Theory stmtSimDeclCompose
Ancestors
  stmtSimDeclPath stmtSimDeclGas stmtSimDeclSource gasSummary
  gasSummaryCompose gasOutcome gasExemptCert fragGasMode
  stmtSimDefs exprSimDefs loweringPosts vyperInterpreter vyperState
  venomState compileEnv loweringStateRelDefs valueEncoding list finite_map stmtLowering
  emitHelperProps exprLoweringProps fragGasPath stmtSimProps
Libs monadsyntax

(* A statement-level frame may be stated from the old cenv when the new one
   agrees on every name in scope at the start. *)
Theorem alloca_frame_cenv_pre:
  alloca_frame c es sa s0 c' ee t /\
  (!n. IS_SOME (lookup_scopes n es.scopes) ==>
       FLOOKUP old.ce_vars n = FLOOKUP c.ce_vars n) ==>
  alloca_frame old es sa s0 c' ee t
Proof
  rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP _ _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!n b sz'. local_region old _ _ _ _ _ ==> _` irule >>
      qexists_tac `n` >> gvs[local_region_def] >>
      `IS_SOME (lookup_scopes n es.scopes)` by fs[] >>
      `FLOOKUP old.ce_vars n = FLOOKUP c.ce_vars n` by metis_tac[] >>
      fs[]) >>
  disch_then ACCEPT_TAC
QED

(* A word store into one alloca keeps the bytes of every other alloca. *)
Theorem mstore_alloca_others:
  !s aid0 (w:bytes32) z.
  allocas_non_overlapping s /\ FLOOKUP s.vs_allocas aid0 = SOME (w2n w, z) /\
  32 <= z ==>
  !wd aid off z'. FLOOKUP s.vs_allocas aid = SOME (off, z') /\ aid <> aid0 ==>
    mem_bytes_at off z' (mstore (w2n w) wd s).vs_memory =
    mem_bytes_at off z' s.vs_memory
Proof
  rewrite_tac[venomMemDefsTheory.allocas_non_overlapping_def] >> rpt gen_tac >>
  rpt strip_tac >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  first_x_assum (qspecl_then [`aid`, `aid0`, `off`, `z'`, `w2n w`, `z`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  decide_tac
QED

(* Storing into a freshly declared local keeps the frame of the allocas older
   than the declaration: they are disjoint from the new local's alloca. *)
Theorem alloca_frame_declare_store:
  alloca_frame c es sa s0 c es1 s /\ sa0.cs_next_id <= sa.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w, z) /\ sa0.cs_next_id <= aid0 /\
  lookup_var p s = SOME w /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) z) /\
  es1.scopes = sc :: rest /\ ee.scopes = (sc |+ (id, entry)) :: rest /\
  (!aid off z'. FLOOKUP s.vs_allocas aid = SOME (off, z') /\ aid < sa0.cs_next_id ==>
     mem_bytes_at off z' t.vs_memory = mem_bytes_at off z' s.vs_memory) /\
  local_ptrs_reserved c sa1 /\
  (!x. not_fresh_at sa1 x ==> lookup_var x t = lookup_var x s) ==>
  alloca_frame c es sa0 s0 c ee t
Proof
  rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >- first_assum ACCEPT_TAC >- decide_tac >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off, sz)` by metis_tac[] >>
  `aid <> aid0` by decide_tac >>
  Q.SUBGOAL_THEN `off + sz <= w2n w \/ w2n w + z <= off` assume_tac
  >- (qpat_x_assum `allocas_non_overlapping _`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     disch_then (qspecl_then [`aid`, `aid0`, `off`, `sz`, `w2n w`, `z`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `!aid off z'. FLOOKUP s.vs_allocas _ = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `!n q z'. FLOOKUP c.ce_vars n = SOME (PtrVar (Var q) z') ==>
            lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `n = id`
  >- (gvs[local_region_def] >> metis_tac[optionTheory.SOME_11]) >>
  qpat_x_assum `!n b sz'. local_region c es1.scopes s _ _ _ ==> _` irule >>
  qexists_tac `n` >>
  gvs[local_region_def, lookup_scopes_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* The frame of a declaration whose store writes only its own alloca,
   stated from the declaration's start (sa0) and its outer cenv (old). *)
Theorem alloca_frame_declare_local_store:
  alloca_frame c es sa s0 c es1 s /\ sa0.cs_next_id <= sa.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w, z) /\ sa0.cs_next_id <= aid0 /\
  lookup_var p s = SOME w /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) z) /\
  es1.scopes = sc :: rest /\ ee.scopes = (sc |+ (id, entry)) :: rest /\
  (!aid off z'. FLOOKUP s.vs_allocas aid = SOME (off, z') /\ aid < sa0.cs_next_id ==>
     mem_bytes_at off z' t.vs_memory = mem_bytes_at off z' s.vs_memory) /\
  local_ptrs_reserved c sa1 /\
  (!x. not_fresh_at sa1 x ==> lookup_var x t = lookup_var x s) /\
  MAP FDOM es1.scopes = MAP FDOM es.scopes /\ lookup_scopes id es1.scopes = NONE /\
  (!n. n <> id ==> FLOOKUP c.ce_vars n = FLOOKUP old.ce_vars n) ==>
  alloca_frame old es sa0 s0 c ee t
Proof
  strip_tac >> irule alloca_frame_cenv_pre >> qexists_tac `c` >>
  `alloca_frame c es sa0 s0 c ee t` by
    (mp_tac alloca_frame_declare_store >> disch_then irule >> simp[] >>
     metis_tac[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `lookup_scopes id es.scopes = NONE` by
    metis_tac[vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom] >>
  `n <> id` by (strip_tac >> gvs[]) >>
  metis_tac[]
QED

Theorem annassign_store_continuation:
  !H ctx func old cenv cx lctx e es es1 s0 s sa0 sa sb sf op id p sz w inst
    v etv tyv sc rest.
    expr_post H ctx func cenv cx e es sa sb s0 es1 v op s /\
    stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es1.scopes = MAP FDOM es.scopes /\
    sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
    sa0.cs_next_var <= sa.cs_next_var /\
    (!n. n <> id ==> FLOOKUP cenv.ce_vars n = FLOOKUP old.ce_vars n) /\
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
    gas_marked_exec F (ctx,func) (new_variable id tyv v) (es1,s)
      [] (INL ()) (es1 with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
      (OK (mstore (w2n w) (typed_val_to_w256 etv v) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    stmt_post H ctx func cx lctx old cenv sa0 sf es s0 (INL ())
      (es1 with scopes :=
        (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
      (mstore (w2n w) (typed_val_to_w256 etv v) s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_word_store_post_path >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  `alloca_frame cenv es sa s0 cenv es1 s` by
    (irule expr_post_alloca_frame >> metis_tac[]) >>
  `allocas_non_overlapping s` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >> metis_tac[]) >>
  `lookup_var p s = SOME w /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
            FLOOKUP s.vs_allocas aid = SOME b)` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> metis_tac[]) >>
  `alloca_frame old es sa0 s0 cenv (es1 with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (mp_tac (Q.INST [`c` |-> `cenv`, `aid0` |-> `inst.inst_id`, `z` |-> `sz`,
       `entry` |-> `<|assignable := T; type := tyv; value := v; popped := []|>`,
       `sa1` |-> `sa`, `ee` |-> `es1 with scopes :=
         (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`]
       alloca_frame_declare_local_store) >>
     disch_then irule >> simp[] >>
     mp_tac (Q.SPECL [`s`, `inst.inst_id`, `w`, `sz`] mstore_alloca_others) >>
     impl_tac >- simp[] >> strip_tac >> rpt strip_tac >>
     first_x_assum irule >> qexists_tac `aid` >> simp[]) >>
  `storage_well_formed_on cx es1 (FST H)` by fs[expr_post_def] >>
  `storage_well_formed_on cx (es1 with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
     (FST H)` by
    fs[vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageBackendTheory.get_storage_scopes] >>
  qpat_x_assum `t = _` (fn th => REWRITE_TAC[SYM th]) >>
  conj_tac
  >- simp[gas_marked_exec_def] >>
  simp[stmt_post_def, stmt_lands_def] >> rpt strip_tac >>
  `not_fresh_at sa x` by
    (qpat_x_assum `not_fresh_at sa0 x` mp_tac >> rw[not_fresh_at_def] >>
     first_x_assum irule >> simp[]) >>
  metis_tac[]
QED

Theorem gas_marked_exec_end_gas_obs:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r ==>
  gas_marked_exec memory (ctx,func) source (es,s0) marks res
    (ee with gas_obs := gs) r
Proof
  simp[gas_marked_exec_def]
QED

Theorem annassign_rhs_outcome:
  !ctx func cx st0 lctx RetQ id typ tyv es salloc old c sa sf s0 Q.
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,salloc) Q
      (\H res ee r. expr_exit res r) /\
    (!H res ee t. Q H res ee t ==> ?v. res = INL v) /\
    (!marks v ee t.
      gas_marked_exec F (ctx,func)
        (bind (eval_expr cx e) (read_result cx)) (es,salloc)
        marks (INL v) ee (OK t) /\
      (?H. valid_horizon cx st0 H ee.storage_trace) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
           Q H (INL v) (ee with gas_obs := []) t) ==>
      ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
        !H. valid_horizon cx st0 H ff.storage_trace ==>
          stmt_post H ctx func cx lctx old c sa sf es s0 (INL ())
            (ff with gas_obs := []) u) ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (eval_stmt cx (AnnAssign id typ e)) (es,salloc)
      (\H. stmt_post H ctx func cx lctx old c sa sf es s0)
      (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[gas_outcome_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_def]) >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule eval_annassign_action >>
      disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_new_variable])
  >- (qexists_tac `marks` >>
      drule eval_annassign_action >>
      disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> BETA_TAC >> strip_tac
      >- (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
          >- (disj1_tac >> irule gasStorageTheory.gas_bad_storage_at_bind_left >>
              simp[vyperStorageTraceTheory.storage_trace_frame_new_variable] >>
              metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
          `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
            metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
          gvs[] >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          qpat_x_assum `!marks v ee t. _`
            (qspecl_then [`marks`, `v`, `es_end`, `t`] mp_tac) >>
          impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
          disj2_tac >> disj1_tac >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INL ()`, `ff`, `OK u`] >> simp[] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
            |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end with gas_obs := []`, `t`, `v`] >>
          simp[] >> irule gas_marked_exec_end_gas_obs >> simp[]) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disj1_tac >> irule gasStorageTheory.gas_bad_storage_at_bind_left >>
          simp[vyperStorageTraceTheory.storage_trace_frame_new_variable] >>
          metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
      `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
        metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      `expr_exit res r` by (gs[] >> metis_tac[]) >>
      Cases_on `res` >- gvs[expr_exit_def] >>
      disj2_tac >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      rpt strip_tac >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
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
  !ctx func old c cx st0 lctx id typ tyv e es etv sa0 st sa sb sf salloc
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
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func c cx es salloc) /\
    sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
    sa0.cs_next_var <= sa.cs_next_var /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\ 32 <= sz /\
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,salloc) marks (INL v) ee (OK s) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         expr_post H ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op s) /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ff u. gas_marked_exec F (ctx,func) (new_variable id tyv v)
      (ee with gas_obs := [],s) [] (INL ()) ff (OK u) /\
      !H. valid_horizon cx st0 H ff.storage_trace ==>
        stmt_post H ctx func cx lctx old c sa0 sf es salloc (INL ()) ff u
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
  `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule eval_read_preserves_scopes_dom >> simp[]) >>
  drule_all declare_local_ptr >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_marked_exec F (ctx,func) (new_variable id tyv v) (ee with gas_obs := [],s)
       [] (INL ())
       ((ee with gas_obs := []) with scopes :=
          (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
       (OK (mstore (w2n w) (typed_val_to_w256 etv v) s with
              vs_inst_idx := SUC s.vs_inst_idx)) /\
     stmt_post H ctx func cx lctx old c sa0 sf es salloc (INL ())
       ((ee with gas_obs := []) with scopes :=
          (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest)
       (mstore (w2n w) (typed_val_to_w256 etv v) s with
          vs_inst_idx := SUC s.vs_inst_idx)` by
    (qx_gen_tac `HH` >> strip_tac >>
     `valid_horizon cx st0 HH es.storage_trace` by
       (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                             gas_marked_exec_valid_prefix)) >>
        impl_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
             vyperStorageTraceTheory.storage_trace_frame_read_result,
             vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
        disch_then irule >> gs[]) >>
     qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `HH` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `HH` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
     drule annassign_store_continuation >> disch_then irule >>
     gvs[] >> qexists_tac `inst` >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`(ee with gas_obs := []) with scopes :=
      (sc |+ (id, <|assignable := T; type := tyv; value := v; popped := []|>)) :: rest`,
    `mstore (w2n w) (typed_val_to_w256 etv v) s with
       vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- metis_tac[] >>
  qx_gen_tac `HH` >> strip_tac >>
  first_x_assum (qspec_then `HH` mp_tac) >> impl_tac >- gs[] >> simp[]
QED

Theorem stmt_post_end_gas_obs:
  stmt_post H ctx func cx lctx old c sa sf es0 s0 res (ee with gas_obs := gs) t =
  stmt_post H ctx func cx lctx old c sa sf es0 s0 res ee t
Proof
  `!b. get_storage cx (ee with gas_obs := gs) b = get_storage cx ee b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[stmt_post_def, stmt_state_rel_def, state_rel_gas_obs,
       immutable_alloca_sep_def, alloca_frame_def,
       vyperStorageFootprintTheory.storage_well_formed_on_def]
QED

Theorem annassign_concrete_rhs_outcome:
  !ctx func old c cx st0 lctx RetQ id typ tyv e es etv sa0 st sa sb sf salloc
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
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func c cx es salloc) /\
    sa0.cs_next_id <= inst.inst_id /\ sa0.cs_next_id <= sa.cs_next_id /\
    sa0.cs_next_var <= sa.cs_next_var /\
    emit_void MSTORE [Var p; op] sb = ((), sf) /\ fn_has_code sb sf func /\
    fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) sz) /\ not_fresh_at sa p /\
    lookup_var p salloc = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP salloc.vs_allocas inst.inst_id = SOME (w2n w,sz) /\ 32 <= sz /\
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,salloc)
      (\H res ee t. ?v. res = INL v /\
        expr_post H ctx func c cx e es sa sb salloc ee v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\H res ee r. expr_exit res r) ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (eval_stmt cx (AnnAssign id typ e)) (es,salloc)
      (\H. stmt_post H ctx func cx lctx old c sa0 sf es salloc)
      (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule annassign_rhs_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func c cx e es sa sb salloc (ee with gas_obs := []) v op t` by
    metis_tac[] >>
  `?H'. valid_horizon cx st0 H' ee.storage_trace` by
    (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  qspecl_then [`ctx`, `func`, `old`, `c`, `cx`, `st0`, `lctx`, `id`, `typ`,
               `tyv`, `e`, `es`, `etv`, `sa0`, `st`, `sa`, `sb`, `sf`,
               `salloc`, `marks`, `v`, `ee`, `t`, `op`, `p`, `sz`, `w`,
               `inst`] mp_tac
    (INST_TYPE [alpha |-> ``:256``] annassign_normal_continuation) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qexistsl_tac [`ff`, `u`] >> simp[stmt_post_end_gas_obs]
QED

Theorem gas_outcome_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_outcome F tops (ctx,func) cx st0 source (es,s1) Q R ==>
  gas_outcome F tops (ctx,func) cx st0 source (es,s0) Q R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      `s1.vs_gas_readings = s0.vs_gas_readings` by
        (drule gas_marked_path_ok_suffix >> simp[]) >>
      fs[gasStorageTheory.gas_bad_storage_at_def])
  >- (disj2_tac >> disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_exec_zero_prefix]) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_zero_prefix >> qexists_tac `s1` >> simp[]
QED

Theorem stmt_post_entry_frame:
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
     not_fresh_at sa x /\ lookup_var x s1 = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP s1.vs_allocas aid = SOME b) /\
  sa0.cs_next_id <= sa.cs_next_id /\ alloca_frame old es0 sa0 s0 old es1 s1 /\
  stmt_post H ctx func cx lctx old c sa sf es1 s1 res ee t ==>
  stmt_post H ctx func cx lctx old c sa0 sf es0 s0 res ee t
Proof
  simp[stmt_post_def] >> strip_tac >>
  `alloca_frame old es0 sa0 s0 cenv'' ee t` by
    (irule alloca_frame_trans >> metis_tac[]) >>
  qexists_tac `cenv''` >> simp[] >> conj_tac >> metis_tac[]
QED

Theorem annassign_outcome_entry_prefix:
  gas_marked_path F ctx func s0 0 (OK salloc) /\
  (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
     lookup_var x salloc = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP salloc.vs_allocas aid = SOME b) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func old cx es s0) /\
  local_ptrs_reserved old sa0 /\
  salloc.vs_memory = s0.vs_memory /\ storage_trace_frame source /\
  gas_outcome F tops (ctx,func) cx st0 source (es,salloc)
    (\H. stmt_post H ctx func cx lctx old c sa0 sf es salloc) R ==>
  gas_outcome F tops (ctx,func) cx st0 source (es,s0)
    (\H. stmt_post H ctx func cx lctx old c sa0 sf es s0) R
Proof
  strip_tac >>
  drule_all gas_outcome_zero_prefix >>
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      disj1_tac >> rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
           (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              gas_marked_exec_valid_prefix)) >>
         impl_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
         disch_then irule >> gs[]) >>
      `stmt_state_rel H ctx func old cx es s0` by metis_tac[] >>
      `alloca_frame old es sa0 s0 old es salloc` by
        (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
         simp[] >> metis_tac[]) >>
      irule (Q.INST [`sa` |-> `sa0`, `es1` |-> `es`, `s1` |-> `salloc`]
               stmt_post_entry_frame) >>
      simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* Counted memory composition of a declaration: the local's ALLOCA, the
   right-hand side's source action, then the store that binds the local.
   The memory-mode twins of stmtSimDeclCompose's annassign_rhs_outcome and
   annassign_outcome_entry_prefix. *)
Theory bodyDeclMemoryCompose
Ancestors
  stmtSimDeclCompose stmtSimDeclGas stmtSimDeclSource gasSummary
  gasSummaryCompose gasOutcome gasExemptCert fragGasMode fragGasPathMem
  stmtSimDefs stmtSimProps exprSimDefs vyperInterpreter vyperState list
Libs monadsyntax

Theorem gas_marked_exec_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_marked_exec T (ctx,func) source (es,s1) marks res ee r ==>
  gas_marked_exec T (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `gas_marked_path T ctx func s0 0 (OK s1)` by simp[gas_marked_path_def] >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  fs[gas_marked_exec_def] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem gas_exempt_cert_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_exempt_cert T tops (ctx,func) source (es,s1) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert T tops (ctx,func) source (es,s0) marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, return_def, gas_marked_path_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem gas_outcome_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_outcome T tops (ctx,func) source (es,s1) Q R ==>
  gas_outcome T tops (ctx,func) source (es,s0) Q R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_exec_zero_prefix_mem]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_zero_prefix_mem >> qexists_tac `s1` >> simp[]
QED

(* The declaration's source action from the state after the local's
   ALLOCA (salloc): the right-hand side's outcome, and the binding of the
   local after a value, which the caller supplies with the post P. *)
Theorem annassign_rhs_outcome_mem:
  !ctx func cx RetQ id typ tyv e es s0 salloc tops Q P.
    gas_path_mem ctx func s0 0 (OK salloc) /\
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_outcome T tops (ctx,func)
      (bind (eval_expr cx e) (read_result cx)) (es,salloc) Q
      (\res ee r. expr_exit res r) /\
    (!res ee t. Q res ee t ==> ?v. res = INL v) /\
    (!marks v ee t.
      gas_marked_exec T (ctx,func)
        (bind (eval_expr cx e) (read_result cx)) (es,salloc)
        marks (INL v) ee (OK t) /\
      Q (INL v) (ee with gas_obs := []) t ==>
      ?ff u. gas_marked_exec T (ctx,func) (new_variable id tyv v)
        (ee with gas_obs := [],t) [] (INL ()) ff (OK u) /\
        P (INL ()) (ff with gas_obs := []) u) ==>
    gas_outcome T tops (ctx,func)
      (eval_stmt cx (AnnAssign id typ e)) (es,s0) P
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `salloc` >> simp[] >>
  rewrite_tac[gas_outcome_def] >>
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

(* The frame of a declaration from its start (sa, s0): the local's ALLOCA
   (to salloc) writes no memory, the right-hand side's fragment (sA, from
   salloc to t) keeps the frame, and the store into the new local (from t
   to u) keeps the bytes of every alloca older than the declaration. *)
Theorem annassign_alloca_frame_mem:
  alloca_frame c es sA salloc c ee t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x salloc = lookup_var x s0) /\
  salloc.vs_memory = s0.vs_memory /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP salloc.vs_allocas aid = SOME b) /\
  sa.cs_next_id <= sA.cs_next_id /\
  (!aid b. FLOOKUP salloc.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  allocas_non_overlapping t /\
  FLOOKUP t.vs_allocas aid0 = SOME (w2n w, z) /\ sa.cs_next_id <= aid0 /\
  lookup_var p t = SOME w /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) z) /\
  (!n. n <> id ==> FLOOKUP c.ce_vars n = FLOOKUP cenv.ce_vars n) /\
  ee.scopes = sc :: rest /\ ee'.scopes = (sc |+ (id, entry)) :: rest /\
  (!aid off z'. FLOOKUP t.vs_allocas aid = SOME (off, z') /\ aid < sa.cs_next_id ==>
     mem_bytes_at off z' u.vs_memory = mem_bytes_at off z' t.vs_memory) /\
  local_ptrs_reserved c sB /\
  (!x. not_fresh_at sB x ==> lookup_var x u = lookup_var x t) /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\ lookup_scopes id ee.scopes = NONE ==>
  alloca_frame cenv es sa s0 c ee' u
Proof
  strip_tac >>
  `alloca_frame cenv es sa salloc c ee' u` by
    (mp_tac (Q.INST [`sa` |-> `sA`, `s0` |-> `salloc`, `es1` |-> `ee`,
       `s` |-> `t`, `sa0` |-> `sa`, `t` |-> `u`, `sa1` |-> `sB`,
       `old` |-> `cenv`, `ee` |-> `ee'`]
       stmtSimDeclComposeTheory.alloca_frame_declare_local_store) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv es salloc` by
    (irule alloca_frame_of_mem_frame >> simp[] >> metis_tac[]) >>
  irule alloca_frame_trans >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

(*
 * The statement-list cons case of the full body induction: the head's
 * joint fragment and the tail's, composed through one source/memory/
 * pointer witness, the head's landing state feeding the tail's entry.
 *
 * TOP-LEVEL:
 *   stmt_frag_full_cons_env -- the joint twin of stmtFragPtr's
 *     stmt_frag_cons_env_ptr, over paired original/shadow compilations
 *)
Theory bodyFullStmtsCons
Ancestors
  bodySimFull gasOutcomeFull gasOutcomeFullCompose fragGasOriginPtr
  gasShadowState stmtFragPtr stmtSimSeqEnv stmtSimProps stmtSimDefs
  fragGasOrigin gasOutcome gasSummary fragGasPathPtr fragGasMode
  loweringPosts bodyMemoryDefs bodyPtrDefs bodyExprPreFacts
  stmtLoweringMono fragExec gasSummaryCompose gasExemptCert exprSimDefs
  compileEnv stmtLowering vyperInterpreter vyperState
  vyperEvalPreservesScopes venomInst list

(* TEMPORARY: gasShadowCompileStmtBase's terminator lemmas, until the
   restored shadow spine is in this branch's base. *)
Theorem gas_shadow_inst_terminator_tmp[local]:
  gas_shadow_inst i j ==>
  is_terminator i.inst_opcode = is_terminator j.inst_opcode
Proof
  rw[gas_shadow_inst_def] >> simp[is_terminator_def]
QED

Theorem gas_shadow_insts_terminated_tmp[local]:
  !xs ys. LIST_REL gas_shadow_inst xs ys ==>
  (case xs of [] => F | _ => is_terminator (LAST xs).inst_opcode) =
  (case ys of [] => F | _ => is_terminator (LAST ys).inst_opcode)
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  Cases_on `xs`
  >- (gvs[] >> irule gas_shadow_inst_terminator_tmp >> simp[]) >>
  Cases_on `t` >> gvs[] >>
  first_x_assum (qspec_then `h'''::t''` mp_tac) >> simp[]
QED

Theorem gas_shadow_state_terminated_tmp[local]:
  gas_shadow_state s t ==> block_is_terminated s = block_is_terminated t
Proof
  strip_tac >> fs[gas_shadow_state_def] >>
  drule gas_shadow_insts_terminated_tmp >>
  Cases_on `s.cs_current_insts` >> Cases_on `t.cs_current_insts` >>
  simp[block_is_terminated_def]
QED

(* An outcome's normal post also knows the source run that reached it. *)
Theorem gas_outcome_full_eval_evidence:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn)
    (\res ee G' tn' t. Q res ee G' tn' t /\
       ?xs ee0. ee = ee0 with gas_obs := [] /\
         !tail. source (es with gas_obs := xs ++ tail) =
                (res, ee0 with gas_obs := tail)) R
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> qexistsl_tac [`res`, `ee`, `OK t`, `G'`, `tn'`] >>
      simp[] >>
      disj1_tac >> qexistsl_tac [`gas_explicit marks s.vs_gas_readings`, `ee`] >>
      simp[])
  >- (disj1_tac >> qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      simp[]) >>
  disj2_tac >> metis_tac[]
QED

(* gas_outcome_full_bind, with an exception that lands normally (a loop's
   Break or Continue) passing straight to the composite's post. *)
Theorem gas_outcome_full_bind_lands:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn)
    (\res mid G1 tn1 t.
       (?v. res = INL v /\
          gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (next v)
            (mid, t, G1, tn1) Q R) \/
       (?exc. res = INR exc /\ Q (INR exc) mid G1 tn1 t))
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!marks err ee leaf stop_state.
     gas_exempt_cert T tops (ctx, func) (ignore_bind source (return ()))
       (es, s) marks (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert T tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) marks (err, ee) (leaf, stop_state)) /\
  (!left v mid t right err ee leaf stop_state.
     gas_marked_exec T (ctx, func) source (es, s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert T tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) (left ++ right) (err, ee) (leaf, stop_state)) ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (bind source next)
    (es, s, G, tn) Q R
Proof
  strip_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_outcome_full _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (gvs[]
      >- (qpat_x_assum `gas_outcome_full _ _ (next _) _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
      >- (gvs[] >>
          `gas_path ctx func s (LENGTH marks) (OK t)` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase, gas_marked_path_exec] >>
          drule gas_explicit_append_path >>
          disch_then (qspec_then `marks'` assume_tac) >>
          rewrite_tac[gas_outcome_full_def] >>
          qexists_tac `marks ++ marks'` >> disj1_tac >>
          qexistsl_tac [`res`, `ee'`, `OK t'`, `G''`, `tn''`] >>
          conj_tac
          >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> simp[] >>
              metis_tac[]) >>
          conj_tac
          >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
          metis_tac[])
      >- (gvs[] >>
          `gas_path ctx func s (LENGTH marks) (OK t)` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase, gas_marked_path_exec] >>
          drule gas_explicit_append_path >>
          disch_then (qspec_then `marks'` assume_tac) >>
          rewrite_tac[gas_outcome_full_def] >>
          qexists_tac `marks ++ marks'` >> disj1_tac >>
          qexistsl_tac [`res`, `ee'`, `r`, `G''`, `tn''`] >>
          conj_tac
          >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >>
              simp[] >> metis_tac[]) >>
          conj_tac
          >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
          metis_tac[]) >>
      `gas_marked_exec T (ctx, func) source (es, s) marks (INL v) ee (OK t)` by
        (rewrite_tac[gas_marked_exec_def] >>
         metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
      asm_rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks ++ marks'` >> disj2_tac >>
      qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                    `finish'`] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
      rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `OK t`, `G'`, `tn'`] >>
      simp[] >> metis_tac[gas_source_bind_exception])
  >- (gvs[] >> rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      simp[] >> metis_tac[gas_source_bind_exception])
  >> asm_rewrite_tac[gas_outcome_full_def] >> metis_tac[]
QED

Theorem stmt_frag_full_cons_env:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty
   stmt shadow_stmt ss shadow_ss es.
    gas_shadow_compiles (stmt_env cenv lctx ty stmt)
      (stmt_env cenv lctx ty shadow_stmt) /\
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt) (stmt_env cenv lctx ty shadow_stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ c
         (stmts_env c lctx ty ss) (stmts_env c lctx ty shadow_ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss))
      (stmts_env cenv lctx ty (shadow_stmt::shadow_ss))
      (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ (stmt::ss) _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  `~block_is_terminated shadow_sa` by
    metis_tac[gas_shadow_state_terminated_tmp] >>
  qpat_x_assum `stmts_env _ _ _ (shadow_stmt::shadow_ss) _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >>
  rename1 `stmt_env cenv lctx ty shadow_stmt shadow_sa = (c', shadow_sm)` >>
  `c' = c /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `stmt`, `sa`, `c`, `sm`] mp_tac
    stmt_env_reserved >>
  simp[cj 1 compile_stmt_cs_mono] >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`c`, `lctx`, `ty`, `ss`] mp_tac stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends shadow_sa shadow_sm` by
    (`stmts_env cenv lctx ty [shadow_stmt] shadow_sa = (c, shadow_sm)` by
       simp[stmts_env_cons, comp_bind_def, stmts_env_def, comp_return_def] >>
     qspecl_then [`cenv`, `lctx`, `ty`, `[shadow_stmt]`] mp_tac
       stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends shadow_sm shadow_sb` by
    (qspecl_then [`c`, `lctx`, `ty`, `shadow_ss`] mp_tac stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es` by
    (irule gas_admissible_stmts_head >> qexists_tac `ss` >> simp[]) >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ (stmt_env _ _ _ _) _ _ _` mp_tac >>
  simp[stmt_frag_full_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `shadow_sa`, `shadow_sm`, `s0`,
                           `G0`, `tn0`, `c`] mp_tac) >>
  simp[] >>
  disch_then (assume_tac o MATCH_MP gas_outcome_full_eval_evidence) >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_outcome_full_bind_lands >> rpt conj_tac
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule (cj 2 gas_exempt_cert_rules) >> simp[] >>
      qexistsl_tac [`mid`, `t`] >> Cases_on `v` >> fs[])
  >~ [`gas_exempt_cert _ _ _ (ignore_bind (eval_stmt _ _) _)`]
  >- (rpt strip_tac >> irule (cj 3 gas_exempt_cert_rules) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ (eval_stmt _ _) _ _ _`
    (irule o MATCH_MP
       (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_full_post_mono)) >>
  reverse conj_tac
  >- (rpt strip_tac >> fs[] >> Cases_on `res` >> simp[] >>
      qpat_x_assum `!tail. stmt_exit_ptr _ (_ with gas_obs := tail) _ _ _`
        (qspec_then `[]` mp_tac) >>
      simp[stmt_exit_ptr_def, expr_exit_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> gvs[] >> suspend "tail") >>
  rename1 `INR exc` >> gvs[] >>
  qexists_tac `cenv''` >> fs[stmt_lands_def] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv''`, `t`, `sm`] >> simp[]
QED

Resume stmt_frag_full_cons_env[tail]:
  rename1 `!tail. eval_stmt cx stmt (es with gas_obs := xs ++ tail) =
             (INL (), ee0 with gas_obs := tail)` >>
  `eval_stmt cx stmt (es with gas_obs := xs) =
     (INL (), ee0 with gas_obs := [])` by
    (qpat_assum `!tail. eval_stmt _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx)
     (ee0 with gas_obs := [])` by
    (irule gas_admissible_stmts_tail >> metis_tac[]) >>
  `c.ce_return_pc = cenv.ce_return_pc /\
   c.ce_return_buf = cenv.ce_return_buf /\
   (c.ce_is_ctor <=> cenv.ce_is_ctor)` by
    metis_tac[cenv_top_ext_return_pc, cenv_top_ext_return_buf,
              cenv_top_ext_is_ctor] >>
  `dead_lo_ok D lo c cx` by fs[dead_lo_ok_def] >>
  `ret_pc_ok c sm t` by (irule ret_pc_ok_frame >> metis_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     metis_tac[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[stmt_lands_def] >>
  qpat_x_assum `!gs es1 c sa sm. _`
    (qspecl_then [`xs`, `ee0 with gas_obs := []`, `c`, `sa`, `sm`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[stmt_frag_full_def] >>
  disch_then (qspecl_then [`sm`, `sb`, `shadow_sm`, `shadow_sb`, `t`, `G'`,
                           `tn'`, `cenv'`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (assume_tac o MATCH_MP gas_outcome_full_eval_evidence) >>
  qpat_x_assum `gas_outcome_full _ _ (eval_stmts _ _) _ _ _`
    (irule o MATCH_MP
       (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_full_post_mono)) >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `cenv_top_ext c cfin _` >>
  qpat_x_assum `!tail. eval_stmts _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     simp[]) >>
  qexists_tac `cfin` >> simp[] >>
  irule cenv_top_ext_trans >> qexistsl_tac [`c`, `ee0.scopes`] >>
  gvs[preserves_scopes_dom_def]
QED

Finalise stmt_frag_full_cons_env

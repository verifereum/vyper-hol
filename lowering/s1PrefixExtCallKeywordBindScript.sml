(* Join keyword evaluation to the packed external-call continuation. *)
Theory s1PrefixExtCallKeywordBind
Ancestors
  s1PrefixCompose s1PrefixProps gasOutcomeFullCompose
  stmtSimProps exprSimDefs vyperInterpreter vyperStorageTrace vyperStorageFootprint

(* The keyword post is supplied by the full keyword-list judgment. The
   callback starts at its single successful replay and returns a prefix after
   the optional generated GAS; no source action intervenes on that path. *)
Theorem extcall_request_keyword_bind_prefix:
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx kw_es) (ee,u,G2,tn2) Qkw
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t)) /\
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx kw_es) (ee,u,G2,tn2) /\
  (!kw_marks kws ke G3 tn3 z.
     (!tail. eval_exprs cx kw_es
       (ee with gas_obs := gas_explicit kw_marks u.vs_gas_readings ++ tail) =
       (INL kws,ke with gas_obs := tail)) /\
     storage_trace_domain cx st0 ke.storage_trace /\ ke.gas_obs = [] /\
     (!H. valid_horizon cx st0 H ke.storage_trace ==> Qkw H (INL kws) ke G3 tn3 z) ==>
     ?n zg Gg tng.
       (!H. valid_horizon cx st0 H ke.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (z,G3,tn3) (REPLICATE n F) (OK zg,Gg,tng)) /\
       gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         cx st0 (eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws)))
         (ke,zg,Gg,tng)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_exprs cx kw_es)
      (\kws. eval_ext_call cx stat skip (fname,ats,rt) opts (v::(vs ++ kws))))
    (ee,u,G2,tn2)
Proof
  strip_tac >> irule gas_prefix_full_bind >>
  irule_at Any gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Qkw _` (irule_at Any) >>
  qexistsl [`\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
                 (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t)`,
            `\H res ke G tn z. Qkw H res ke G tn z /\ ke.gas_obs = []`] >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_ext_call] >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> Cases_on `r` >> simp[expr_exit_def]) >>
  qx_genl_tac [`kw_marks`,`kws`,`ke`,`G3`,`tn3`,`z`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ke.storage_trace) ke.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ke.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H ke.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qpat_assum `!kw_marks kws ke G3 tn3 z. _ ==> ?n zg Gg tng. _`
    (qspecl_then [`kw_marks`,`kws`,`ke`,`G3`,`tn3`,`z`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule gas_prefix_full_generated_prefix >>
  simp[storage_trace_frame_ext_call] >>
  qexistsl [`Gg`,`n`,`zg`,`tng`] >> simp[]
QED

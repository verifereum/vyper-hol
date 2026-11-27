Theory bodyIntCallBufferHeadUnwrapWordMods
Ancestors
  bodyIntCallBufferHeadSpecMods bodyIntCallBufferHeadCutsMods
  bodyIntCallBufferWordInputMods bodyFullPostsMods

val _ = Parse.hide "base";

Theorem intcall_buffer_head_unwrap_word_mods:
  intcall_buffer_head_input_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods exps src tops cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
    pin (ops,ws,vals,ptys,pflags) e dty (shi,vv,ci,shci,buf,ca,opn,cu,cs) /\
  intcall_buffer_head_alloc_post_mods (DF,lo,d,ctx,shadow_ctx,PG,func) mods cenv cx env st0
    (si,esi,s,G,tn) (ci,mid,u,Gu,tu) (ca,mid,a,Ga,ta)
    e dty raw vv buf aid dst base cap v /\
  storage_trace_domain cx st0 mid.storage_trace /\ is_word_type dty ==>
  ?z Gz tz. intcall_buffer_head_unwrap_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func) cenv cx st0
    (si,esi,s,G,tn) (ca,mid,a,Ga,ta) (cu,mid,z,Gz,tz)
    e dty raw vv aid dst base cap v opn
Proof
  pure_rewrite_tac [intcall_buffer_head_input_mods_def,
    intcall_buffer_head_alloc_post_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac exprSimFullBundlePropsTheory.expr_sim_full_code_fields >>
  qpat_assum `compile_alloc_buffer _ _ = _` (fn th =>
    assume_tac (REWRITE_RULE [th]
      (Q.SPECL [`MAX 32 (type_memory_bytes cenv dty)`,`ci`]
        exprLoweringPropsTheory.ci_mono_compile_alloc_buffer))) >>
  qpat_assum `ci_mono _ _`
    (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]) >>
  qpat_x_assum `?rt. evaluate_type _ (expr_type e) = _ /\ _`
    (qx_choose_then `rt` strip_assume_tac) >>
  `32 <= cap /\ w2n (n2w base : bytes32) = base` by
    (conj_tac >- simp[] >>
     `base < dimword (:256)` by decide_tac >> simp[arithmeticTheory.LESS_MOD]) >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  drule intcall_buffer_word_input_mods >>
  disch_then (fn th => qpat_assum `unwrap_value _ _ _ = _`
    (mp_then (Pat `unwrap_value _ _ _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ptr_covers Ga ta dst a cap`
    (mp_then (Pat `ptr_covers`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at _ _ _ _ _ _ _ Ga ta`
    (mp_then (Pat `ghost_kept_at`) mp_tac th)) >>
  disch_then (fn th => qhdtm_assum `ptr_vv_ok`
    (mp_then (Pat `ptr_vv_ok`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `storage_trace_domain _ _ _`
    (mp_then (Pat `storage_trace_domain`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `type_widens_to _ _ _`
    (mp_then (Pat `type_widens_to`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ (expr_type e) = SOME rt`
    (mp_then (Pat `evaluate_type _ _ = SOME _`) mp_tac th)) >>
  simp[] >>
  disch_then (fn th =>
    `!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx func cenv cx e esi si ca s mid raw vv a /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Ga ta a` by
        (gen_tac >> qpat_assum `!H. _ ==> storage_well_formed_on _ _ _ /\ _`
          (qspec_then `H` mp_tac) >> simp[]) >>
    qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (mp_then (Pat `vv_post_mods`) mp_tac th)) >>
  simp[] >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`dtv`,`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  `ca.cs_next_var <= cu.cs_next_var /\ ca.cs_next_id <= cu.cs_next_id` by
    (qspecl_then [`cenv`,`vv`,`ca`] mp_tac exprLoweringPropsTheory.ci_mono_unwrap_value >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved cenv ca` by
    (drule_then strip_assume_tac exprSimUnwrapTheory.compile_expr_extends >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `si` >> simp[] >> decide_tac) >>
  qpat_x_assum `aid = ci.cs_next_id` SUBST_ALL_TAC >>
  qpat_x_assum `cap = _` SUBST_ALL_TAC >>
  qexistsl [`z`,`Gz`,`tz`] >>
  simp[intcall_buffer_head_unwrap_post_mods_def] >>
  (reverse conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  simp[intcall_buffer_head_edge_mods_def] >>
  conj_tac >-
    (qpat_assum `z = a with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])) >>
  conj_tac >-
    (rpt gen_tac >> once_rewrite_tac[EQ_SYM_EQ] >>
     irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `ca` >> simp[]) >>
  simp[loweringPostsTheory.wb_frame_def,exprSimPropsTheory.locals_kept_mem]
QED

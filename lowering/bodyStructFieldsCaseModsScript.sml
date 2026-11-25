(* The linked StructLit constructor assembles one allocation and its ordered stores. *)
Theory bodyStructFieldsCaseMods
Ancestors
  bodyStructFieldsRunMods bodyStructFieldAllocMods bodyStructFieldsLayoutMods bodyStructFieldCutsMods
  bodyStructResultMemoryMods bodyStructFieldsCompileMods bodyStructFieldsSourceMods
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach bodyFullHashKeccakFixed
  exprSimFullBundleProps exprBodyPreProps exprSimAggregateSource gasOutcomeFullMods
  gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods gasStorage vyperStorageFootprint vyperStorageTrace
  gasContext vyperInterpreter vyperState vyperAST exprLoweringProps compileEnv
  loweringPosts loweringStateRelDefs context list pair
Libs monadsyntax

Triviality struct_outcome_map:
  (!es. result es = (f (FST (source es)), SND (source es))) /\
  (!ex. f (INR ex) = INR ex) /\ (!v. ISL (f (INL v))) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!H res ee g ts u. Q H res ee g ts u ==> Q' H (f res) ee g ts u) /\
  (!H res ee gt r. R H res ee gt r ==> R' H (f res) ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 result
    (es,s,G,tn) Q' R'
Proof
  strip_tac >>
  `ignore_bind result (return ()) = ignore_bind source (return ())` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `source x` >> rename1 `source x = (res,st)` >>
     Cases_on `res` >> simp[] >>
     rename1 `f (INL v)` >> `ISL (f (INL v))` by simp[] >>
     Cases_on `f (INL v)` >> fs[]) >>
  `!x. SND (result x) = SND (source x)` by simp[] >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  asm_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl [`f res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Triviality struct_initial_domain:
  storage_trace_frame source /\ ~s.vs_halted /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 es.storage_trace` >- simp[] >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >> qx_gen_tac `tail` >>
  Cases_on `source (es with gas_obs := tail)` >> simp[] >>
  irule storage_trace_frame_preserves_bad_domain >>
  qexistsl [`source`,`q`,`es with gas_obs := tail`] >> simp[]
QED

Triviality struct_lit_result_map:
  eval_expr cx (StructLit ann nsid kes) es =
    ((case FST (eval_exprs cx (MAP SND kes) es) of
       INL vs => INL (Value (StructV (ZIP (MAP FST kes,vs)))) | INR ex => INR ex),
     SND (eval_exprs cx (MAP SND kes) es))
Proof
  Cases_on `eval_exprs cx (MAP SND kes) es` >>
  drule_then (qspecl_then [`nsid`,`ann`] mp_tac) aggregate_eval_struct >> simp[]
QED

Triviality struct_literal_vv_mods:
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  body_exprs_full_ok_mods mods exps cx (MAP SND kes) /\
  expr_body_pre_mods mods ce cx env (StructLit (StructT nsid) nsid kes) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (StructLit (StructT nsid) nsid kes) es
Proof
  strip_tac >> drule_then strip_assume_tac struct_fields_layout_mods >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  irule struct_initial_domain >> simp[evaluate_storage_trace_frame] >> strip_tac >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac struct_literal_paired_compile >>
  rename1 `compile_alloc_buffer (type_memory_size_list tvs) sa = (ba,sm)` >>
  rename1 `compile_alloc_buffer _ shadow_sa = (ba,shadow_sm)` >>
  `fn_has_code sa sm func` by fs[expr_sim_full_code_def] >>
  qabbrev_tac `pure = ~expr_has_effect (StructLit (StructT nsid) nsid kes)` >>
  `?root addr t G tn.
     ba.buf_operand = Var root /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) [] (OK t,G,tn)) /\
     return_buf_frame d ce sm t /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
       struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (es,sa,s0,G0,tn0)
         (root,addr,type_memory_size_list tvs,sa.cs_next_id) (H,DF H,es,sm,G,tn,t) [] 0)` by
    (irule struct_field_alloc_prefix_mods >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `return_buf_frame d ce sm s1` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) _ [] (OK s1,G1,tn1)` >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?(H : (bool # 256 word # type_value) list # num list). stmt_state_rel H ctx func ce cx es s0` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     qpat_assum `!H. valid_horizon cx st0 H _ ==> stmt_state_rel H ctx func ce cx es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >> simp[] >>
     qexistsl [`ce`,`ctx`,`cx`,`exps`,`func`,`mods`] >> simp[]) >>
  `!fn inst s. frag_reachable ctx func s1 fn inst s ==> dalloca_fmp_headroom inst s` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) _ [] (OK s1,G1,tn1)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)`
         (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom)) >>
     disch_then (qspecl_then [`fn`,`inst`,`s`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def]) >>
  drule_then assume_tac struct_fields_list_admissible_mods >>
  `!e ee. MEM e (MAP SND kes) /\ expr_sim_inv_mods mods ce cx env ee ==>
    expr_body_pre_mods mods ce cx env e ee` by (rpt strip_tac >> drule_all_then ACCEPT_TAC struct_field_pre_mods) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `pure ==> ~EXISTS expr_has_effect (MAP SND kes)` by
    simp[Abbr `pure`, expr_has_effect_thm, EVERY_MAP, combinTheory.o_DEF] >>
  `LENGTH kes = LENGTH tvs` by
    (qpat_assum `LIST_REL (\t (name,e). _) _ kes` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  `type_memory_bytes ce (StructT nsid) = type_memory_size_list tvs` by
    simp[type_memory_bytes_def] >>
  qpat_x_assum `type_memory_size_list tvs = SUM _` kall_tac >>
  qpat_assum `ba.buf_operand = Var root` (fn th =>
    qpat_x_assum `compile_struct_lit _ ce _ _ _ 0 sm = _`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
    qpat_x_assum `compile_struct_lit _ (gas_shadow_env T ce) _ _ _ 0 shadow_sm = _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (conj_tac >> rpt gen_tac >> strip_tac >> first_x_assum irule >> metis_tac[]) >>
  suspend "stores"
QED

Resume struct_literal_vv_mods[stores]:
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    ce.ce_modules cx st0 (eval_exprs cx (MAP SND kes)) (es,s0,G0,tn0)
    (\H res ee g ts u. ?vs cells. res = INL vs /\ expr_sim_inv_mods mods ce cx env ee /\
      LIST_REL value_has_type tvs vs /\
      struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (es,sa,s0,G0,tn0)
        (root,addr,type_memory_size_list tvs,sa.cs_next_id) (H,DF H,ee,sb,g,ts,u)
        ([] ++ cells) (0 + type_memory_size_list tvs) /\
      (!m. mem_agree_outside ts.t_mem u.vs_memory m ==>
        fields_in_memory (ZIP (MAP FST kes,vs)) (ZIP (MAP FST kes,tvs)) (addr+0) m))
    (\H res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
      halt_exit H cx ee (INR exc : eval_result + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))` by
    (irule gas_outcome_full_mods_zero_prefix >> qexistsl [`G1`,`s1`,`tn1`] >>
     conj_tac >- (qx_gen_tac `Hx` >>
       qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) _ [] (OK s1,G1,tn1)`
         (qspec_then `DF Hx` ACCEPT_TAC)) >>
     irule (BETA_RULE struct_fields_run_mods) >>
     simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES, arithmeticTheory.LESS_EQ_REFL] >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- (qexists_tac `H` >> first_assum ACCEPT_TAC)
     >- (qexistsl [`nsid`,`Var root`,`shadow_func`,`shadow_sb`,`shadow_sm`,`sm`,
          `MAP (FST o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC)
     >- (qexists_tac `exps` >> rpt conj_tac >> first_assum ACCEPT_TAC)
     >- (qexistsl [`src`,`tops`] >> first_assum ACCEPT_TAC)) >>
  suspend "post"
QED

Resume struct_literal_vv_mods[post]:
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ Qlist Rlist` >>
  irule (INST_TYPE [``:'b`` |-> ``:value list``] struct_outcome_map) >>
  qexistsl [`Qlist`,`Rlist`,
    `\res. case res of INL vs => INL (Value (StructV (ZIP (MAP FST kes,vs))))
                     | INR ex => INR ex`, `eval_exprs cx (MAP SND kes)`] >>
  simp_tac bool_ss [struct_lit_result_map, sumTheory.sum_case_def, sumTheory.ISL, AND_CLAUSES] >>
  reverse conj_tac
  >- (conj_tac >- (simp[Abbr `Rlist`] >> rpt strip_tac >> fs[]) >>
      simp[Abbr `Rlist`]) >>
  simp_tac bool_ss [Abbr `Qlist`, arithmeticTheory.ADD_CLAUSES, APPEND] >>
  rpt strip_tac >> qunabbrev_tac `pure` >>
  drule_all_then strip_assume_tac struct_result_vv_post_mods >>
  qpat_assum `struct_prefix_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def]) >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  gvs[expr_type_def, exprLoweringTheory.lowered_value_type_def, vv_location_def, base_ptr_def]
QED

Finalise struct_literal_vv_mods

Theorem body_structlit_case_full_mods:
  !mods exps cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_full_ok_mods mods exps cx (MAP SND kes)) ==>
    body_expr_full_ok_mods mods exps cx (StructLit v7 (src_id_opt,id) kes)
Proof
  simp[Once body_expr_full_ok_mods_def] >> rpt strip_tac >>
  drule_then strip_assume_tac struct_fields_layout_mods >>
  gvs[] >> drule_all_then assume_tac struct_literal_vv_mods
  >~ [`expr_sim_full_mods _ _ _ _ _ _`]
  >- (irule struct_literal_value_of_memory_vv_mods >> simp[]) >>
  simp[]
QED

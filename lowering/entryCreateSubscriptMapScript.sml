(* Mapping subscripts evaluate a reference, then a value key. *)
Theory entryCreateSubscriptMap
Ancestors
  entryCreateSubscriptMapSpec entryCreateSubscriptLayout entryCreateSubscriptMapRun
  entryCreateImmSubscriptIntervals entryCreateIntervalLayout createSizeCutCode
  exprLoweringProps exprLowering exprSimMapKey exprSimMapDefs exprSimPlaces exprSimUnwrap
  gasShadowCompileBase gasShadowCompilePure gasShadowCompileStmtHelpers
  gasShadowState gasShadow compileEnv fragExec context pair
  exprSimFullBundleProps s1PrefixDefs entryCreateFocusSpec exprSimSubscriptMap
  exprSimDefs gasContext bodyFullPreds bodyFullIfExpReach bodyMemoryDefs freshWrites
  bodySim exprSimHypsDefs loweringPosts fragGasOriginPtr gasSummary vyperStorageFootprint
  vyperState vyperInterpreter gasExplicitSites exprSimSource createSizeCutOpens
  emitHelper venomInst

Theorem mapping_shadow_landing[local]:
  gas_shadow_state a a' /\ comp a = (v,b) /\ gas_shadow_compiles comp shcomp ==>
  ?b'. shcomp a' = (v,b') /\ gas_shadow_state b b'
Proof
  strip_tac >> Cases_on `shcomp a'` >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`a`,`a'`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[]
QED

Theorem mapping_selector_extends[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sn else (key,sn)) =
    (hashed,sp) /\ compile_mapping_subscript bop hashed sp = (slot,sb) ==>
  cs_extends sn sb
Proof
  strip_tac >>
  `ci_mono sn sp` by
    (Cases_on `is_bytestring_type kt` >> gvs[ci_mono_def,cs_extends_refl] >>
     metis_tac[ci_mono_compile_keccak256_key,ci_mono_def,SND]) >>
  `ci_mono sp sb` by metis_tac[ci_mono_compile_mapping_subscript,SND] >>
  metis_tac[ci_mono_def,cs_extends_trans]
QED

Theorem mapping_compiled_intervals:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha =
    (vv,shb) /\ gas_shadow_state sa sha /\
  place_type ce obj = MapPT kt vt /\ expr_map_pre ce cx env obj es /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc ==>
  ~subscript_reads_base cx obj idx /\
  ?bvv sm key sn hashed sp slot shm shn.
    compile_expr ce ty obj sa = (bvv,sm) /\
    lower_value compile_expr ce (expr_type idx) idx sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn else (key,sn)) =
      (hashed,sp) /\ compile_mapping_subscript (vv_operand bvv) hashed sp = (slot,sb) /\
    vv = LocatedValue ann (mk_ptr slot
      (case vv_location bvv of SOME l => l | NONE => LocMemory)) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type idx)
      (gas_shadow_expr idx) shm = (key,shn) /\
    gas_shadow_state sm shm /\ gas_shadow_state sn shn /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    fn_has_code sha shm shfunc /\ fn_has_code shm shn shfunc
Proof
  strip_tac >> drule_all create_subscript_mapping_layout >> strip_tac >>
  `?shm. compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
         gas_shadow_state sm shm` by
    (irule mapping_shadow_landing >> first_assum (irule_at Any) >>
     simp[gas_shadow_stmt_compile_expr_env]) >>
  `?shn. lower_value compile_expr (gas_shadow_env T ce) (expr_type idx)
           (gas_shadow_expr idx) shm = (key,shn) /\ gas_shadow_state sn shn` by
    (irule mapping_shadow_landing >> first_assum (irule_at Any) >>
     qexists_tac `lower_value compile_expr ce (expr_type idx) idx` >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `cs_extends shn shb` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,NoAsms] >> strip_tac >>
     drule_at (Pat `compile_expr _ _ (Subscript _ _ _) _ = _`)
       compile_expr_mapping_subscript_parts >>
     simp[gas_shadow_place_type, place_type_gas_shadow_env,
          copies_subscript_base_gas_shadow_env, gas_shadow_expr_type] >>
     impl_tac >- fs[copies_subscript_base_def] >>
     strip_tac >> gvs[] >> metis_tac[mapping_selector_extends]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bvv`,`sm`,`key`,`sn`,`hashed`,`sp`,`slot`,`shm`,`shn`] >> simp[] >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
   cs_extends sha shm /\ cs_extends shm shn` by
    metis_tac[compile_expr_extends,cj 2 compile_expr_grows,mapping_selector_extends] >>
  simp[] >> metis_tac[fn_has_code_split,cs_extends_trans]
QED

(* The map pre is shortened to the installed reference-producing interval. *)
Theorem mapping_base_ready:
  (entryCreateSubscriptMapSpec$expr_map_sim_full_pre (DF,lo,d,C,CS,PG,f,fs) ce cx ty
      (Subscript ann obj idx) es (st0,a,b,ha,hb,vv,s,G,tn) \/
   expr_vv_sim_full_pre (DF,lo,d,C,CS,PG,f,fs) ce cx ty
      (Subscript ann obj idx) es (st0,a,b,ha,hb,vv,s,G,tn)) /\
  compile_expr ce ty obj a = (bv,m) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) ha = (bv,hm) /\
  gas_shadow_state m hm /\ fn_has_code a m f /\ fn_has_code ha hm fs ==>
  entryCreateSubscriptMapSpec$expr_map_sim_full_pre (DF,lo,d,C,CS,PG,f,fs) ce cx ty
    obj es (st0,a,m,ha,hm,bv,s,G,tn)
Proof
  strip_tac >>
  gvs[entryCreateSubscriptMapSpecTheory.expr_map_sim_full_pre_def,
      expr_vv_sim_full_pre_def,expr_sim_full_code_def,
      create_operand_at_def]
  >- (drule subscript_map_base_admissible >> metis_tac[]) >>
  conj_tac >- (irule subscript_result_base_admissible >>
    goal_assum (drule_at Any) >> simp[subscript_result_predicates_exceptions]) >>
  metis_tac[]
QED

(* The source pre and const cells follow the reference result; the key may
   have arbitrary effects allowed by that actual selected source handoff. *)
Theorem mapping_key_source_ready:
  (expr_body_pre ce cx env (Subscript ann obj idx) es \/
   expr_map_pre ce cx env (Subscript ann obj idx) es) /\
  expr_map_pre ce cx env obj es /\ place_type ce obj = MapPT kt vt /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) ==>
  expr_body_pre ce cx env idx mid /\ body_const_cells_agree [(NONE,tops)] cx env mid
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (`(expr_body_pre ce cx env (Subscript ann obj idx) (es with gas_obs := gs) \/
        expr_map_pre ce cx env (Subscript ann obj idx) (es with gas_obs := gs))` by
        metis_tac[expr_body_pre_gas_obs,expr_map_pre_gas_obs] >>
      metis_tac[mapping_subscript_index_pre]) >>
  `body_const_cells_agree [(NONE,tops)] cx env (es with gas_obs := gs)` by simp[] >>
  `IS_SOME (type_place_expr env obj)` by (fs[expr_map_pre_def] >> simp[]) >>
  metis_tac[body_const_cells_agree_expr]
QED

Theorem mapping_key_target_ready:
  entryCreateSubscriptMapSpec$expr_map_sim_full_pre (DF,lo,d,C,CS,PG,f,sf) ce cx ty
    obj es (st0,a,m,ha,hm,bvv,s0,G0,tn0) /\
  lower_value compile_expr ce (expr_type idx) idx m = (key,n) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type idx) (gas_shadow_expr idx) hm =
    (key,hn) /\
  gas_shadow_state n hn /\ fn_has_code m n f /\ fn_has_code hm hn sf /\
  cs_extends a m /\ (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\ create_operand_at m s /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok mid /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    entryCreateSubscriptMapSpec$expr_map_sim_full_post (DF,lo,d,C,f) ce cx obj
      (es,a,m,s0,bvv,G0,tn0) H (INL raw) mid G1 tn1 s /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites C CS,C,f,PG)
      (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
  expr_sim_full_pre (DF,lo,d,C,CS,PG,f,sf) ce cx (expr_type idx)
    idx mid (st0,m,n,hm,hn,key,s,G1,tn1)
Proof
  strip_tac >>
  fs[entryCreateSubscriptMapSpecTheory.expr_map_sim_full_pre_def,expr_sim_full_code_def] >>
  `a.cs_next_var <= m.cs_next_var` by
    (qpat_assum `compile_expr ce ty obj a = _`
       (mp_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `!fn inst z. frag_reachable C f s fn inst z ==> dalloca_fmp_headroom inst z` by
    metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  qpat_assum `entryCreateSubscriptMapSpec$expr_map_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE
      [entryCreateSubscriptMapSpecTheory.expr_map_sim_full_post_def]) >>
  fs[expr_sim_full_endpoint_def] >>
  `return_buf_frame d ce m s` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`a`] >> simp[]) >>
  simp[expr_sim_full_pre_def,create_operand_at_def] >> rpt conj_tac
  >~ [`local_ptrs_reserved _ _`] >- metis_tac[local_ptrs_reserved_next_var]
  >~ [`not_fresh_at _ _`] >- metis_tac[not_fresh_at_mono]
  >~ [`not_fresh_at _ _`] >- metis_tac[not_fresh_at_mono] >>
  TRY (first_assum ACCEPT_TAC) >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[entryCreateSubscriptMapSpecTheory.expr_map_sim_full_post_def]
QED

Theorem mapping_selector_cut_code:
  (if is_bytestring_type kt then compile_keccak256_key key F n else (key,n)) =
    (hashed,p) /\ compile_mapping_subscript bop hashed p = (slot,b) ==>
  create_cut_code {} n b
Proof
  strip_tac >> irule create_cut_code_join >> qexists_tac `p` >> conj_tac
  >- (Cases_on `is_bytestring_type kt` >> gvs[] >>
      qpat_assum `compile_keccak256_key _ _ _ = _`
        (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
      simp[NoAsms,compile_keccak256_key_def] >>
      irule create_cut_code_bind >> simp[create_cut_code_emit_op,create_cut_targets_def] >>
      irule create_cut_code_bind >> simp[create_cut_code_emit_op,create_cut_targets_def]) >>
  qpat_assum `compile_mapping_subscript _ _ _ = _`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
  simp[NoAsms,compile_mapping_subscript_def] >>
  irule create_cut_code_bind_all >> simp[create_alloc_buffer_cut_code] >>
  rpt gen_tac >> irule create_cut_code_ignore_bind >>
  simp[create_cut_code_emit_void,create_cut_targets_def] >>
  irule create_cut_code_bind >> simp[create_cut_code_emit_op,create_cut_targets_def] >>
  irule create_cut_code_ignore_bind >>
  simp[create_cut_code_emit_op,create_cut_code_emit_void,create_cut_targets_def]
QED

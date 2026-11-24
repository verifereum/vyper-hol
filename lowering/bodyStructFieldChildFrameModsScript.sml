(* Protect the already initialized fields across one successful child read. *)
Theory bodyStructFieldChildFrameMods
Ancestors
  bodyStructFieldCutsMods bodyFullStructLitInputs bodyCopyReadPhysicalTypeMods
  bodyAnnNonwordReadTypesMods bodyAssignNameLinkedSetup exprBodyPreProps
  exprSimWordArgs wordArgsPtr freshWrites appendStorageGhostPtr
  stateRelProj allocaSiteResource exprSimPrecompiles exprSimAggregateChildren
  bodyPtrPrecompileBuiltinsGhost venomState
  bodyFullPostsMods bodyPtrDefs bodyPtrMakeArrayMemoryFrame
  loweringPosts loweringStateRelDefs valueEncodingTyping valueCopyBytes
  abiDecodeStaticProps representationCleanPtr assignBasePtrBoundary
  typedMemoryCopy vyperTypeArgFits exprSimFullBundleProps exprSimProps list
  bodySimStmtFacts exprSimIfExpCompat vyperTypeSystem vyperTypeEvalCaseProofs
  exprLoweringProps exprLowering compileEnv vyperAST vyperTypeExprSoundness
  valueEncoding vyperState vyperInterpreter finite_map words exprSimSource
  exprSimHypsDefs vyperTypeInvariants

Theorem field_read_result_frame[local]:
  wb_frame ce es ee si s z /\ ghost_kept_at lo ce es si Gi ti s G tn /\
  FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\ aid < si.cs_next_id /\
  (!name p k. local_region ce es.scopes s name p k ==>
    addr+capacity <= p \/ p+k <= addr) ==>
  mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s.vs_memory /\
  (!i. addr <= i /\ i < addr+capacity /\ i IN tn.t_mem ==> i IN ti.t_mem)
Proof
  pure_rewrite_tac [wb_frame_def, ghost_kept_at_def] >> strip_tac >> conj_tac
  >- (qpat_assum `!a b n. _ ==> mem_bytes_at b n _ = _`
       (qspecl_then [`aid`,`addr`,`capacity`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!a b n i. _ ==> i IN ti.t_mem`
    (qspecl_then [`aid`,`addr`,`capacity`,`i`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Theorem field_read_cells_kept[local]:
  mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s.vs_memory /\
  (!i. addr <= i /\ i < addr+capacity /\ i IN tn.t_mem ==> i IN ti.t_mem) /\
  EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\ off <= capacity /\
  literal_prefix_ok cells ti s ==>
  literal_prefix_ok cells tn z
Proof
  strip_tac >> irule literal_prefix_transport >> qexistsl [`s`,`ti`] >> simp[] >>
  rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac literal_prefix_lookup >>
  `addr <= p /\ p+k <= addr+off` by
    (qpat_assum `EVERY _ cells` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(tv,v,p,k)` mp_tac) >> simp[]) >>
  gen_tac >> strip_tac >> irule robust_val_in_memory_shrinking_frame >>
  simp[] >> qexistsl [`ti.t_mem`,`tn.t_mem`,`s.vs_memory`,`z.vs_memory`,`k`] >>
  simp[] >> irule mem_bytes_at_bytewise >> rpt strip_tac >> irule mem_bytes_at_eq_byte >>
  qexistsl [`addr`,`capacity`] >> simp[] >> decide_tac
QED

Theorem struct_field_prefix_after_read_mods:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (Hi,Di,es,si,Gi,ti,s) cells off /\
  stmt_state_rel H0 ctx func ce cx ees sf /\
  expr_post_mods H ctx func ce cx e es si su s ee v op z /\
  ghost_inv_at_mods D lo d ce cx ee G tn z /\
  ghost_kept_at lo ce es si Gi ti s G tn /\
  local_ptrs_reserved ce fr /\ local_ptrs_reserved ce si /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  si.cs_next_id <= su.cs_next_id /\ si.cs_next_var <= su.cs_next_var /\
  ~z.vs_halted /\ expr_sim_full_endpoint func su s z /\
  (pure ==> ~expr_has_effect e) ==>
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (H,D,ee,su,G,tn,z) cells off
Proof
  pure_rewrite_tac [struct_prefix_mods_def, expr_post_mods_def] >> strip_tac >>
  drule_then assume_tac expr_post_frame >>
  `fr.cs_next_id <= si.cs_next_id` by decide_tac >>
  `wb_frame ce ees ee fr sf z` by
    metis_tac[wb_frame_trans] >>
  `ghost_kept_at lo ce ees fr Gf tnf sf G tn` by
    metis_tac[ghost_kept_at_wb_trans] >>
  drule_all_then strip_assume_tac field_read_result_frame >>
  drule_all_then assume_tac field_read_cells_kept >>
  `lookup_var root z = SOME (n2w addr)` by metis_tac[wb_frame_vars] >>
  `ptr_covers G tn root z capacity` by
    (qpat_assum `ghost_kept_at _ ce es si Gi ti s G tn`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `!x. not_fresh_at si x ==> FLOOKUP G x = _ /\ _`
       (qspec_then `root` (drule_then strip_assume_tac)) >>
     qpat_assum `ptr_covers Gi ti root s capacity`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def]) >>
  `FLOOKUP z.vs_allocas aid = SOME (addr,capacity)` by fs[wb_frame_def] >>
  `!name p k. local_region ce ee.scopes z name p k <=> local_region ce es.scopes s name p k` by
    metis_tac[wb_frame_local_regions] >>
  `expr_sim_full_endpoint func su sf z` by
    (qpat_assum `expr_sim_full_endpoint func si sf s` mp_tac >>
     fs[expr_sim_full_endpoint_def] >> decide_tac) >>
  `pure ==> pure_frame ce func ees fr sf z` by
    (strip_tac >> irule pure_frame_trans >> simp[] >>
     qexistsl [`es`,`si`,`s`] >> simp[] >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `wb_frame ce ees es fr sf s`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     simp[]) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `MAP FDOM ees.scopes = MAP FDOM ee.scopes` by metis_tac[] >>
  `not_fresh_at su root` by metis_tac[not_fresh_at_mono] >>
  `aid < su.cs_next_id /\ fr.cs_next_var <= su.cs_next_var` by decide_tac >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem field_word_lowered[local]:
  expr_body_pre_mods mods ce cx env e es /\ is_word_type (expr_type e) ==>
  lowered_value_type ce e = expr_type e
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >> simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all ifexp_lowered_type_classify >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac))
  >- metis_tac[is_bytestring_word_type] >>
  qpat_x_assum `e = Call _ (IntCall _) _ _` SUBST_ALL_TAC >>
  PairCases_on `fid` >>
  qpat_x_assum `well_typed_expr env _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  drule_all_then assume_tac expr_sim_inv_mods_return_type >>
  fs[lowered_value_type_def,expr_type_def] >> metis_tac[compileEnvTheory.type_widens_to_word]
QED

Theorem field_read_robust_nonword[local]:
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  value_has_type stv v /\ value_has_type pt v /\
  expr_val_at ce cx (post_value_type ce e) si su ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op G tn z ==>
  ?sw. eval_operand op z = SOME sw /\
    (!m. mem_agree_outside tn.t_mem z.vs_memory m ==> val_in_memory stv v (w2n sw) m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [expr_val_at_def]) >>
  qpat_x_assum `!tv. evaluate_type _ _ = SOME tv /\ _ ==> _`
    (qspec_then `pt` mp_tac) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `w` (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
  qexists_tac `w` >> simp[] >>
  `!m. mem_agree_outside tn.t_mem z.vs_memory m ==> val_in_memory pt v (w2n w) m` by
    (fs[ptr_val_ok_def,ptr_mem_ok_def] >> metis_tac[]) >>
  Cases_on `post_value_type ce e = lowered_value_type ce e` >> gvs[] >>
  rpt strip_tac >> metis_tac[bytestring_val_in_memory_transfer]
QED

Theorem field_read_disjoint[local]:
  stmt_state_rel H ctx func ce cx ee z /\
  expr_val_at ce cx sty si su ee v op z /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\ 0 < type_memory_size stv /\
  eval_operand op z = SOME sw /\
  FLOOKUP z.vs_allocas aid = SOME (addr,capacity) /\ aid < si.cs_next_id /\
  off + n <= capacity /\
  (!name p k. local_region ce ee.scopes z name p k ==>
    addr + capacity <= p \/ p+k <= addr) ==>
  w2n sw + val_footprint stv v <= addr+off \/ addr+off+n <= w2n sw
Proof
  strip_tac >> drule_all_then assume_tac evaluated_nonbytes_footprint >>
  `addr <= addr+off /\ addr+off+n <= addr+capacity` by decide_tac >>
  `!name p k. local_region ce ee.scopes z name p k ==>
      p+k <= addr+off \/ addr+off+n <= p` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> decide_tac) >>
  `0 < val_footprint stv v` by simp[] >>
  drule_all structlit_physical_footprint_bounds >> simp[]
QED

(* The destination was formed before unwrap; use its preserved variable and
   coverage at the store cursor, not a fresh evaluation of the child. *)
Theorem struct_field_store_input_mods:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  value_runtime_typed env (expr_type e) v /\
  arg_type_fits (expr_type e) fty /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
  expr_post_mods H ctx func ce cx e es si su s ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op G tn z /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G z) /\
  (~is_word_type (post_value_type ce e) ==>
   !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  FLOOKUP z.vs_allocas aid = SOME (addr,capacity) /\ aid < si.cs_next_id /\
  addr + capacity < dimword (:256) /\ off + type_memory_size ftv <= capacity /\
  (!name p k. local_region ce ee.scopes z name p k ==>
    addr+capacity <= p \/ p+k <= addr) /\
  not_fresh_at su dst /\ lookup_var dst z = SOME (n2w (addr+off)) /\
  ptr_covers G tn dst z (type_memory_size ftv) ==>
  ?stv. struct_operand_mods (ce,get_tenv cx,lowered_value_type ce e,fty,stv,ftv)
    (op,v) (dst,addr+off) (su,G,tn,z)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all_then assume_tac assign_name_memory_bytes_mods >>
  `type_widens_to (get_tenv cx) (expr_type e) fty` by
    simp[type_widens_to_def,well_formed_type_def] >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_state >>
  drule_then (strip_assume_tac) stmt_state_rel_local_ptrs_alloca >>
  drule_all_then assume_tac alloca_site_registered_below >>
  `addr+off+type_memory_size ftv < dimword (:256) /\
   addr+off+type_memory_size ftv <= z.vs_alloca_next` by decide_tac >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  Cases_on `is_word_type fty`
  >- (drule_all_then assume_tac compileEnvTheory.type_widens_to_word >>
      `is_word_type (expr_type e)` by metis_tac[] >>
      drule_all_then assume_tac field_word_lowered >>
      `value_has_type ftv v` by fs[value_runtime_typed_def] >>
      `eval_operand op z = SOME (typed_val_to_w256 ftv v)` by
        metis_tac[expr_post_typed_stack_operand] >>
      qexists_tac `ftv` >> simp[struct_operand_mods_def,cj 1 value_has_type_val_wf]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  drule_all_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `pt` (qx_choose_then `rt` (map_every assume_tac o CONJUNCTS)))))
    copy_read_physical_type_gas_obs_mods >>
  `value_has_type ftv v` by metis_tac[type_widens_to_value_has_type,optionTheory.SOME_11] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `?sw. eval_operand op z = SOME sw /\
    (!m. mem_agree_outside tn.t_mem z.vs_memory m ==> val_in_memory rt v (w2n sw) m)` by
    (irule field_read_robust_nonword >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G`,`ce`,`cx`,`e`,`ee`,`pt`,`si`,`su`] >> asm_simp_tac bool_ss []) >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac alloca_room_next_lt >>
  qexists_tac `rt` >> simp[struct_operand_mods_def,cj 1 value_has_type_val_wf] >>
  `0 < type_memory_size rt ==> type_memory_size rt + w2n sw <= z.vs_alloca_next` by
    (qpat_x_assum `_ ==> !r w. _` (drule_then (qspecl_then [`rt`,`sw`] mp_tac)) >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  conj_tac
  >- (Cases_on `type_memory_size rt = 0` >- simp[wordsTheory.w2n_lt] >>
      `0 < type_memory_size rt` by decide_tac >>
      qpat_assum `0 < type_memory_size rt ==> _` (drule_then assume_tac) >> decide_tac) >>
  disch_tac >>
  qpat_assum `0 < type_memory_size rt ==> _` (drule_then assume_tac) >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (`ptr_buf_ok ce e op G z` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      `0 < type_memory_bytes ce (lowered_value_type ce e)` by simp[] >>
      `type_memory_size rt <= type_memory_bytes ce (lowered_value_type ce e)` by simp[] >>
      drule_all_then (qx_choose_then `src` strip_assume_tac)
        assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
      qexists_tac `src` >> asm_simp_tac bool_ss []) >>
  strip_tac >>
  `~is_bytestring_type (lowered_value_type ce e)` by metis_tac[type_widens_from_bytestring] >>
  `post_value_type ce e = lowered_value_type ce e` by metis_tac[type_widens_from_bytestring,
      typed_copy_bytestring_source] >>
  pure_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> irule field_read_disjoint >>
  asm_simp_tac bool_ss [] >>
  qexistsl [`H`,`aid`,`capacity`,`ce`,`ctx`,`cx`,`ee`,`func`,`op`,`si`,
            `lowered_value_type ce e`,`su`,`z`] >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name p k. local_region _ _ _ name p k ==> _ \/ _`
        (drule_then strip_assume_tac) >> decide_tac) >>
  qpat_x_assum `expr_val_at _ _ (post_value_type _ _) _ _ _ _ _ _` mp_tac >> simp[]
QED

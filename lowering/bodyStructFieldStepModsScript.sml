(* Continuation of one reached StructLit child at the paired compiler cuts. *)
Theory bodyStructFieldStepMods
Ancestors
  bodyStructFieldAddMods bodyStructFieldSimpleReadMods bodyStructFieldSlotReadMods
  bodyStructFieldRuntimeReadMods bodyStructFieldCtorReadMods bodyStructFieldChildFrameMods
  bodyStructFieldSmallStoreMods bodyStructFieldBytesStoreMods bodyStructFieldAggregateStoreMods
  bodyStructFieldExtendMods bodyStructFieldsCompileMods bodyFullIfExpReach
  bodyFullHashKeccakFixed bodyMemoryDefs bodyInvCodeProps bodyAssignNameLinkedSetup
  bodyWriteSubscriptSourceMods exprBodyPreProps exprSimFullBundleProps exprOperandVar
  exprSimWordArgs wordArgsPtr exprSimProps loweringShapeDefs bodyPtrMakeArrayMemoryFrame
  exprSimMemDefs exprLoweringProps bodyFullPostsMods bodyFullShadowBodyInv
  emitHelperProps freshWrites valueEncodingTyping valueCopyBytes exprSimCopy
  stateRelProj allocaSiteResource vyperEvalExprPreservesScopesDom
  bodySimStmtFacts vyperTypeArgFits vyperTypeInvariants vyperTypeSystem
  fragGasOriginPtrLoop venomState venomMemDefs words list finite_map pair
  loweringPosts bodyPtrDefs context abiDecodeStaticProps representationCleanPtr ptrDiscipline
  bodyStructFieldCutsMods vyperStorageFootprint exprSimHypsDefs
  vyperTypeEvalCaseProofs exprSimSource exprLowering vyperAST

Theorem field_preserve_cells[local]:
  wb_frame ce es ee si s z /\ ghost_kept_at lo ce es si Gi ti s G tn /\
  FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\ aid < si.cs_next_id /\
  (!name p k. local_region ce es.scopes s name p k ==>
    addr+capacity <= p \/ p+k <= addr) /\
  EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\ off <= capacity /\
  literal_prefix_ok cells ti s ==>
  literal_prefix_ok cells tn z
Proof
  pure_rewrite_tac [wb_frame_def, ghost_kept_at_def] >> strip_tac >>
  `mem_bytes_at addr capacity z.vs_memory = mem_bytes_at addr capacity s.vs_memory` by
    (qpat_assum `!a b n. _ ==> mem_bytes_at b n _ = _`
       (qspecl_then [`aid`,`addr`,`capacity`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  irule literal_prefix_transport >> qexistsl [`s`,`ti`] >> simp[] >>
  rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac literal_prefix_lookup >>
  `addr <= p /\ p+k <= addr+off` by
    (qpat_assum `EVERY _ cells` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(tv,v,p,k)` mp_tac) >> simp[]) >>
  gen_tac >> strip_tac >> irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl [`ti.t_mem`,`tn.t_mem`,`s.vs_memory`,`z.vs_memory`,`k`] >>
  simp[] >> reverse conj_tac
  >- (irule mem_bytes_at_bytewise >> rpt strip_tac >> irule mem_bytes_at_eq_byte >>
      qexistsl [`addr`,`capacity`] >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!a b n i. _ ==> i IN ti.t_mem`
    (qspecl_then [`aid`,`addr`,`capacity`,`i`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  disch_then ACCEPT_TAC
QED

Theorem field_prefix_landing[local]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (Hi,Di,es,si,Gi,ti,s) cells off /\
  stmt_state_rel H0 ctx func ce cx ees sf /\
  stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods D lo d ce cx ee G tn z /\
  wb_frame ce es ee si s z /\ ghost_kept_at lo ce es si Gi ti s G tn /\
  local_ptrs_reserved ce fr /\ local_ptrs_reserved ce si /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  si.cs_next_id <= su.cs_next_id /\ si.cs_next_var <= su.cs_next_var /\
  ~z.vs_halted /\ expr_sim_full_endpoint func su s z /\
  (pure ==> pure_frame ce func es si s z) ==>
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (H,D,ee,su,G,tn,z) cells off
Proof
  pure_rewrite_tac [struct_prefix_mods_def] >> strip_tac >>
  `fr.cs_next_id <= si.cs_next_id` by decide_tac >>
  `wb_frame ce ees ee fr sf z` by metis_tac[wb_frame_trans] >>
  `ghost_kept_at lo ce ees fr Gf tnf sf G tn` by metis_tac[ghost_kept_at_wb_trans] >>
  drule_all_then assume_tac field_preserve_cells >>
  `lookup_var root z = SOME (n2w addr)` by metis_tac[wb_frame_vars] >>
  `ptr_covers G tn root z capacity` by
    (qpat_assum `ghost_kept_at lo ce es si Gi ti s G tn`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `!x. not_fresh_at si x ==> FLOOKUP G x = _ /\ _`
       (qspec_then `root` (drule_then strip_assume_tac)) >>
     qpat_assum `ptr_covers Gi ti root s capacity` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def]) >>
  `FLOOKUP z.vs_allocas aid = SOME (addr,capacity)` by fs[wb_frame_def] >>
  `!name p k. local_region ce ee.scopes z name p k <=> local_region ce es.scopes s name p k` by
    metis_tac[wb_frame_local_regions] >>
  `expr_sim_full_endpoint func su sf z` by fs[expr_sim_full_endpoint_def] >>
  `pure ==> pure_frame ce func ees fr sf z` by
    (strip_tac >> irule pure_frame_trans >> simp[] >>
     qexistsl [`es`,`si`,`s`] >> fs[wb_frame_def]) >>
  `MAP FDOM ees.scopes = MAP FDOM ee.scopes` by metis_tac[] >>
  `not_fresh_at su root` by metis_tac[not_fresh_at_mono] >>
  `aid < su.cs_next_id /\ fr.cs_next_var <= su.cs_next_var` by decide_tac >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem field_vv_frame[local]:
  vv_post_mods H ctx func ce cx e es si sm s ee tv vv z ==>
  stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
  storage_well_formed_on cx ee (FST H) /\ wb_frame ce es ee si s z /\
  (~expr_has_effect e ==> pure_frame ce func es si s z)
Proof
  simp_tac bool_ss [vv_post_mods_def, wb_frame_def] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem field_store_run[local]:
  compile_store_memory ce op (Var dst) dty sty sa = ((),sb) /\
  struct_operand_mods (ce,tenv,sty,dty,stv,dtv) (op,v) (dst,addr) (sa,G,tn,s) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    struct_store_effects func (sa,G,tn,s) (sb,G',tn',t) (addr,dtv,v)
Proof
  strip_tac >> Cases_on `is_word_type dty \/ type_memory_size stv = 0`
  >- (irule struct_field_small_store_mods >> simp[] >>
      qexistsl [`ce`,`dst`,`dty`,`op`,`stv`,`sty`,`tenv`] >> simp[]) >>
  fs[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `0 < type_memory_size stv` by simp[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  Cases_on `is_bytestring_type dty`
  >- (irule struct_field_bytes_store_mods >> simp[] >>
      qexistsl [`ce`,`dst`,`dty`,`op`,`stv`,`sty`,`tenv`] >>
      simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule struct_field_aggregate_store_mods >> simp[] >>
  qexistsl [`ce`,`dst`,`dty`,`op`,`stv`,`sty`,`tenv`] >>
  simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The prefix transition from the child entry to the ADD cursor keeps the
   child's original anchor, rather than reinterpreting the VV as a value. *)
Theorem field_prefix_vv[local]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (Hi,Di,es,si,Gi,ti,s) cells off /\
  stmt_state_rel H0 ctx func ce cx ees sf /\
  vv_post_mods H ctx func ce cx e es si su s ee tv vv z /\
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
  strip_tac >> drule_then strip_assume_tac field_vv_frame >>
  irule field_prefix_landing >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (qexists `H0` >> first_assum ACCEPT_TAC) >>
  qexistsl [`Di`,`Gi`,`Hi`,`es`,`s`,`si`,`ti`] >> simp[]
QED

Theorem field_store_landing[local]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (Hi,Di,es,si,Gi,ti,s) cells off /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
       (root,addr,capacity,aid) (H,DF H,ee,su,G,tn,z) cells off) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  struct_operand_mods (ce,get_tenv cx,lowered_value_type ce e,fty,stv,ftv)
    (op,v) (dst,addr+off) (su,G,tn,z) /\
  compile_store_memory ce op (Var dst) fty (lowered_value_type ce e) su = ((),ss) /\
  fn_has_code su ss func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx ce cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre_mods mods ce cx env e es /\
  ci_mono su ss /\ si.cs_next_var <= su.cs_next_var /\
  off+type_memory_size ftv <= capacity /\ local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s /\ wb_frame ce es ee si s z /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,Gi,ti) marks (OK t,G1,tn1) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK z,G,tn)) ==>
  ?u G2 tn2.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2) /\
       struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
         (root,addr,capacity,aid) (H,DF H,ee,ss,G2,tn2,u)
         (cells ++ [(ftv,v,addr+off,type_memory_size ftv)]) (off+type_memory_size ftv)) /\
    value_has_type ftv v /\ ~u.vs_halted /\ local_ptrs_reserved ce ss /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
    return_buf_frame d ce ss u /\
    (!fn inst t'. frag_reachable ctx func u fn inst t' ==> dalloca_fmp_headroom inst t')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
    (drule_then assume_tac) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z /\
   allocas_from lo z /\ lo <= z.vs_alloca_next /\ ~z.vs_halted /\
   alloca_history func z /\ z.vs_current_bb = su.cs_current_bb /\
   z.vs_inst_idx = LENGTH su.cs_current_insts` by
    fs[struct_prefix_mods_def, ghost_inv_at_mods_def, expr_sim_full_endpoint_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`u`,`G2`,`tn2`] strip_assume_tac))
    field_store_run >>
  suspend "prefix"
QED

Resume field_store_landing[prefix]:
  `local_ptrs_reserved ce su` by (irule local_ptrs_reserved_next_var >> qexists `si` >> simp[]) >>
  `su.cs_next_var <= ss.cs_next_var` by fs[ci_mono_def] >>
  `si.cs_next_var <= ss.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce ss` by (irule local_ptrs_reserved_next_var >> qexists `si` >> simp[]) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at su x /\ not_fresh_at ss x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `si` >> simp[]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at su x /\ not_fresh_at ss x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `si` >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
         (root,addr,capacity,aid) (H,DF H,ee,ss,G2,tn2,u)
         (cells ++ [(ftv,v,addr+off,type_memory_size ftv)]) (off+type_memory_size ftv)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ _ _ _`
       (drule_then assume_tac) >>
     irule struct_field_store_extends_prefix_mods >> simp[] >> qexistsl [`G`,`z`,`su`,`tn`] >>
     simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`G`,`z`,`tn`] >> simp[]) >>
  qexistsl [`u`,`G2`,`tn2`] >> conj_tac >- simp[] >>
  conj_tac >- fs[struct_operand_mods_def] >>
  suspend "tail"
QED

Resume field_store_landing[tail]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (metis_tac[body_inv_no_phi_mods]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `!fn inst s'. frag_reachable ctx func t fn inst s' ==> dalloca_fmp_headroom inst s'` by
    (qpat_assum `gas_origin_ptr_path _ (s,Gi,ti) marks (OK t,G1,tn1)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (fn th => rpt strip_tac >> irule th) >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] _`
    (drule_then assume_tac) >>
  `!fn inst s'. frag_reachable ctx func u fn inst s' ==> dalloca_fmp_headroom inst s'` by
    (qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (fn th => rpt strip_tac >> irule th) >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ (_,_,_,ss,_,_,u) _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def])) >>
  `return_buf_frame d ce ss u` suffices_by
    (strip_tac >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  qpat_assum `struct_store_effects _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [struct_store_effects_def]) >>
  `return_buf_frame d ce su z` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`si`] >> simp[] >>
     rpt strip_tac >> drule_all wb_frame_vars >> simp[]) >>
  irule return_buf_frame_frame >> qexistsl [`ce`,`z`,`su`] >> simp[] >>
  fs[expr_sim_full_endpoint_def, typedMemoryCopyTheory.typed_copy_state_frame_def] >> metis_tac[]
QED

Finalise field_store_landing

(* The copying reads agree on this physical certificate, independently of
   whether the source was a storage slot or an immutable in code/memory. *)
Theorem field_copy_operand[local]:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) anchor
    (root,addr,capacity,aid) (H,D,ee,su,G,tn,z) cells off /\
  off + type_memory_size ftv <= capacity /\
  ~is_word_type fty /\ type_widens_to (get_tenv cx) (lowered_value_type ce e) fty /\
  evaluate_type (get_tenv cx) fty = SOME ftv /\
  type_memory_bytes ce fty = type_memory_size ftv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  value_has_type stv v /\ op_taint tn op = {} /\ eval_operand op z = SOME w /\
  w2n w + type_memory_size stv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem z.vs_memory m ==> val_in_memory stv v (w2n w) m) /\
  (type_memory_size stv = 0 \/ w2n w + type_memory_size stv <= z.vs_alloca_next) /\
  (0 < type_memory_size stv ==>
    ?src. op = Var src /\ not_fresh_at su src /\ ptr_covers G tn src z (type_memory_size stv)) /\
  (w2n w + val_footprint stv v <= addr \/ addr+capacity <= w2n w) /\
  not_fresh_at su dst /\ lookup_var dst z = SOME (n2w (addr+off)) /\
  ptr_covers G tn dst z (type_memory_size ftv) ==>
  struct_operand_mods (ce,get_tenv cx,lowered_value_type ce e,fty,stv,ftv)
    (op,v) (dst,addr+off) (su,G,tn,z)
Proof
  PairCases_on `anchor` >>
  simp_tac bool_ss [struct_prefix_mods_def,struct_operand_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type ftv v` by (drule_all type_widens_to_value_has_type >> simp[]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `addr+capacity <= z.vs_alloca_next` by (drule_all alloca_site_registered_below >> simp[]) >>
  `addr+off+type_memory_size ftv < dimword (:256) /\
   addr+off+type_memory_size ftv <= z.vs_alloca_next` by decide_tac >>
  simp[cj 1 value_has_type_val_wf] >> qexists `w` >> simp[] >>
  rpt strip_tac >> decide_tac
QED

val read_after_add = ``
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  unwrap_value ce vv sn = (op,su) /\
  ci_mono si sm /\ ci_mono sm sn /\ ci_mono sn su /\ fn_has_code sn su func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si sn s ee tv vv a /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv a /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Ga ta a /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e x Ga a) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand Ga a) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            eval_operand (vv_operand vv) a = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es si Gi ti s Ga ta /\
  ~a.vs_halted /\ expr_sim_full_endpoint func sn s a /\
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (Hi,Di,es,si,Gi,ti,s) cells off /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
      (root,addr,capacity,aid) (H,DF H,ee,sn,Ga,ta,a) cells off) /\
  stmt_state_rel H0 ctx func ce cx ees sf /\ (pure ==> ~expr_has_effect e) /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
  type_widens_to (get_tenv cx) (expr_type e) fty /\
  evaluate_type (get_tenv cx) fty = SOME ftv /\ type_memory_bytes ce fty = type_memory_size ftv /\
  off+type_memory_size ftv <= capacity /\
  not_fresh_at sn dst /\ lookup_var dst a = SOME (n2w (addr+off)) /\
  ptr_covers Ga ta dst a (type_memory_size ftv)``;

val read_done = ``?v z G tn stv.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,G,tn)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
        (root,addr,capacity,aid) (H,DF H,ee,su,G,tn,z) cells off) /\
    wb_frame ce es ee si s z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    struct_operand_mods (ce,get_tenv cx,lowered_value_type ce e,fty,stv,ftv)
      (op,v) (dst,addr+off) (su,G,tn,z)``;

Theorem field_read_simple[local]:
  ^read_after_add /\
  (is_word_type (expr_type e) \/ (?tag x. vv = StackValue tag x) \/
    (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\ ~is_word_type tag)) /\
  (~is_word_type (expr_type e) ==> ~is_word_type (post_value_type ce e)) ==> ^read_done
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `aid < si.cs_next_id` by fs[struct_prefix_mods_def] >>
  `a.vs_current_bb = sn.cs_current_bb /\ a.vs_inst_idx = LENGTH sn.cs_current_insts /\
   alloca_history func a /\ s.vs_alloca_next <= a.vs_alloca_next` by fs[expr_sim_full_endpoint_def] >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  mp_tac (Q.INST [`s` |-> `a`, `G` |-> `Ga`, `tn` |-> `ta`,
                  `s0` |-> `s`, `G0` |-> `Gi`, `tn0` |-> `ti`,
                  `Gi` |-> `Gf`, `ti` |-> `tnf`, `dty` |-> `fty`, `dtv` |-> `ftv`,
                  `ty` |-> `expr_type e`]
            struct_field_simple_read_mods) >>
  impl_tac
  >- (simp_tac bool_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  suspend "read"
QED

Resume field_read_simple[read]:
  disch_then strip_assume_tac >>
  rename1 `read_result cx tv ee = (INL v,ee)` >>
  rename1 `struct_operand_mods _ (op,v) _ (su,G,tn,z)` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  drule_then assume_tac exprSimWordArgsTheory.expr_post_frame >>
  qexistsl [`v`,`z`,`G`,`tn`,`stv`] >> simp[]
QED

Finalise field_read_simple

val copied_read = ``
  read_result cx tv ee = (INL v,ee) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,G,tn)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es si su s ee v op z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn z) /\
  ghost_kept_at lo ce es si Gi ti s G tn /\
  ~z.vs_halted /\ expr_sim_full_endpoint func su a z /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  value_has_type stv v /\ op_taint tn op = {} /\ eval_operand op z = SOME w /\
  w2n w + type_memory_size stv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem z.vs_memory m ==> val_in_memory stv v (w2n w) m) /\
  (type_memory_size stv = 0 \/ w2n w + type_memory_size stv <= z.vs_alloca_next) /\
  (0 < type_memory_size stv ==>
    ?src. op = Var src /\ not_fresh_at su src /\ ptr_covers G tn src z (type_memory_size stv)) /\
  (w2n w + val_footprint stv v <= addr \/ addr+capacity <= w2n w) /\
  (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x a /\
    FLOOKUP G x = FLOOKUP Ga x /\ op_taint tn (Var x) = op_taint ta (Var x)) /\
  ptr_covers G tn dst z (type_memory_size ftv)``;

Theorem field_copy_landing[local]:
  ^read_after_add /\ ~is_word_type (expr_type e) /\ ^copied_read ==> ^read_done
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `si.cs_next_id <= su.cs_next_id /\ si.cs_next_var <= su.cs_next_var /\
   sn.cs_next_var <= su.cs_next_var` by fs[ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_sim_full_endpoint func su s z` by fs[expr_sim_full_endpoint_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
      (root,addr,capacity,aid) (H,DF H,ee,su,G,tn,z) cells off` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_all struct_field_prefix_after_read_mods >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  drule_then assume_tac exprSimWordArgsTheory.expr_post_frame >>
  `s.vs_alloca_next <= z.vs_alloca_next` by fs[expr_sim_full_endpoint_def] >>
  `~is_word_type fty` by
    (qpat_assum `type_widens_to _ (expr_type e) fty` mp_tac >>
     pure_rewrite_tac[type_widens_to_def] >> strip_tac
     >- fs[] >> drule exprSimLayoutTransportTheory.compatible_word_type >> simp[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) fty` by
    (drule_all typedCopyCompatibilityTheory.type_widens_to_trans >> simp[]) >>
  `not_fresh_at su dst` by (irule not_fresh_at_mono >> qexists `sn` >> simp[]) >>
  `lookup_var dst z = SOME (n2w (addr+off))` by
    (qpat_assum `!x. not_fresh_at sn x ==> lookup_var x z = _ /\ _`
      (drule_then strip_assume_tac) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ (_,_,_,su,_,_,z) _ _`
    (drule_then assume_tac) >>
  drule_all_then assume_tac field_copy_operand >>
  qexistsl [`v`,`z`,`G`,`tn`,`stv`] >> asm_rewrite_tac[]
QED

val copy_result = ``?v z G tn stv w. ^copied_read``;

Theorem field_read_copied[local]:
  ^read_after_add /\ ~is_word_type (expr_type e) /\ vv = LocatedValue tag p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/ p.ptr_location = LocCode) ==>
  ^copy_result
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ (_,_,_,sn,_,_,a) _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def])) >>
  `EVERY (\(tv,v,b,n). addr <= b /\ b+n <= addr+capacity) cells` by
    (fs[EVERY_MEM] >> rpt strip_tac >> pairarg_tac >> simp[] >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  `a.vs_current_bb = sn.cs_current_bb /\ a.vs_inst_idx = LENGTH sn.cs_current_insts /\
   alloca_history func a` by fs[expr_sim_full_endpoint_def] >>
  qpat_x_assum `vv = LocatedValue tag p` SUBST_ALL_TAC >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "immutables" >>
  suspend "slots"
QED

(* Bind the cuts by role: all copy routes share the same input cursor,
   but the endpoint and capacity variables differ in the slot certificate. *)
fun copy_cut renames th =
  mp_tac (Q.INST ([`s` |-> `a`, `G` |-> `Ga`, `tn` |-> `ta`,
                   `ty` |-> `expr_type e`, `field_size` |-> `type_memory_size ftv`] @ renames) th) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC);

fun copy_witnesses tac =
  disch_then (qx_choosel_then [`v`,`z`,`G`,`tn`,`stv`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`v`,`z`,`G`,`tn`,`stv`,`w`] >>
  simp_tac bool_ss [] >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE tac);

Resume field_read_copied[slots]:
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by fs[] >>
  copy_cut [`entry` |-> `s`, `cap` |-> `capacity`] struct_field_slot_read_mods >>
  copy_witnesses (rpt strip_tac >> simp[])
QED

Resume field_read_copied[immutables]:
  Cases_on `ce.ce_is_ctor`
  >- (`?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand p.ptr_operand a = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
             val_in_memory rt v (w2n w) mem)` suffices_by
        (disch_tac >> copy_cut [`s0` |-> `s`] struct_field_ctor_read_mods >>
         copy_witnesses (simp[expr_sim_full_endpoint_def])) >>
      fs[vv_location_def, vv_operand_def]) >>
  copy_cut [`s0` |-> `s`] struct_field_runtime_read_mods >>
  copy_witnesses (simp[expr_sim_full_endpoint_def])
QED

Finalise field_read_copied

Theorem field_read_dispatch[local]:
  ^read_after_add /\
  (~is_word_type (expr_type e) ==> ~is_word_type (post_value_type ce e)) ==> ^read_done
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type (expr_type e)`
  >- (mp_tac field_read_simple >> impl_tac
      >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `~is_word_type (post_value_type ce e)` by
    (qpat_assum `~is_word_type (expr_type e) ==> _` (drule_then ACCEPT_TAC)) >>
  Cases_on `?tag x. vv = StackValue tag x`
  >- (mp_tac field_read_simple >> impl_tac
      >- (simp_tac bool_ss [] >> rpt conj_tac >>
          (first_assum ACCEPT_TAC ORELSE (disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC))) >> simp[]) >>
  `?tag p. vv = LocatedValue tag p` by (Cases_on `vv` >> fs[]) >>
  rename1 `vv = LocatedValue tag p` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
  `vv_holds_mods ce cx (post_value_type ce e) tv (LocatedValue tag p) ee a` by
    (qpat_assum `vv = LocatedValue tag p` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (qpat_x_assum `vv_holds_mods _ _ _ _ (LocatedValue _ _) _ _` mp_tac >>
      simp[vv_holds_mods_def,vv_holds_def] >> strip_tac >>
      `~is_word_type tag` by fs[is_bytestring_word_type] >>
      mp_tac field_read_simple >> impl_tac
      >- (simp_tac bool_ss [] >> rpt conj_tac >>
          (first_assum ACCEPT_TAC ORELSE
           (disj2_tac >> disj2_tac >> qexistsl [`tag`,`p`] >> simp[]))) >> simp[]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/ p.ptr_location = LocCode`
    suffices_by
    (disch_tac >> mp_tac field_read_copied >> impl_tac
     >- (simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qx_choosel_then [`v`,`z`,`G`,`tn`,`stv`,`w`]
       (map_every assume_tac o CONJUNCTS)) >>
     mp_tac field_copy_landing >> impl_tac
     >- (simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  Cases_on `p.ptr_location` >> fs[vv_holds_mods_def,vv_holds_def]
QED

Theorem field_step_layout[local]:
  expr_body_pre_mods mods ce cx env e es /\
  arg_type_fits (expr_type e) fty /\ evaluate_type (get_tenv cx) fty = SOME ftv ==>
  type_memory_bytes ce fty = type_memory_size ftv /\
  type_widens_to (get_tenv cx) (expr_type e) fty /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
  (~is_word_type (expr_type e) ==> ~is_word_type (post_value_type ce e))
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_all_then assume_tac assign_name_memory_bytes_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[type_widens_to_def,well_formed_type_def] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `well_formed_type (get_tenv cx) (expr_type e)` by
    (drule_all logArgumentTypeEvalTheory.checked_expr_type_well_formed >> simp[]) >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >> simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
  disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac))
  >- simp[type_widens_to_def, post_value_type_lowered]
  >- simp[type_widens_to_def, post_value_type_def, is_bytestring_word_type] >>
  qpat_x_assum `e = Call _ (IntCall _) _ _` SUBST_ALL_TAC >>
  PairCases_on `fid` >>
  qpat_x_assum `well_typed_expr env _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  drule_all_then assume_tac expr_sim_inv_mods_return_type >>
  fs[lowered_value_type_def,expr_type_def,post_value_type_def] >>
  strip_tac >> Cases_on `is_bytestring_type ty` >> simp[] >>
  qpat_assum `type_widens_to _ _ _` mp_tac >>
  pure_rewrite_tac[type_widens_to_def] >> strip_tac
  >- fs[] >> drule exprSimLayoutTransportTheory.compatible_word_type >> simp[]
QED

(* Execute the real cuts already fixed by the paired compilation.  The
   source reader and the tail receive the same head value and end state. *)
Theorem struct_field_success_step_mods:
  struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
    (root,addr,capacity,aid) (Hi,Di,es,si,Gi,ti,s) cells off /\
  stmt_state_rel H0 ctx func ce cx ees sf /\ (pure ==> ~expr_has_effect e) /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) fty (lowered_value_type ce e) su = ((),ss) /\
  ci_mono si sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su ss /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\ fn_has_code su ss func /\
  fn_inst_ids_distinct func /\ contract_inv mods exps ctx ce cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre_mods mods ce cx env e es /\
  (eval_expr cx e (es with gas_obs := gs) = (INL tv,ee)) /\
  arg_type_fits (expr_type e) fty /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
  off+type_memory_size ftv <= capacity /\ storage_trace_domain cx st0 ee.storage_trace /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s /\
  (!fn inst t'. frag_reachable ctx func s fn inst t' ==> dalloca_fmp_headroom inst t') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,Gi,ti) marks (OK t,G1,tn1)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si sm s ee tv vv t /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G1 tn1 t) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G1 tn1 t /\
  (!tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e x G1 t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G1 t) /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\ ~is_bytestring_type (post_value_type ce e) ==>
    vv_own ce cx (post_value_type ce e) si sm ee tv vv t) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es si Gi ti s G1 tn1 /\ ~t.vs_halted /\ expr_sim_full_endpoint func sm s t ==>
  ?v u G2 tn2. read_result cx tv ee = (INL v,ee) /\ value_has_type ftv v /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,G2,tn2) /\
       struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
         (root,addr,capacity,aid) (H,DF H,ee,ss,G2,tn2,u)
         (cells ++ [(ftv,v,addr+off,type_memory_size ftv)]) (off+type_memory_size ftv)) /\
    ~u.vs_halted /\ local_ptrs_reserved ce ss /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
    return_buf_frame d ce ss u /\
    (!fn inst t'. frag_reachable ctx func u fn inst t' ==> dalloca_fmp_headroom inst t')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac field_step_layout >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `si.cs_next_id <= sm.cs_next_id /\ si.cs_next_var <= sm.cs_next_var /\
   si.cs_next_id <= sn.cs_next_id /\ si.cs_next_var <= sn.cs_next_var /\
   si.cs_next_var <= su.cs_next_var` by fs[ci_mono_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
      (root,addr,capacity,aid) (H,DF H,ee,sm,G1,tn1,t) cells off` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_all field_prefix_vv >> simp[]) >>
  suspend "add"
QED

Resume struct_field_success_step_mods[add]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> struct_prefix_mods _ _ _ (_,_,_,sm,_,_,t) _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [struct_prefix_mods_def])) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
   alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next` by fs[expr_sim_full_endpoint_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sm p` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC (cj 1 compiler_compile_var)) >>
  `op_taint tn1 (Var root) = {} /\ ?b n. FLOOKUP G1 root = SOME (b,n)` by
    fs[ptr_covers_def] >>
  rename1 `FLOOKUP G1 root = SOME (region_base,cap)` >>
  `w2n ((n2w addr):256 word) + off < dimword (:256)` by
    (`addr < dimword (:256)` by decide_tac >>
     `w2n ((n2w addr):256 word) = addr` by simp[] >> decide_tac) >>
  mp_tac (Q.INST [`s` |-> `t`, `s0` |-> `s`, `G` |-> `G1`, `tn` |-> `tn1`,
                  `a` |-> `n2w addr`, `out` |-> `dst`, `n` |-> `type_memory_size ftv`]
            struct_field_add_mods) >>
  impl_tac
  >- (simp_tac bool_ss [] >> rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       (rpt strip_tac >>
        qpat_assum `tv = Value _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
        qpat_assum `!v. tv = Value v /\ _ ==> vv_own _ _ _ _ _ _ _ _ _`
          (drule_all_then ACCEPT_TAC)))) >>
  disch_then (qx_choosel_then [`a`,`Ga`,`ta`] (map_every assume_tac o CONJUNCTS)) >>
  `expr_sim_full_endpoint func sn s a` by fs[expr_sim_full_endpoint_def] >>
  `lookup_var dst a = SOME (n2w (addr+off))` by fs[word_add_n2w] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (ees,fr,sf,Gf,tnf)
      (root,addr,capacity,aid) (H,DF H,ee,sn,Ga,ta,a) cells off` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ a /\ _`
       (drule_then strip_assume_tac) >>
     drule_all field_prefix_vv >> simp[]) >>
  suspend "read_and_store"
QED

Resume struct_field_success_step_mods[read_and_store]:
  mp_tac field_read_dispatch >> impl_tac
  >- (simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`v`,`z`,`G`,`tn`,`stv`] (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,Gi,ti) marks (OK t,G1,tn1) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK z,G,tn)` by
    (rpt strip_tac >- (first_assum drule >> simp[]) >>
     irule gas_origin_ptr_path_trans >> qexistsl [`Ga`,`a`,`ta`] >>
     conj_tac
     >- (qpat_assum `!D l e. allocas_from l t ==> gas_origin_ptr_path _ _ _ _`
           (qspecl_then [`DF H`,`lo`,`explicit`] mp_tac) >> simp[]) >> simp[]) >>
  mp_tac field_store_landing >> impl_tac
  >- (simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`u`,`G2`,`tn2`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`v`,`u`,`G2`,`tn2`] >>
  simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise struct_field_success_step_mods

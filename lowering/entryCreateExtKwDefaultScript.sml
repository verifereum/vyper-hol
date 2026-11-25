(* The nonword default keyword evaluates its child before allocating its
   private result buffer. The call's later return decoder is not in this cut. *)
Theory entryCreateExtKwDefault
Ancestors
  entryCreateFocusSpec entryCreateCompositeFocus entryCreateEffectFocus
  createSizeOperandMutual createSizeCutCode createSizeCutOpens createSizeLocationCode createSizeTypedCopyCode
  abiEncodeMaterialize assignEffectfulIndexPhysical bodyMemSnapshotSourceLocation
  immutableDeployPhysicalSource loweringPosts
  createCtorMaterializeSource createCtorMaterializeStore createCtorMaterializePhysical
  gasShadowCompile gasShadowCompileStmtHelpers gasShadowState
  exprSimUnwrap exprLowering exprLoweringProps fragExec context compileEnv pair
  createCtorSegmentArrival createCtorObservedSilence createMarkedPath createSizePrefixReplay
  entryCreatePathScope entryCreateCompletedCut fragGasOrigin fragGasOriginPtr abiEncoderProps
  venomExecSemantics venomExecProofs venomInst venomState gasEvents relation list
  abiEncodeArgsCase exprSimHyps exprOperandVar bodyMemoryDefs arithmetic words finite_map
  bodyFullPathHistory stateRelProj targetPureSourceFrame vyperState
  exprSimProps bodyPtrDefs entryCreateScopedBind entryCreateNativeFirstExit
  aggregateEvaluatedLayout stmtLoweringMono sum vyperStorageFootprint valueCopyBytes
  fragGasOriginPtrLoop gasOriginPtrLabels loweringStateRelDefs abiBufferAllocationCode
  freshWrites bodyFullHashKeccakFixed bodyFullIfExpReach fragGasPath
  gasSummary gasExemptCert exprSimDefs stmtSimProps vyperStorageTrace exprSimMemorySource
  entryCreatePendingScope entryCreateStmtCases createSizeCutRegion
  exprSimAbiEncodeObliviousCode entryCreateOperandReplay
  entryCreateIntervalLayout entryCreateRegionLift entryCreateBodyCut s1PrefixDefs

Theorem extcall_kw_memory_default_compile:
  ~is_word_type rt /\
  compile_ext_call_kwarg compile_expr ce rt EKDefault e a = ((op,dt),b) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T ce) rt EKDefault
    (gas_shadow_expr e) ha = ((op,dt),hb) /\
  gas_shadow_state a ha /\ fn_has_code a b f /\ fn_has_code ha hb hf ==>
  ?vv m hm.
    dt = lowered_value_type ce e /\
    compile_expr ce (expr_type e) e a = (vv,m) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) ha = (vv,hm) /\
    compile_materialize_vv ce dt vv m = (op,b) /\
    gas_shadow_state m hm /\
    fn_has_code a m f /\ fn_has_code m b f /\ fn_has_code ha hm hf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_expr ce (expr_type e) e a` >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,m)` >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) ha` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) ha = (hv,hm)` >>
  `hv = vv /\ gas_shadow_state m hm` by
    (`gas_shadow_compiles (compile_expr ce (expr_type e) e)
       (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_compile_expr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`a`,`ha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  Cases_on `compile_materialize_vv ce (lowered_value_type ce e) vv m` >>
  Cases_on `compile_materialize_vv ce (lowered_value_type ce e) vv hm` >>
  gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  `cs_extends a m /\ cs_extends ha hm` by metis_tac[compile_expr_extends] >>
  `cs_extends m b /\ cs_extends hm hb` by
    metis_tac[ci_mono_def, ci_mono_compile_materialize_vv, SND] >>
  metis_tac[fn_has_code_split]
QED

(* Positional materialization uses a retagged VV. On this selected
   value the retagging gives exactly the same unwrap program. *)
Theorem extcall_kw_default_same_unwrap:
  expr_body_pre ce cx env e es /\ compile_expr ce ty e a = (vv,m) /\
  vv_post H C f ce cx e es a m s0 ee tv vv s ==>
  unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) = unwrap_value ce vv
Proof
  strip_tac >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee s` by fs[vv_post_def] >>
  drule immutable_rhs_post_physical_classify >> strip_tac >>
  `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) = unwrap_value ce vv` by
    (irule snapshot_retag_unwrap >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     metis_tac[snapshot_changed_type_location]) >>
  Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_with_type_def]
QED

Theorem extcall_kw_default_materialize_code:
  compile_materialize_vv ce dt vv m = (op,b) ==>
  ?buf n src c.
    compile_alloc_buffer (type_memory_bytes ce dt) m = (buf,n) /\
    unwrap_value ce vv n = (src,c) /\
    compile_store_memory ce src buf.buf_operand dt dt c = ((),b) /\
    op = buf.buf_operand /\
    create_cut_code {} m n /\ create_cut_code {} n c /\ create_cut_code {} m c /\
    create_cut_code {} c b /\ create_cut_code {} m b
Proof
  strip_tac >> drule materialize_compile_trace >> strip_tac >>
  rename1 `compile_alloc_buffer _ m = (buf,n)` >>
  rename1 `unwrap_value ce vv n = (src,c)` >>
  `create_cut_code {} m n` by metis_tac[create_alloc_buffer_cut_code,SND] >>
  `create_cut_code {} n c` by metis_tac[create_unwrap_cut_code,SND] >>
  `create_cut_code {} c b` by metis_tac[create_store_memory_cut_code,SND] >>
  metis_tac[create_cut_code_join]
QED

(* Read the already selected compiler-band execution as marked edges.
   No new endpoint or pointer ghosts are chosen by this projection. *)
Theorem extcall_kw_segment_edge[local]:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ ctor_segment_fetch f s = SOME i /\ i.inst_opcode <> INVOKE /\
  ctor_segment_next f s i = SOME t ==>
  ~t.vs_halted /\ ?ms. gas_origin_edge F E C f s ms (OK t)
Proof
  strip_tac >> fs[ctor_segment_fetch_def, AllCaseEqs()] >>
  Cases_on `step_inst_base i s` >>
  gvs[ctor_segment_next_def, ctor_segment_entry_def, AllCaseEqs()] >>
  rename1 `step_inst_base i s = OK mid` >>
  `~mid.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  `step_inst 0 C i s = OK mid` by simp[step_inst_non_invoke] >>
  TRY (rename1 `lookup_block mid.vs_current_bb f.fn_blocks = SOME target` >>
       `phi_prefix_length target.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
       gvs[eval_phis_no_phi]) >>
  simp[gas_origin_edge_def] >> qexists_tac `0` >> simp[eval_phis_no_phi] >> metis_tac[]
QED

Theorem extcall_kw_segment_marked[local]:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          b.cs_next_id <= i.inst_id) ==>
  !s t. RTC (\u v. ?i. ctor_segment_fetch f u = SOME i /\
               a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
               i.inst_opcode <> INVOKE /\ ctor_segment_next f u i = SOME v) s t ==>
        ~s.vs_halted ==> ~t.vs_halted /\ ?ms. create_expr_prefix a b E C f s ms t
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT_RIGHT1 >> conj_tac
  >- (rpt strip_tac >> qexists_tac `[]` >> simp[]) >>
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  disch_tac >> rename1 `ctor_segment_next f u i = SOME v` >>
  `~u.vs_halted` by metis_tac[] >>
  drule_all extcall_kw_segment_edge >>
  disch_then (qspecl_then [`E`,`C`] strip_assume_tac) >> simp[] >>
  `create_prefix_step a b E C f u ms v` by
    (fs[ctor_segment_fetch_def, AllCaseEqs()] >>
     simp[create_prefix_step_def,frag_ids_def] >>
     metis_tac[arithmeticTheory.NOT_LESS]) >>
  `create_expr_prefix a b E C f u ms v` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >> simp[create_marked_edge_def]) >>
  metis_tac[create_expr_prefix_append]
QED

Theorem extcall_kw_segment_scope:
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          b.cs_next_id <= i.inst_id) /\
  ~s.vs_halted /\ create_operand_at b t /\
  RTC (\u v. ?i. ctor_segment_fetch f u = SOME i /\
               a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
               i.inst_opcode <> INVOKE /\ ctor_segment_next f u i = SOME v) s t /\
  gas_origin_path T E C f s [] (OK t) ==>
  create_operand_full_scope a b E C f s [] (OK t)
Proof
  strip_tac >> drule_all extcall_kw_segment_marked >>
  disch_then (qspecl_then [`E`,`C`] strip_assume_tac) >>
  qpat_assum `create_expr_prefix _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[create_expr_prefix_marked]) >> strip_tac >>
  `ms = []` by
    (irule ctor_observed_cut_silent >>
     qexistsl_tac [`C`,`(b.cs_current_bb,LENGTH b.cs_current_insts)`,`E`,`f`,`t`,`s`] >>
     fs[create_operand_at_def] >>
     qpat_x_assum `RTC (create_marked_edge _) _ _` mp_tac >> match_mp_tac RTC_MONOTONE >>
     simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS]) >>
  fs[create_operand_full_scope_def, create_operand_at_def]
QED

Definition extcall_kw_memory_post_def:
  extcall_kw_memory_post (DF,lo,d,C,f) ce cx e (a,b,es,s0,G0,tn0,op)
    H v ee G tn t <=>
    stmt_state_rel H C f ce cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    create_operand_at b t /\ ~t.vs_halted /\
    alloca_history f t /\ (ctx_has_dalloca C ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d ce cx ee G tn t /\
    ghost_kept_at lo ce es a G0 tn0 s0 G tn /\
    return_buf_frame d ce b t /\ wb_frame ce es ee a s0 t /\
    MAP FDOM ee.scopes = MAP FDOM es.scopes /\
    (!x w. not_fresh_at a x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
    t.vs_labels = s0.vs_labels /\
    (!x. op = Var x ==> not_fresh_at b x) /\
    ptr_val_ok cx (lowered_value_type ce e) v op G tn t /\
    ptr_mem_ok cx (lowered_value_type ce e) v op G tn t /\
    ptr_buf_ok ce e op G t /\
    (!w. eval_operand op t = SOME w /\ type_memory_bytes ce (lowered_value_type ce e) <> 0 ==>
         w2n w + type_memory_bytes ce (lowered_value_type ce e) <= t.vs_alloca_next) /\
    (?w aid tv. eval_operand op t = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      val_wf tv v /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < b.cs_next_id /\
      (!n p sz. local_region ce ee.scopes t n p sz ==>
        regions_disjoint (w2n w) (type_memory_size tv) p sz))
End

(* Use the allocation/unwrap/store witnesses of the constructor producer,
   which runs the same materialize program after the selected VV result. *)
Theorem extcall_kw_default_suffix[local]:
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv m = (op,b) /\
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce a /\ fn_has_code m b f /\ fn_inst_ids_distinct f /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==> b.cs_next_id <= i.inst_id) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
      H (INL raw : eval_result + vyperState$exception) ee G tn s /\ storage_well_formed_on cx ee (FST H)) /\
  ~s.vs_halted /\ create_operand_at m s /\ return_buf_frame d ce a s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==> FLOOKUP s.vs_allocas aid = SOME row) /\
  s.vs_labels = s0.vs_labels ==>
  ?t Gt tt. create_operand_full_scope m b E C f s [] (OK t) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK t,Gt,tt) /\
      extcall_kw_memory_post (DF,lo,d,C,f) ce cx e (a,b,es,s0,G0,tn0,op) H v ee Gt tt t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  `~is_word_type (lowered_value_type ce e) /\ ~is_word_type (post_value_type ce e)` by
    (drule expr_body_pre_lowered_fits >>
     metis_tac[arg_type_fits_word_type,materialize_post_lowered_classify,is_bytestring_word_type]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then (strip_assume_tac o SIMP_RULE bool_ss [create_operand_vv_post_def,INL_11]))) >>
  `unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) = unwrap_value ce vv` by
    metis_tac[extcall_kw_default_same_unwrap] >>
  `compile_materialize_vv ce (lowered_value_type ce e)
      (ext_call_arg_value (lowered_value_type ce e) vv) m = (op,b)` by
    fs[compile_materialize_vv_def,comp_bind_def] >>
  `ci_mono a m /\ ci_mono m b` by
    metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_materialize_vv,SND] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at m x` by metis_tac[cj 1 compiler_compile_var] >>
  `local_ptrs_reserved ce m /\ return_buf_frame d ce m s` by
    (fs[ci_mono_def] >> conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
     irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`a`] >> fs[vv_post_def]) >>
  suspend "source"
QED

Resume extcall_kw_default_suffix[source]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H C f ce cx e (es with gas_obs := gs) a m s0 ee raw vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE bool_ss [create_operand_vv_post_def,INL_11]))) >>
     simp[vv_post_initial_gas]) >>
  `ghost_kept_at lo ce (es with gas_obs := gs) a G0 tn0 s0 G tn` by
    (simp[ghost_kept_at_def] >> fs[ghost_kept_at_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `a.cs_next_var <= m.cs_next_var /\ a.cs_next_id <= m.cs_next_id` by fs[ci_mono_def] >>
  `type_memory_bytes ce (lowered_value_type ce e) + 64 < dimword (:256)` by simp[] >>
  `MAP FDOM (es with gas_obs := gs).scopes = MAP FDOM ee.scopes /\ (!ty op. vv = StackValue ty op ==> ptr_buf_ok ce e op G s)` by simp[] >>
  qpat_assum `create_operand_at m s` (strip_assume_tac o REWRITE_RULE[create_operand_at_def]) >>
  drule_all (SIMP_RULE bool_ss [vyperStateTheory.evaluation_state_accessors]
    (Q.INST [`es` |-> `es with gas_obs := gs`] ctor_materialize_source_arrival)) >>
  disch_then (qspecl_then [`E`,`PG`]
    (qx_choosel_then [`buf`,`mid`,`c`,`src`,`p`,`dw`,`rt`,`sw`,`z`,`Gz`,`tz`,`inst`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "store"
QED

Resume extcall_kw_default_suffix[store]:
  qabbrev_tac `HP = \H. valid_horizon cx st0 H ee.storage_trace` >>
  qabbrev_tac `n = if is_bytestring_type (lowered_value_type ce e) then val_store_size rt v
                    else type_memory_size rt` >>
  `HP H0` by simp[Abbr `HP`] >>
  `!H. HP H ==> stmt_state_rel H C f ce cx ee z /\
                ghost_inv_at (DF H) lo d ce cx ee Gz tz z` by simp[Abbr `HP`] >>
  `(0 < n ==> w2n sw + n <= z.vs_alloca_next /\
              ?x. src = Var x /\ ptr_covers Gz tz x z n)` by
    (`n <= type_memory_size rt` by (simp[Abbr `n`] >> rw[] >> simp[val_store_size_le]) >>
     strip_tac >> `0 < type_memory_size rt` by decide_tac >>
     qpat_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- decide_tac >> qexists_tac `x` >> simp[] >>
     fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS,LESS_EQ_MONO_ADD_EQ]) >>
  `!name b len. local_region ce ee.scopes z name b len ==>
      w2n dw + type_memory_size rt <= b \/ b + len <= w2n dw` by
    (qpat_assum `!name b len. local_region ce ee.scopes z name b len ==> regions_disjoint _ _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `!name b len. local_region ce (es with gas_obs := gs).scopes s0 name b len ==>
      w2n dw + type_memory_size rt <= b \/ b + len <= w2n dw` by
    (qpat_assum `!name b len. local_region ce (es with gas_obs := gs).scopes s0 name b len ==> _`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  qunabbrev_tac `n` >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`n` |-> `if is_bytestring_type (lowered_value_type ce e) then val_store_size tv v
              else type_memory_size tv`, `es` |-> `es with gas_obs := gs`] ctor_materialize_store_arrival)) >>
  disch_then (qspecl_then [`E`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "scope"
QED

Resume extcall_kw_default_suffix[scope]:
  `ci_mono mid c /\ ci_mono c b` by
    metis_tac[ci_mono_unwrap_value,ci_mono_compile_store_memory,SND] >>
  `m.cs_next_id < mid.cs_next_id` by (drule compile_alloc_buffer_code >> simp[]) >>
  `m.cs_next_id < b.cs_next_id /\ m.cs_next_id <= c.cs_next_id /\ c.cs_next_id <= b.cs_next_id /\
    c.cs_next_var <= b.cs_next_var /\ a.cs_next_var <= b.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (rpt gen_tac >> disch_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gz`,`z`,`tz`] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]) >>
  `create_operand_at b u` by simp[create_operand_at_def] >>
  qexistsl_tac [`u`,`Gu`,`tu`] >> simp[] >>
  conj_tac >- suspend "scoped_run" >>
  suspend "post"
QED

Resume extcall_kw_default_suffix[scoped_run]:
  irule extcall_kw_segment_scope >> simp[] >> reverse conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
        (qspec_then `H0` (drule_then (ACCEPT_TAC o cj 1 o MATCH_MP gas_origin_ptr_path_projections)))) >>
  irule RTC_TRANS >> qexists_tac `z` >> conj_tac
  >- (irule RTC_MONOTONE >> qpat_assum `RTC (\u v. ?i. _ /\ m.cs_next_id <= _ /\ _) s z`
        (irule_at Any) >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  irule RTC_MONOTONE >> qpat_assum `RTC (\u v. ?i. _ /\ c.cs_next_id <= _ /\ _) z u`
    (irule_at Any) >> metis_tac[LESS_EQ_TRANS]
QED

Resume extcall_kw_default_suffix[post]:
  rpt gen_tac >> disch_tac >>
  `alloca_inv z` by
    (qpat_assum `!H. HP H ==> stmt_state_rel H C f ce cx ee z /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history f u` by
    (irule body_full_path_alloca_history >> simp[] >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] (OK u,Gu,tu)`
       (qspec_then `DF H` (irule_at Any)) >> simp[]) >>
  `u.vs_labels = s0.vs_labels` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `H0` (drule_then (mp_tac o MATCH_MP gas_origin_ptr_path_preserves_labels))) >> simp[]) >>
  `wb_frame ce es ee a s0 u` by
    (qpat_assum `wb_frame ce (es with gas_obs := gs) ee a s0 u` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[wb_frame_def,locals_kept_def,popped_kept_def] >> metis_tac[]) >>
  `ghost_kept_at lo ce es a G0 tn0 s0 Gu tu` by
    (qpat_assum `ghost_kept_at lo ce (es with gas_obs := gs) a G0 tn0 s0 Gu tu` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_kept_at_def] >> metis_tac[]) >>
  `return_buf_frame d ce b u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`a`] >> fs[wb_frame_def]) >>
  `not_fresh_at b p` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!H. HP H ==> stmt_state_rel H C f ce cx ee u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `storage_well_formed_on cx ee (FST H)` by
    (qpat_assum `!h. valid_horizon _ _ h _ ==> create_operand_vv_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> fs[Abbr `HP`]) >>
  `(ctx_has_dalloca C ==> allocas_below_fmp u)` by metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  simp[extcall_kw_memory_post_def,eval_operand_def] >>
  `ptr_mem_ok cx (lowered_value_type ce e) v (Var p) Gu tu u` by fs[ptr_val_ok_def] >>
  simp[] >> conj_tac >- fs[wb_frame_def] >> conj_tac >- fs[wb_frame_def] >>
  `FLOOKUP z.vs_allocas m.cs_next_id = SOME (w2n dw,type_memory_size rt)` by metis_tac[] >>
  qexists_tac `m.cs_next_id` >> simp[loweringStateRelDefsTheory.regions_disjoint_def,ADD_COMM] >>
  rpt strip_tac >> qpat_assum `!name b len. local_region ce ee.scopes u name b len ==> _`
    (drule_then mp_tac) >> simp[ADD_COMM]
QED

Finalise extcall_kw_default_suffix

Theorem extcall_kw_default_read[local]:
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv m = (op,b) /\
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) /\
  local_ptrs_reserved ce a /\ fn_has_code m b f /\ fn_inst_ids_distinct f /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==> b.cs_next_id <= i.inst_id) /\
  return_buf_frame d ce a s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  eval_expr cx e (es with gas_obs := gs) = (res,ee) /\ ee.gas_obs = [] /\
  storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at m s /\
  ~s.vs_halted /\ s.vs_labels = s0.vs_labels /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
      H res ee G tn s) ==>
  ?raw. res = INL raw /\
    scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 m b
      (read_result cx raw) (ee,s,G,tn)
      (\H res ee G tn t. ?v. res = INL v /\
        extcall_kw_memory_post (DF,lo,d,C,f) ce cx e (a,b,es,s0,G0,tn0,op) H v ee G tn t)
      (create_operand_exit_post C cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace`
      (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def]))) >>
  rename1 `res = INL raw` >> gvs[] >>
  Cases_on `read_result cx raw ee` >>
  rename1 `read_result cx raw ee = (read_res,read_state)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  Cases_on `read_res` >- (rename1 `read_result cx raw ee = (INL v,ee)` >> suspend "success") >>
  metis_tac[vv_post_failed_read]
QED

Resume extcall_kw_default_read[success]:
  `!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==> FLOOKUP s.vs_allocas aid = SOME row` by
    fs[vv_post_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
      H (INL raw : eval_result + vyperState$exception) ee G tn s /\ storage_well_formed_on cx ee (FST H)` by
    (rpt gen_tac >> disch_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qhdtm_assum `create_operand_vv_post`
       (mp_tac o REWRITE_RULE [create_operand_vv_post_def]) >> simp[INL_11,vv_post_def]) >>
  drule_all extcall_kw_default_suffix >>
  disch_then (qspecl_then [`PG`,`E`] (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`,`ee`,`OK u`,`Gu`,`tu`] >>
  simp[gas_explicit_def] >> metis_tac[read_result_gas_obs]
QED

Finalise extcall_kw_default_read

(* Refine the normal post at its own edge, not at another arrival at m. *)
Theorem extcall_kw_default_child[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s0,G0,tn0)
    (\H (res : eval_result + vyperState$exception) ee G tn t.
       create_operand_vv_post (DF,lo,d,C,f) ce cx e
       (es,a,m,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at m t)
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. ?raw. res = INL raw /\
      create_operand_vv_post (DF,lo,d,C,f) ce cx e
        (es,a,m,s0,vv,G0,tn0) H (INL raw : eval_result + vyperState$exception) ee G tn t /\
      create_operand_at m t /\ ee.gas_obs = [] /\ ~t.vs_halted /\ t.vs_labels = s0.vs_labels)
    (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post C cx H (INR exc : value + vyperState$exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >>
  qexists_tac `marks` >> simp[]
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> res_tac >> fs[]
      >- (`~t.vs_halted /\ t.vs_labels = s0.vs_labels` by
            metis_tac[gas_origin_ptr_path_erase,gas_path_normal,gas_origin_ptr_path_preserves_labels] >>
          `?raw. res = INL raw` by
            (qhdtm_assum `create_operand_vv_post`
               (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def]) >> metis_tac[]) >>
          gvs[exit_result_def] >>
          qpat_assum `!h. valid_horizon _ _ h _ ==> _` (qspec_then `H` mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
      Cases_on `res` >>
      fs[create_operand_exit_post_def,expr_exit_def,halt_exit_def,
         stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem extcall_kw_default_bind[local]:
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv m = (op,b) /\
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) /\
  local_ptrs_reserved ce a /\ fn_has_code m b f /\ fn_inst_ids_distinct f /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==> b.cs_next_id <= i.inst_id) /\
  return_buf_frame d ce a s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a m (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,C,f) ce cx e
      (es,a,m,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at m t)
    (create_operand_exit_post C cx) /\
  (!marks. create_operand_focus_scope a m E C f s0 marks ==>
           create_operand_focus_scope a b E C f s0 marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s0 marks r ==>
             create_operand_full_scope a b E C f s0 marks r) /\
  (!left t right. create_operand_full_scope a m E C f s0 left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s0 (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s0 left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s0 (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) (cx_tops cx) cx st0 a b
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      extcall_kw_memory_post (DF,lo,d,C,f) ce cx e (a,b,es,s0,G0,tn0,op) H v ee G tn t)
    (create_operand_exit_post C cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac extcall_kw_default_child >>
  irule scoped_operand_bind >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_result >> simp[GSYM ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`\H (raw : eval_result) ee G tn t.
    create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,m,s0,vv,G0,tn0)
      H (INL raw : eval_result + vyperState$exception) ee G tn t /\
    create_operand_at m t /\ ee.gas_obs = [] /\ ~t.vs_halted /\ t.vs_labels = s0.vs_labels`, `m`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  qx_genl_tac [`marks`,`raw`,`mid`,`G`,`tn`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `create_operand_at m s /\ ~s.vs_halted /\ s.vs_labels = s0.vs_labels` by metis_tac[] >>
  mp_tac (Q.INST [`ee` |-> `mid with gas_obs := []`,
                  `res` |-> `INL raw : eval_result + vyperState$exception`,
                  `gs` |-> `gas_explicit marks s0.vs_gas_readings`]
                 (SPEC_ALL extcall_kw_default_read)) >>
  simp[] >> metis_tac[APPEND_NIL]
QED

(* Track only emitted instructions: the incoming state may already contain
   calls/creates from earlier operands. *)
val kw_code_rules =
  [LET_DEF, code_action_return, code_action_fresh_label, code_action_fresh_var,
   code_action_new_block, code_action_emit_inst, code_action_emit_op,
   code_action_emit_void, code_action_alloc_buffer];

fun kw_code_steps ths =
  rpt (FIRST [CHANGED_TAC (simp (ths @ kw_code_rules)),
              match_mp_tac code_action_bind, match_mp_tac code_action_ignore_bind,
              conj_tac, gen_tac, CHANGED_TAC BETA_TAC, IF_CASES_TAC]);

Theorem extcall_kw_copy_actions[local]:
  let P = \opc. ~MEM opc [INVOKE;CREATE;CREATE2] in
    (!ctor imm src dst n off. code_action P (compile_imm_copy_to_memory ctor imm src dst n off)) /\
    (!src dst count ll sl ctor imm. code_action P (compile_word_copy_loop_base src dst count ll sl ctor imm))
Proof
  simp[] >> conj_tac
  >- (rpt gen_tac >> map_every qid_spec_tac [`off`,`dst`,`src`,`imm`,`ctor`] >>
      Induct_on `n` >> rpt gen_tac >> Cases_on `src` >> Cases_on `dst` >> Cases_on `imm` >>
      kw_code_steps [Once compile_imm_copy_to_memory_def,compile_lit_byte_offset_def,compile_imm_load_word_def]) >>
  `!ctor imm loc op. code_action (\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2)
      (compile_ptr_load ctor imm loc op)` by
    (rpt gen_tac >> Cases_on `loc` >> Cases_on `imm` >>
     kw_code_steps [compile_ptr_load_def,compile_imm_load_word_def]) >>
  `!ctor imm loc op v. code_action (\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2)
      (compile_ptr_store ctor imm loc op v)` by
    (rpt gen_tac >> Cases_on `loc` >> Cases_on `imm` >>
     kw_code_steps [compile_ptr_store_def,compile_imm_store_word_def]) >>
  kw_code_steps [compile_word_copy_loop_base_def]
QED

Theorem extcall_kw_unwrap_action[local]:
  code_action (\opc. ~MEM opc [INVOKE;CREATE;CREATE2]) (unwrap_value ce vv)
Proof
  `!op loc nb n ctor imm. code_action (\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2)
        (compile_ensure_in_memory op loc nb n ctor imm)` by
   (rpt gen_tac >> Cases_on `loc` >>
    kw_code_steps [compile_ensure_in_memory_def,compile_storage_to_memory_def,compile_transient_to_memory_def,
      compile_word_copy_loop_def,compile_word_copy_loop_op_def,
      SIMP_RULE (srw_ss()) [LET_DEF] extcall_kw_copy_actions]) >>
  Cases_on `vv` >> simp[unwrap_value_def,code_action_return] >>
  Cases_on `p.ptr_location` >> Cases_on `ce.ce_imm_alloca` >>
  kw_code_steps [compile_ptr_load_def,compile_imm_load_word_def]
QED

Theorem extcall_kw_materialize_action[local]:
  code_action (\opc. ~MEM opc [INVOKE;CREATE;CREATE2]) (compile_materialize_vv ce dt vv)
Proof
  `!src dst. code_action (\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2)
      (compile_store_memory ce src dst dt dt)` by
    (rpt gen_tac >> Cases_on `type_memory_bytes ce dt` >>
     kw_code_steps [compile_store_memory_def,compile_store_bytestring_def,
       compile_bytestring_copy_len_def,compile_copy_memory_def]) >>
  kw_code_steps [compile_materialize_vv_def, SIMP_RULE (srw_ss()) [] extcall_kw_unwrap_action]
QED

Theorem extcall_kw_materialize_opcodes[local]:
  compile_materialize_vv ce dt vv m = (op,b) ==>
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code m b)
Proof
  strip_tac >> mp_tac extcall_kw_materialize_action >>
  simp[code_action_def,code_step_def] >> metis_tac[]
QED

Theorem extcall_kw_default_cut[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  compile_materialize_vv ce dt vv m = (op,b) /\
  create_operand_cut a m E C f tops cx st0 (eval_expr cx e) (es,s0) ==>
  create_operand_cut a b E C f tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[create_operand_cut_def] >> rpt gen_tac >> disch_tac >>
  drule_all_then strip_assume_tac create_interior_visit_first_exit
  >- (irule create_cut_bind_left >> simp[storage_trace_frame_read_result] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  drule extcall_kw_materialize_opcodes >> strip_tac >>
  rename1 `create_interior_visit m b E C f _ t _` >>
  `create_cut_region m b t` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  qpat_assum `create_interior_visit m b _ _ _ _ t _`
    (strip_assume_tac o MATCH_MP create_interior_visit_cases) >>
  `create_cut_region m b u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def,create_operand_at_def,EVERY_MEM] >>
  `MEM inst (frag_code m b)` by metis_tac[] >>
  gvs[create_body_cut_def,venomRunBoundedTheory.inst_create_size_ok_def]
QED

Theorem extcall_kw_memory_default_scoped_cut:
  body_inv tops C ce cx /\ expr_body_pre ce cx env e es /\
  expr_type e = rt /\ ~is_word_type rt /\
  compile_ext_call_kwarg compile_expr ce rt EKDefault e a = ((op,dt),b) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T ce) rt EKDefault
    (gas_shadow_expr e) ha = ((op,dt),hb) /\
  gas_shadow_state a ha /\ gas_shadow_context C hC /\ ctx_inst_ids_distinct C /\
  gas_shadow_function f hf /\ MEM f C.ctx_functions /\ MEM hf hC.ctx_functions /\
  fn_has_code a b f /\ fn_has_code ha hb hf /\ fn_inst_ids_distinct f /\
  create_layout a b /\ local_ptrs_reserved ce a /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
           get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==> b.cs_next_id <= i.inst_id) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s0 /\ alloca_history f s0 /\
  (ctx_has_dalloca C ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable C f s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H C f ce cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ create_operand_at a s0 /\
  (!m hm vv. expr_vv_sim_full_pre (DF,lo,d,C,hC,PG,f,hf) ce cx (expr_type e) e es
       (st0,a,m,ha,hm,vv,s0,G0,tn0) /\ create_layout a m ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites C hC,C,f,PG) (cx_tops cx) cx st0 a m
       (eval_expr cx e) (es,s0,G0,tn0)
       (\H res ee G tn t. create_operand_vv_post (DF,lo,d,C,f) ce cx e
          (es,a,m,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at m t)
       (create_operand_exit_post C cx) /\
     create_operand_cut a m (gas_explicit_sites C hC) C f tops cx st0 (eval_expr cx e) (es,s0)) ==>
  dt = lowered_value_type ce e /\
  scoped_operand_outcome (DF,lo,gas_explicit_sites C hC,C,f,PG) (cx_tops cx) cx st0 a b
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      extcall_kw_memory_post (DF,lo,d,C,f) ce cx e (a,b,es,s0,G0,tn0,op) H v ee G tn t)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b (gas_explicit_sites C hC) C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`vv`,`m`,`hm`] strip_assume_tac) extcall_kw_memory_default_compile >>
  gvs[] >>
  `expr_vv_sim_full_pre (DF,lo,d,C,hC,PG,f,hf) ce cx (expr_type e) e es
       (st0,a,m,ha,hm,vv,s0,G0,tn0)` by
    (drule_then assume_tac expr_body_pre_vv_gas_admissible >>
     simp[expr_vv_sim_full_pre_def] >>
     fs[create_operand_at_def] >> first_assum ACCEPT_TAC) >>
  `create_cut_code {} a m` by metis_tac[operand_vv_cut_code] >>
  `create_cut_code {} m b` by metis_tac[extcall_kw_default_materialize_code] >>
  `cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[create_cut_code_def] >>
  `create_layout a m` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  qpat_assum `!m hm vv. _ ==> _ /\ _` (drule_then (strip_assume_tac o UNDISCH)) >>
  reverse conj_tac >- drule_all_then ACCEPT_TAC extcall_kw_default_cut >>
  qabbrev_tac `E = gas_explicit_sites C hC` >>
  `create_cut_region a m s0` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[create_layout_left_stop] >>
  `!bb i. lookup_block b.cs_current_bb f.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==> i.inst_id NOTIN frag_ids a m` by
    (simp[frag_ids_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  irule extcall_kw_default_bind >>
  qpat_assum `compile_expr ce _ e a = (vv,m)` (irule_at Any) >>
  qpat_assum `expr_body_pre ce cx env e es` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC create_left_terminal_lift_at)
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC create_operand_full_scope_prepend)
  >- (rpt strip_tac >>
      `create_operand_at m t /\ create_expr_prefix a m E C f s0 left t` by
        fs[create_operand_full_scope_def,create_operand_at_def] >>
      `create_cut_region m b t` by
        (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
      drule_all_then ACCEPT_TAC create_operand_focus_scope_join) >>
  rpt strip_tac >> drule_all_then ACCEPT_TAC create_left_focus_lift_at
QED

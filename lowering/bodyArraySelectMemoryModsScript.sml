(* Memory-place selection at the linked no-copy array cut. *)
Theory bodyArraySelectMemoryMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayNoCopySourceMods bodySubscriptArrayRouteDefsMods
  bodyFullPostsMods loweringPosts exprLoweringProps compileEnv vyperAST
  exprBodyPreProps vyperTypeSystem
  bodyArrayMemoryIndexCutMods bodyArrayMemorySourcePathsMods
  bodyArrayMemoryReachedRowMods bodyArrayMemoryCoveredReadMods
  bodyArrayMemoryParentViewMods bodyArrayMemoryDynamicChildMods
  bodyArrayMemoryFixedSuffixMods bodyArrayMemoryDynamicSuffixMods
  exprSimTopLevelProps vyperTypeStatePreservation vyperTypeValues
  valueEncodingTyping valueEncodingDefs bodyPtrDefs bodyFullShadowBodyInv
  vyperTypeEvalProofs vyperPlaceResultTyping vyperValueOperation
  vyperState vyperValue vyperTyping words freshWrites vyperStorageFootprint
  context exprLowering finite_map loweringStateRelDefs valueEncoding
  venomState ptrDiscipline

Theorem array_memory_base_post[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) bvv s /\
  post_value_type cenv obj = ArrayT et bd ==>
  ?p. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocMemory /\
      vv_post H ctx func cenv cx obj es sa sm s0 mid
        (PlaceR (MemoryPlace id path)) bvv s /\
      immutable_frame_mods func cenv cx mid s
Proof
  Cases_on `bvv` >> simp[vv_post_mods_def, vv_at_def, is_word_type_def] >>
  strip_tac >> rename1 `p.ptr_location = LocMemory` >>
  Cases_on `p.ptr_location = LocMemory` >> fs[] >>
  fs[vv_holds_mods_def, vv_holds_def, is_bytestring_type_def] >>
  gvs[vv_post_def, vv_at_def, vv_holds_def, vv_place_ptr_mods_def,
      is_word_type_def, is_bytestring_type_def] >> metis_tac[]
QED

Theorem array_select_memory_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (MemoryPlace id path) /\ ~(?n. bd = Fixed n /\ base_from_pop obj) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0
    (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  `post_value_type cenv obj = ArrayT et bd` by simp[] >>
  qpat_assum `raw = PlaceR _` (fn raw_eq =>
    qpat_assum `vv_post_mods H0 _ _ _ _ obj _ _ _ _ _ raw _ _`
      (assume_tac o REWRITE_RULE [raw_eq])) >>
  drule_all_then strip_assume_tac array_memory_base_post >>
  `~array_slot_base cenv obj` by
    (strip_tac >> drule array_slot_base_compile_location >>
     disch_then (qspecl_then [`ty`,`sa`] mp_tac) >> simp[contextTheory.vv_location_def]) >>
  `expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1)` by simp[] >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  drule_all_then strip_assume_tac array_memory_index_cut_mods >>
  qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac array_memory_source_paths_mods >>
  qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es s0 /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. _ ==> expr_post H _ _ _ _ idx _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `s0.vs_alloca_next <= it.vs_alloca_next /\ sa.cs_next_var <= st2.cs_next_var` by decide_tac >>
  qpat_assum `vv_post_mods H0 _ _ _ _ obj _ _ _ _ _ _ _ _`
    (mp_then (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac array_memory_reached_row_mods) >>
  disch_then (fn row =>
    qpat_assum `expr_post H0 _ _ _ _ idx _ _ _ _ _ _ _ _`
      (mp_then (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac row)) >>
  disch_then (fn row =>
    qpat_assum `evaluate_type _ (ArrayT et bd) = SOME _`
      (mp_then (Pat `evaluate_type _ (ArrayT _ _) = _`) mp_tac row)) >>
  disch_then (qspecl_then [`rt`,`initial`,`entry`,`em`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>

  suspend "covered_read"
QED

(* Read the parent through the same covered row used for its children. *)
Resume array_select_memory_mods[covered_read]:
  `popped_kept cenv es fin s0 it` by
    (qpat_assum `wb_frame cenv es fin sa s0 it`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def, locals_kept_def]) >>
     first_assum ACCEPT_TAC) >>
  `well_formed_type_value initial.type` by
    (irule evaluate_type_well_formed_type_value >> goal_assum (drule_at Any)) >>
  `value_has_type initial.type initial.value` by
    (irule lookup_scopes_state_well_typed_value_has_type >>
     goal_assum (drule_at (Pat `lookup_scopes _ es.scopes = _`)) >> simp[]) >>
  `value_has_type entry.type entry.value` by
    (irule lookup_scopes_state_well_typed_value_has_type >>
     goal_assum (drule_at (Pat `lookup_scopes _ fin.scopes = _`)) >> simp[]) >>
  `!r k t. (?v0. evaluate_subscripts initial.type initial.value r = INL v0) /\
    live_memory_result fin (PlaceR (MemoryPlace id r)) /\
    mem_path_offset entry.type r = SOME (k,t) ==>
    ?v. read_result cx (PlaceR (MemoryPlace id r)) fin = (INL v,fin) /\
        value_has_type t v /\ well_formed_type_value t /\
        k + type_memory_size t <= sz /\
        !m. mem_agree_outside tni.t_mem it.vs_memory m ==>
            val_in_memory t v (w2n B + k) m` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule array_memory_covered_read_mods >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods (DF H0) lo _ _ _ es _ _ _` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods (DF H0) lo _ _ _ fin _ _ _` (irule_at Any) >>
     qpat_assum `entry_pop_trace initial events entry` (irule_at Any) >>
     qpat_assum `FLOOKUP cenv.ce_vars id = _` (irule_at Any) >> simp[]) >>
  qpat_assum `!r k t. _ ==> ?v. read_result _ _ _ = _ /\ _`
    (qspecl_then [`path`,`j`,`ArrayTV etv bd`] mp_tac) >>
  impl_tac >- (simp[] >> goal_assum (drule_at Any)) >>
  disch_then strip_assume_tac >>
  qpat_assum `w2n a = w2n B + j` (fn addr =>
    qpat_assum `!m. _ ==> val_in_memory _ v (w2n B + j) m`
      (assume_tac o ONCE_REWRITE_RULE [GSYM addr])) >>
  `val_wf (ArrayTV etv bd) v` by (irule (cj 1 value_has_type_val_wf) >> simp[]) >>

  suspend "parent_view"
QED

(* Rebuild the final pointer certificate from its original provenance. *)
Resume array_select_memory_mods[parent_view]:
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `evaluate_type (get_tenv cx) rt = SOME entry.type` by simp[] >>
  qpat_assum `ptr_vv_ok _ _ _ _ mid _ _ _`
    (mp_then (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`) mp_tac
       (INST_TYPE [alpha |-> ``:256``] array_memory_parent_view_mods)) >>
  disch_then (fn parent =>
    qpat_assum `mem_path_offset entry.type path = _`
      (mp_then (Pat `mem_path_offset _ _ = _`) mp_tac parent)) >>
  disch_then (fn parent =>
    qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni`
      (mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) mp_tac parent)) >>
  disch_then (fn parent =>
    qpat_assum `read_result cx (PlaceR (MemoryPlace id path)) fin = _`
      (mp_then (Pat `read_result _ _ _ = _`) mp_tac parent)) >>
  disch_then (fn parent =>
    qpat_assum `local_region cenv fin.scopes it id (w2n B) sz`
      (mp_then (Pat `local_region _ _ _ _ _ _`) mp_tac parent)) >>
  disch_then (fn parent =>
    qpat_assum `evaluate_type _ (ArrayT et bd) = _`
      (mp_then (Pat `evaluate_type _ (ArrayT _ _) = _`) mp_tac parent)) >>
  disch_then (qspecl_then [`st2`,`sa`,`rt`,`a`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `allocas_from lo it` by
    (qpat_assum `ghost_inv_at_mods (DF H0) lo _ _ _ fin _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by simp[] >>
  `loc = LocMemory` by simp[vv_location_def] >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory =
     (\op. emit_op MLOAD [op])` by simp[FUN_EQ_THM, compile_ptr_load_def] >>
  qpat_assum `type_memory_bytes cenv et = _` (fn size =>
    qpat_assum `compile_ptr_load _ _ LocMemory = _` (fn load =>
      qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
        (assume_tac o SIMP_RULE (srw_ss())
           [vv_operand_def, elem_size_in_location_def, is_slot_addressed_def,
            word_scale_def, size, load]))) >>
  Cases_on `bd`
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume array_select_memory_mods[fixed]:
  rename1 `array_select_outcome_mods _ _ _ _ _ _ _ (Fixed n) _ _ _ _ _` >>
  qpat_x_assum `!k. Fixed n = Fixed k ==> _ /\ vv_at _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `n` (strip_assume_tac o SRULE [])) >>
  qpat_x_assum `v = ArrayV (SArrayV _)` SUBST_ALL_TAC >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o SRULE []) >>
  irule array_memory_fixed_suffix_mods >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `read_result cx (PlaceR (MemoryPlace id path)) fin = _` (irule_at Any) >>
  qpat_assum `vv_at _ _ _ sa st2 fin _ _ it` (irule_at Any) >>
  qpat_assum `eval_operand p.ptr_operand it = SOME a` (irule_at Any) >>
  qpat_assum `eval_operand iop it = SOME iw` (irule_at Any) >>
  simp[type_memory_size_def, IgnAsm `i = if _ then _ else _`] >>
  qexists `j` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `entry.type = initial.type` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  fs[type_memory_size_def]
QED

Resume array_select_memory_mods[dynamic]:
  rename1 `array_select_outcome_mods _ _ _ _ _ _ _ (Dynamic cap) _ _ _ _ _` >>
  qpat_x_assum `!k. Dynamic cap = Dynamic k ==> subscripts_type _ _ = _ /\ _`
    (qspec_then `cap` (strip_assume_tac o SRULE [])) >>
  qpat_x_assum `v = ArrayV (DynArrayV _)` SUBST_ALL_TAC >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (assume_tac o SRULE []) >>
  `0 <= i /\ Num i < LENGTH vs ==>
   ?val root ssz base rt' k.
     read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
       (INL val,fin) /\ value_has_type etv val /\
     (!m. mem_agree_outside tni.t_mem it.vs_memory m ==>
          val_in_memory etv val (w2n a + 32 + Num i * type_memory_size etv) m) /\
     FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) ssz) /\
     lookup_var root it = SOME base /\
     cenv.ce_var_type id = SOME rt' /\ evaluate_type (get_tenv cx) rt' = SOME entry.type /\
     mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,etv) /\
     w2n a + 32 + Num i * type_memory_size etv = w2n base + k /\
     k + type_memory_size etv <= ssz` by
    (strip_tac >> irule array_memory_dynamic_child_mods >>
     qpat_assum `read_result cx (PlaceR (MemoryPlace id path)) fin = _` (irule_at Any) >>
     qpat_assum `mem_path_offset entry.type path = _` (irule_at Any) >>
     qpat_assum `FLOOKUP cenv.ce_vars id = _` (irule_at Any) >>
     qpat_assum `lookup_var q it = SOME B` (irule_at Any) >>
     qpat_assum `ce_var_type cenv id = _` (irule_at Any) >>
     qexists `initial` >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!r k t. _ ==> ?v. read_result _ _ _ = _ /\ _`
          (qspecl_then [`r`,`k`,`t`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (qx_choose_then `child` strip_assume_tac) >>
        qexists `child` >> asm_rewrite_tac[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `!cap vs i. _ ==> _ /\ live_memory_result _ _`
          (qspecl_then [`cap`,`vs`,`i`] mp_tac) >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  irule array_memory_dynamic_suffix_mods >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `op_prov Gi p.ptr_operand = SOME (_,_)` (irule_at Any) >>
  qpat_assum `read_memory_path entry path = _` (irule_at Any) >>
  qpat_assum `eval_operand p.ptr_operand it = SOME a` (irule_at Any) >>
  qpat_assum `eval_operand iop it = SOME iw` (irule_at Any) >>
  qpat_assum `evaluate_type _ et = SOME etv` (irule_at Any) >>
  simp[IgnAsm `i = if _ then _ else _`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[type_memory_size_def]
QED

Finalise array_select_memory_mods

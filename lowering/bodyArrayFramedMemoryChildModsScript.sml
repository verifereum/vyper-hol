(* The successful element of a captured fixed memory window. *)
Theory bodyArrayFramedMemoryChildMods
Ancestors
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods bodyFullPostsMods
  vyperInterpreter vyperTypeSystem vyperTypeValues vyperValueOperation vyperValue
  compileEnv context loweringStateRelDefs venomState exprLowering bodyFullShadowBodyInv
  exprSimWordArgs exprBopSimProps fragGasOriginPtr ptrDiscipline vyperAST arithmetic pair
  bodyForRangeScalarFrameMods gasOutcomeFullPostMods bodyFullPathHistory
  bodyFullUnwrapRun bodyFullHashKeccakFixed exprSimSubscriptArrayFrame exprSimSubscriptArraySuffix
  exprSimSubscriptArraySource exprSimSubscriptArrayEndpoint exprSimSubscriptArrayFramed exprSimHash
  exprBodyPreCallSafetyProps exprBodyPreTypingProps exprBodyPreProps
  vyperTypeExprSoundness vyperTypeEvalCaseProofs exprSimSource exprSimHypsDefs
  bodyAssignNameLinkedSetup exprSimIfExpCompat assignBasePtrBoundary
  exprSimVVFrame exprSimBopRestWordLoads bodyPtrBopHashFootprint
  exprSimProps exprSimCopy valueTypingMemoryProps vyperTypeEvalSoundness
  valueEncoding valueEncodingDefs vyperStorageFootprint gasShadow gasSummary
  vyperTypeInvariants vyperPlaceTyping vyperAssignPreservesType
  vyperArray vyperState loweringPosts exprSimMemDefs bodyPtrDefs
  exprLoweringProps loweringShapeDefs stateRelProj words integer finite_map

Theorem memory_place_ptr_mods[local]:
  p.ptr_location = LocMemory ==>
  (vv_place_ptr_mods cenv cx ee s raw (LocatedValue a p) <=>
   vv_place_ptr cenv cx ee s raw (LocatedValue a p))
Proof
  strip_tac >> Cases_on `raw` >> simp[vv_place_ptr_mods_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def]
QED

Theorem memory_post_mods[local]:
  p.ptr_location = LocMemory ==>
  (vv_post_mods H ctx func cenv cx e es sa sb s0 ee raw (LocatedValue a p) s <=>
   vv_post H ctx func cenv cx e es sa sb s0 ee raw (LocatedValue a p) s /\
   immutable_frame_mods func cenv cx ee s)
Proof
  strip_tac >> simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
                    memory_place_ptr_mods] >> metis_tac[]
QED

Theorem fixed_memory_source_inputs[local]:
  expr_body_pre_mods mods cenv cx env obj es /\ eval_expr cx obj es = (INL raw,mid) ==>
  env.type_defs = get_tenv cx /\ eval_result_typed (env,cx,mid) raw (Type (expr_type obj)) /\
  popped_keys_indexed mid.scopes
Proof
  strip_tac >> drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `env_consistent env cx es /\ context_well_typed cx /\ state_well_typed es /\
   accounts_well_typed es.accounts` by fs[runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  simp[] >> conj_tac
  >- (qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
      disch_then (qspecl_then [`env`,`es`,`INL raw`,`mid`] mp_tac) >> simp[]) >>
  irule eval_expr_popped_keys_indexed >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  fs[expr_body_pre_mods_def, expr_sim_inv_mods_def]
QED

Theorem fixed_memory_select_source[local]:
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,mid) raw (Type (ArrayT et (Fixed n))) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  popped_keys_indexed mid.scopes /\ fin.scopes = mid.scopes /\
  vv_place_ptr cenv cx fin it raw (LocatedValue a p) /\ p.ptr_location = LocMemory /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v ==>
  ?child. select_result cx (ArrayT et (Fixed n)) raw (ValueSubscript (IntV i)) fin = (INL child,fin) /\
          read_result cx child fin = (INL v,fin) /\
          (!x. child = Value x ==> raw = Value (ArrayV av))
Proof
  strip_tac >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV av) [ValueSubscript (IntV i)] = INL v`
    by simp[evaluate_array_subscript_result] >>
  Cases_on `raw`
  >- (gvs[read_result_def, return_def] >> drule_all select_value_read >> simp[])
  >- (rename1 `read_result cx (PlaceR pl) _ = _` >>
      Cases_on `pl` >> gvs[vv_place_ptr_def]
      >- (rename1 `read_result cx (PlaceR (MemoryPlace id path)) fin = _` >>
          `runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n))` by
            fs[eval_result_typed_def, runtime_place_typed_memory] >>
          `popped_keys_indexed fin.scopes` by simp[] >>
          drule_all select_fixed_memory_read >> simp[])) >>
  gvs[read_result_def, raise_def]
QED

Theorem fixed_memory_place_step[local]:
  expr_sim_inv_mods mods cenv cx env mid /\ env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,mid) raw (Type (ArrayT et (Fixed n))) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  vv_place_ptr cenv cx fin sf raw (LocatedValue a p) /\ p.ptr_location = LocMemory /\
  select_result cx (ArrayT et (Fixed n)) raw (ValueSubscript (IntV i)) fin = (INL child,fin) /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) = SOME (k,etv) /\
  eval_operand p.ptr_operand sf = SOME w /\ eval_operand dst sf = SOME (w + n2w k) ==>
  vv_place_ptr cenv cx fin sf child (LocatedValue et (mk_ptr dst LocMemory))
Proof
  strip_tac >> Cases_on `raw`
  >- gvs[select_result_def, bind_def, return_def, lift_option_type_def,
          lift_sum_def, raise_def, AllCaseEqs(), vv_place_ptr_def]
  >- (rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[vv_place_ptr_def, slot_loc_def]
      >- (rename1 `(if tr then LocTransient else LocStorage) = LocMemory` >> Cases_on `tr` >> gvs[]) >>
      rename1 `select_result cx _ (PlaceR (MemoryPlace id path)) _ _ = _` >>
      `child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))` by
        gvs[select_result_def, extend_place_def, extend_memory_place_def, bind_def,
            return_def, lift_sum_def, raise_def, ignore_bind_def, AllCaseEqs()] >>
      fs[eval_result_typed_def, runtime_place_typed_memory] >>
      rename1 `cenv.ce_var_type id = SOME ty0` >>
      `evaluate_type (get_tenv cx) ty0 = SOME entry.type` by
        (fs[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def,
            optionTheory.IS_SOME_EXISTS] >>
         `?ty'. FLOOKUP env.var_types id = SOME ty'` by
           (qpat_assum `!id entry. lookup_scopes id mid.scopes = SOME entry ==> _`
              drule >> simp[]) >>
         `cenv.ce_var_type id = SOME ty'` by simp[] >>
         `evaluate_type (get_tenv cx) ty' = SOME entry.type` by
           (qpat_assum `!id ty entry. _ ==> evaluate_type _ ty = SOME entry.type`
              (qspecl_then [`id`,`ty'`,`entry`] mp_tac) >> simp[]) >> gvs[]) >>
      gvs[] >> drule mem_path_offset_sound >> simp[] >> strip_tac >> gvs[] >>
      drule_all mem_path_offset_snoc >> strip_tac >>
      simp[vv_place_ptr_def, mk_ptr_def, GSYM WORD_ADD_ASSOC, word_add_n2w, ADD_COMM]) >>
  gvs[eval_result_typed_def]
QED

Theorem fixed_memory_base_types[local]:
  expr_body_pre_mods mods cenv cx env obj es /\ expr_type obj = ArrayT et (Fixed n) /\
  post_value_type cenv obj = expr_type obj /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) ==>
  lowered_value_type cenv obj = expr_type obj /\
  type_memory_bytes cenv (lowered_value_type cenv obj) = type_memory_size (ArrayTV etv (Fixed n))
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >> simp[well_formed_type_def]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_mods_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
     cenv.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  `lowered_value_type cenv obj = expr_type obj` by
    (drule_all ifexp_lowered_type_classify >> simp[is_bytestring_type_def] >>
     disch_then (DISJ_CASES_THEN2 ACCEPT_TAC STRIP_ASSUME_TAC) >>
     gvs[expr_type_def, post_value_type_def, is_word_type_def, is_bytestring_type_def]) >>
  simp[] >> irule assign_name_memory_bytes_mods >> metis_tac[]
QED

Theorem fixed_memory_element_extent[local]:
  array_length (ArrayTV etv (Fixed n)) av = n /\ valid_index (ArrayTV etv (Fixed n)) av i ==>
  Num i * type_memory_size etv + type_memory_size etv <= type_memory_size (ArrayTV etv (Fixed n))
Proof
  simp[valid_index_def] >> strip_tac >>
  `Num i < n` by intLib.COOPER_TAC >>
  once_rewrite_tac[ADD_COMM] >>
  pure_rewrite_tac[type_memory_size_def, GSYM (cj 5 MULT_CLAUSES)] >>
  irule LESS_MONO_MULT >> decide_tac
QED

(* The machine suffix does not write either the captured bytes or the state
   used by the linked immutable and ghost relations. *)
val suffix_frame = ``
    sf.vs_immutables = it.vs_immutables /\
    sf.vs_memory = it.vs_memory /\ sf.vs_allocas = it.vs_allocas /\
    sf.vs_alloca_next = it.vs_alloca_next /\ sf.vs_data_section = it.vs_data_section /\
    sf.vs_fmp = it.vs_fmp /\ sf.vs_accounts = it.vs_accounts /\
    sf.vs_transient = it.vs_transient /\ sf.vs_call_ctx = it.vs_call_ctx /\
    sf.vs_requests = it.vs_requests /\
    tnf.t_mem = tni.t_mem /\ tnf.t_stor = tni.t_stor /\
    tnf.t_trans = tni.t_trans /\ tnf.t_imm = tni.t_imm /\
    (!q. not_fresh_at st2 q ==>
      lookup_var q sf = lookup_var q it /\ FLOOKUP (Gf:string |-> num # num) q = FLOOKUP Gi q /\
      op_taint tnf (Var q) = op_taint tni (Var q))``;

Theorem fixed_memory_framed_post[local]:
  vv_post_mods H ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx)
    es sa st2 s0 fin raw (LocatedValue (ArrayT et (Fixed n)) p) it /\
  p.ptr_location = LocMemory /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= st2.cs_next_var /\ st2.cs_next_id <= sb.cs_next_id /\
  eval_operand p.ptr_operand sf = eval_operand p.ptr_operand it /\ ^suffix_frame /\
  stmt_state_rel H ctx func cenv cx fin sf ==>
  vv_post_mods H ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx)
    es sa sb s0 fin raw (LocatedValue (ArrayT et (Fixed n)) p) sf
Proof
  strip_tac >> fs[memory_post_mods] >> conj_tac
  >- (irule memory_vv_post_readonly_tail >>
      simp[] >> qexistsl [`it`,`st2`] >>
      simp[contract_storage_def, contract_transient_def] >>
      rpt gen_tac >> sym_tac >> irule copy_buffer_local_region_frame >>
      qexists_tac `st2` >> simp[] >> rpt strip_tac >>
      qpat_assum `!q. not_fresh_at st2 q ==> _` drule >> simp[]) >>
  irule immutable_frame_mods_exterior_frame >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  qexists_tac `st2` >> simp[] >> rpt strip_tac >>
  qpat_assum `!q. not_fresh_at st2 q ==> _` drule >> simp[]
QED

Theorem fixed_memory_child_covers[local]:
  ptr_buf_ok cenv obj p.ptr_operand Gi it /\ op_taint tni p.ptr_operand = {} /\
  eval_operand p.ptr_operand it = SOME w /\
  type_memory_bytes cenv (lowered_value_type cenv obj) = type_memory_size (ArrayTV etv (Fixed n)) /\
  k + type_memory_size etv <= type_memory_size (ArrayTV etv (Fixed n)) /\
  lookup_var out sf = SOME dw /\ w2n dw = w2n w + k /\
  op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov Gi p.ptr_operand /\
  0 < type_memory_size etv ==>
  ptr_covers Gf tnf out sf (type_memory_size etv)
Proof
  strip_tac >>
  `0 < type_memory_size (ArrayTV etv (Fixed n))` by decide_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _`
    (qspec_then `w` mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
  simp[] >> strip_tac >>
  fs[ptr_covers_def, op_prov_def, eval_operand_def] >>
  goal_assum (drule_at (Pat `FLOOKUP Gf out = _`)) >> simp[] >> decide_tac
QED

Theorem fixed_memory_child_ptr[local]:
  ptr_mem_ok cx (ArrayT et (Fixed n)) (ArrayV av) p.ptr_operand Gi tni it /\
  eval_operand p.ptr_operand it = SOME w /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ value_has_type (ArrayTV etv (Fixed n)) (ArrayV av) /\
  0 <= i /\ array_index (ArrayTV etv (Fixed n)) av i = SOME v /\ val_wf etv v /\
  read_result cx child fin = (INL v,fin) /\ lookup_var out sf = SOME dw /\
  w2n dw = w2n w + Num i * type_memory_size etv /\
  sf.vs_memory = it.vs_memory /\ tnf.t_mem = tni.t_mem /\ op_taint tnf (Var out) = {} /\
  (0 < type_memory_size etv ==> ptr_covers Gf tnf out sf (type_memory_size etv)) /\
  type_memory_bytes cenv et = type_memory_size etv ==>
  ptr_vv_ok cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) fin Gf tnf sf /\
  ptr_buf_ok cenv (Subscript et obj idx) (Var out) Gf sf
Proof
  strip_tac >> conj_tac
  >- (simp[ptr_vv_ok_def, mk_ptr_def, ptr_mem_ok_def, eval_operand_def] >> conj_tac
      >- (rpt strip_tac >>
          `val_in_memory (ArrayTV etv (Fixed n)) (ArrayV av) (w2n w) mem` by
            (irule ptr_mem_ok_robust >> goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >> simp[]) >>
          `&(Num i) = i` by intLib.COOPER_TAC >>
          `array_index (ArrayTV etv (Fixed n)) av (&(Num i)) = SOME v` by
            (pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
          drule_all rest_word_array_memory_index >> simp[]) >>
      strip_tac >>
      `val_footprint etv v <= val_store_size etv v /\ val_store_size etv v <= type_memory_size etv` by
        simp[val_footprint_le_store_size, val_store_size_le] >>
      `0 < type_memory_size etv` by decide_tac >>
      `ptr_covers Gf tnf out sf (type_memory_size etv)` by simp[] >>
      qpat_x_assum `ptr_covers Gf _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
      goal_assum (drule_at (Pat `FLOOKUP Gf out = _`)) >> gvs[] >> decide_tac) >>
  simp[ptr_buf_ok_def, lowered_value_type_def, expr_type_def, eval_operand_def] >> strip_tac >>
  `ptr_covers Gf tnf out sf (type_memory_size etv)` by simp[] >>
  qpat_x_assum `ptr_covers Gf _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  goal_assum (drule_at (Pat `FLOOKUP Gf out = _`)) >> gvs[]
QED

Theorem fixed_memory_parent_owns[local]:
  vv_own cenv cx (ArrayT et (Fixed n)) sa sm mid (Value (ArrayV av))
    (LocatedValue (ArrayT et (Fixed n)) p) s /\ p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand sf = SOME w /\
  wb_frame cenv mid fin sm s it /\ local_ptrs_reserved cenv sm /\ local_ptrs_rel func cenv mid.scopes s /\
  sm.cs_next_id <= sb.cs_next_id /\ fin.scopes = mid.scopes /\ sf.vs_allocas = it.vs_allocas /\
  (!name b sz. local_region cenv fin.scopes sf name b sz <=> local_region cenv fin.scopes it name b sz) ==>
  vv_own cenv cx (ArrayT et (Fixed n)) sa sb fin (Value (ArrayV av))
    (LocatedValue (ArrayT et (Fixed n)) (mk_ptr p.ptr_operand LocMemory)) sf
Proof
  simp[vv_own_def, mk_ptr_def, read_result_def, return_def] >> strip_tac >>
  qpat_x_assum `p.ptr_location = LocMemory ==> _` mp_tac >> simp[] >> strip_tac
  >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (b,sz)` >>
      `FLOOKUP it.vs_allocas aid = SOME (b,sz)` by
        (qpat_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >> simp[]) >>
      disj1_tac >> qexistsl [`aid`,`b`,`sz`] >> simp[] >>
      `aid < sb.cs_next_id` by decide_tac >> simp[] >>
      rpt strip_tac >>
      drule_all local_region_wb_frame >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem fixed_memory_child_capacity[local]:
  vv_store_bound cx (ArrayT et (Fixed n)) (ArrayT et (Fixed n)) mid raw
    (LocatedValue (ArrayT et (Fixed n)) p) s /\ p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ eval_operand p.ptr_operand s = SOME w /\
  eval_operand dst sf = SOME dw /\ w2n dw = w2n w + k /\
  k + type_memory_size etv <= type_memory_size (ArrayTV etv (Fixed n)) /\
  s.vs_alloca_next <= sf.vs_alloca_next /\
  read_result cx child fin = (INL v,fin) /\ val_wf etv v ==>
  vv_store_bound cx et et fin child (LocatedValue et (mk_ptr dst LocMemory)) sf
Proof
  strip_tac >>
  `type_memory_size etv = 0 \/ w2n dw + type_memory_size etv <= sf.vs_alloca_next` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` (mp_tac o cj 2 o REWRITE_RULE [vv_store_bound_def]) >>
     disch_then (qspecl_then [`ArrayT et (Fixed n)`,`p.ptr_operand`,`ArrayTV etv (Fixed n)`,`w`] mp_tac) >>
     simp[] >> decide_tac) >>
  `val_store_size etv v <= type_memory_size etv` by simp[val_store_size_le] >>
  simp[vv_store_bound_def, mk_ptr_def] >> decide_tac
QED

Theorem framed_memory_select_in_bounds_mods:
  linked_subscript_array_context_mods mods exps cx et obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et (Fixed n) /\
  subscript_array_framed_memory_case_mods cenv cx obj idx et (Fixed n) /\
  expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1) /\
  expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2) /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,LocatedValue (ArrayT et (Fixed n)) p,iop,Var out,LocMemory)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,IntV i,it,Gi,tni) /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV av) /\ val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_length (ArrayTV etv (Fixed n)) av = n /\ valid_index (ArrayTV etv (Fixed n)) av i /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand it = SOME w /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    vv_post_mods H ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx)
       es sa st2 s0 fin raw (LocatedValue (ArrayT et (Fixed n)) p) it) /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) fin Gi tni it /\
  ptr_buf_ok cenv obj p.ptr_operand Gi it /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at st2 x) /\ (!l. p.ptr_operand <> Label l) /\
  (!v. raw = Value v ==> vv_own cenv cx (ArrayT et (Fixed n)) sa sm mid raw
    (LocatedValue (ArrayT et (Fixed n)) p) s) /\
  (!D lo' explicit. allocas_from lo' it ==>
    gas_origin_ptr_path (D,lo',explicit,ctx,func,PG) (it,Gi,tni) [] (OK sf,Gf,tnf)) /\
  sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
  lookup_var out sf = SOME (w + n2w (Num i * type_memory_size etv)) /\
  op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = op_prov Gi p.ptr_operand /\ ^suffix_frame /\
  (! (H : (bool # bytes32 # type_value) list # num list) cenv' cx' es'.
    stmt_state_rel H ctx func cenv' cx' es' it /\ local_ptrs_reserved cenv' st2 ==>
    stmt_state_rel H ctx func cenv' cx' es' sf) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx et obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sb,Var out,LocMemory) (raw,IntV i) (fin,it,Gi,tni)
Proof
  strip_tac >>
  qpat_assum `linked_subscript_array_context_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qpat_assum `array_nocopy_cut_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  drule_all_then strip_assume_tac fixed_memory_source_inputs >>
  drule_all_then strip_assume_tac fixed_memory_base_types >>
  drule_all_then assume_tac fixed_memory_element_extent >>
  `0 <= i` by fs[valid_index_def] >>
  drule array_index_valid >> pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `v` assume_tac) >>
  `well_formed_type_value etv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type etv v` by
    (irule array_index_has_type >> simp[] >> qexistsl [`av`,`Fixed n`,`i`] >> simp[]) >>
  `val_wf etv v` by (drule_then ACCEPT_TAC value_has_type_memory_wf) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     irule assign_name_memory_bytes_mods >> metis_tac[]) >>
  `st2.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (mp_tac o AP_TERM ``SND : operand # compile_state -> compile_state``) >>
     pure_rewrite_tac[SND] >> disch_then (SUBST1_TAC o SYM) >>
     irule (cj 3 (iffLR ci_mono_def)) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `sa.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\ s.vs_alloca_next <= sf.vs_alloca_next`
    by decide_tac >>
  `eval_operand p.ptr_operand sf = eval_operand p.ptr_operand it` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def]) >>
  `eval_operand p.ptr_operand sf = SOME w` by simp[] >>
  qabbrev_tac `dw = (w:bytes32) + n2w (Num i * type_memory_size etv)` >>
  `eval_operand (Var out) sf = SOME dw` by simp[eval_operand_def] >>
  suspend "source_and_geometry"
QED

Resume framed_memory_select_in_bounds_mods[source_and_geometry]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _`
    (qspec_then `H0` (strip_assume_tac o UNDISCH)) >>
  `vv_post H0 ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx) es sa st2 s0 fin raw
    (LocatedValue (ArrayT et (Fixed n)) p) it` by
    (qpat_assum `vv_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ it` mp_tac >>
     simp[memory_post_mods] >> (gvs[memory_post_mods])) >>
  `vv_place_ptr cenv cx fin it raw (LocatedValue (ArrayT et (Fixed n)) p)` by fs[vv_post_def] >>
  qpat_x_assum `eval_result_typed _ _ (Type (expr_type obj))` (fn typed =>
    qpat_assum `expr_type obj = _` (fn ty_eq => assume_tac (REWRITE_RULE [ty_eq] typed))) >>
  drule_all_then (qx_choose_then `child` strip_assume_tac) fixed_memory_select_source >>
  `!tail. select_result cx (ArrayT et (Fixed n)) raw (ValueSubscript (IntV i))
     (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)` by
    simp[select_result_nonstorage_gas_obs] >>
  `w2n w + val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) < dimword (:256)` by
    (qpat_assum `vv_post _ _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ it`
       (mp_then Any mp_tac vv_post_memory_footprint_bound) >> simp[expr_type_def]) >>
  `w2n dw = w2n w + Num i * type_memory_size etv` by
    (drule_all fixed_array_element_nonwrapping >> simp[Abbr `dw`]) >>
  `op_taint tni p.ptr_operand = {} /\ ptr_mem_ok cx (ArrayT et (Fixed n)) (ArrayV av) p.ptr_operand Gi tni it`
    by (qpat_x_assum `ptr_vv_ok _ _ _ _ fin Gi _ _` mp_tac >>
        simp[ptr_vv_ok_def]) >>
  `0 < type_memory_size etv ==> ptr_covers Gf tnf out sf (type_memory_size etv)` by
    (disch_tac >> drule_all fixed_memory_child_covers >> simp[]) >>
  drule_all_then strip_assume_tac fixed_memory_child_ptr >>
  `vv_store_bound cx (ArrayT et (Fixed n)) (ArrayT et (Fixed n)) mid raw
     (LocatedValue (ArrayT et (Fixed n)) p) s` by
    (qpat_assum `post_value_type cenv obj = _` (fn post_eq =>
     qpat_assum `lowered_value_type cenv obj = _` (fn low_eq =>
     qpat_assum `expr_type obj = _` (fn ty_eq =>
     qpat_assum `vv_store_bound _ _ _ mid _ _ s`
       (ACCEPT_TAC o REWRITE_RULE [post_eq,low_eq,ty_eq]))))) >>
  drule_all_then assume_tac fixed_memory_child_capacity >>
  suspend "child_post"
QED

Resume framed_memory_select_in_bounds_mods[child_post]:
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
      vv_post_mods H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
        (LocatedValue et (mk_ptr (Var out) LocMemory)) sf` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     `stmt_state_rel H ctx func cenv cx fin it` by fs[vv_post_mods_def] >>
     `stmt_state_rel H ctx func cenv cx fin sf` by
       (qpat_assum `!H cenv cx es. stmt_state_rel _ _ _ _ _ _ it /\ _ ==> _`
          (qspecl_then [`H`,`cenv`,`cx`,`fin`] mp_tac) >> simp[]) >>
     drule_all_then assume_tac fixed_memory_framed_post >>
     suspend "post_slice") >>
  suspend "ownership_and_outcome"
QED

Resume framed_memory_select_in_bounds_mods[post_slice]:
  `vv_post H ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx) es sa sb s0 fin raw
    (LocatedValue (ArrayT et (Fixed n)) p) sf /\ immutable_frame_mods func cenv cx fin sf` by
    (qpat_x_assum `vv_post_mods H _ _ _ _ _ _ _ sb _ _ _ _ sf` mp_tac >>
     simp[memory_post_mods]) >>
  `vv_place_ptr cenv cx fin sf raw (LocatedValue (ArrayT et (Fixed n)) p)` by fs[vv_post_def] >>
  drule_all array_element_step_offset >> simp[] >> disch_tac >>
  `expr_sim_inv_mods mods cenv cx env mid` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ idx _` (mp_then Any mp_tac expr_body_pre_mods_inv) >>
     simp[expr_sim_inv_mods_def] >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var out) sf = SOME (w + n2w (Num i * type_memory_size etv))` by simp[Abbr `dw`] >>
  drule_all_then assume_tac fixed_memory_place_step >>
  `(mk_ptr (Var out) LocMemory).ptr_location = LocMemory` by simp[mk_ptr_def] >>
  simp[memory_post_mods] >>
  `vv_post H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
     (LocatedValue et (mk_ptr (Var out) p.ptr_location)) sf` suffices_by simp[] >>
  irule vv_post_array_element >>
  qpat_assum `vv_post H _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ sf` (irule_at Any) >>
  goal_assum (drule_at (Pat `array_index _ _ _ = _`)) >>
  fs[Abbr `dw`] >> simp[] >>
  drule select_result_memory_place >> simp[]
QED

Resume framed_memory_select_in_bounds_mods[ownership_and_outcome]:
  `!v. child = Value v ==> vv_own cenv cx et sa sb fin child
                    (LocatedValue et (mk_ptr (Var out) LocMemory)) sf` by
    (rpt strip_tac >> suspend "value_slice") >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_at_clean_suffix >>
     qexistsl [`Gi`,`tni`] >> simp[] >>
     qx_gen_tac `q` >> disch_tac >>
     `not_fresh_at st2 q` by (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `!q. not_fresh_at st2 q ==> _` drule >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
        ghost_inv_at_mods (DF H) lo d cenv cx fin Gf tnf sf` by
    (rpt strip_tac >> suspend "ghost_suffix") >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (it,Gi,tni) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >>
     `ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it` by simp[] >>
     `allocas_from lo it` by fs[ghost_inv_at_mods_def] >> simp[]) >>
  `alloca_history func sf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `H0` (assume_tac o UNDISCH)) >>
     `stmt_state_rel H0 ctx func cenv cx fin it` by fs[vv_post_def] >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ _ _ _ sb _ _ _ _ sf`
       (qspec_then `H0` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def] o UNDISCH)) >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ _ sf`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  rewrite_tac[array_select_outcome_mods_def] >> simp[] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`Gf`,`fin`,`INL child`,`sf`,`tnf`] >>
  `vv_location (LocatedValue et (mk_ptr (Var out) LocMemory)) = SOME LocMemory`
    by simp[vv_location_def, mk_ptr_def] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[expr_type_def, lowered_value_type_def] >> rpt strip_tac >> simp[]
  >- (qpat_x_assum `child = Value _` SUBST_ALL_TAC >> simp[]) >>
  simp[mk_ptr_def]
QED

Resume framed_memory_select_in_bounds_mods[value_slice]:
  `raw = Value (ArrayV av)` by
    (qpat_assum `!x. child = Value x ==> raw = Value (ArrayV av)` (drule_then ACCEPT_TAC)) >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    (qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv mid.scopes s` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
       (qspec_then `H0` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def] o UNDISCH)) >>
     qpat_assum `stmt_state_rel H0 _ _ _ _ mid s` (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `wb_frame cenv mid fin sm s it` by
    (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ it /\ _`
       (qspec_then `H0` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def] o UNDISCH)) >>
     qpat_assum `expr_post H0 _ _ _ _ idx mid sm st2 s fin _ _ it` (mp_then Any ACCEPT_TAC expr_post_frame)) >>
  `!name b sz. local_region cenv fin.scopes sf name b sz <=> local_region cenv fin.scopes it name b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `st2` >> simp[] >>
     rpt strip_tac >> qpat_assum `!q. not_fresh_at st2 q ==> _` drule >> simp[]) >>
  `vv_own cenv cx (ArrayT et (Fixed n)) sa sm mid (Value (ArrayV av))
    (LocatedValue (ArrayT et (Fixed n)) p) s` by
    (qpat_assum `raw = Value (ArrayV av)` (fn raw_eq =>
       qpat_assum `!x. raw = Value x ==> vv_own _ _ _ _ _ _ raw _ s`
         (qspec_then `ArrayV av` (ACCEPT_TAC o REWRITE_RULE [raw_eq] o UNDISCH)))) >>
  drule_all_then assume_tac fixed_memory_parent_owns >>
  irule vv_own_memory_slice >>
  goal_assum (drule_at (Pat `vv_own _ _ _ _ _ fin _ _ sf`)) >>
  simp[read_result_def, return_def] >>
  qexists_tac `Num i * type_memory_size etv` >>
  `val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) = type_memory_size (ArrayTV etv (Fixed n))`
    by simp[val_footprint_def] >> simp[] >>
  `val_footprint etv v <= val_store_size etv v /\ val_store_size etv v <= type_memory_size etv` by
    simp[val_footprint_le_store_size, val_store_size_le] >> decide_tac
QED

Resume framed_memory_select_in_bounds_mods[ghost_suffix]:
  `ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it` by simp[] >>
  irule ghost_inv_at_mods_exterior_frame >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `st2` >> simp[] >> rpt strip_tac >>
  irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]
QED

Finalise framed_memory_select_in_bounds_mods

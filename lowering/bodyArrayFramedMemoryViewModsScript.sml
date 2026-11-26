(* Preserve the captured memory window across a scope-preserving key. *)
Theory bodyArrayFramedMemoryViewMods
Ancestors
  bodyArrayNoCopyCutsMods bodySubscriptArrayRouteDefsMods
  exprSimSubscriptArrayFrame exprSimSubscriptArrayOrigin exprSimSubscriptArraySuffix
  exprBodyPreProps exprBodyPreTypingProps exprOperandVar exprReasonOperand
  exprSimWordArgs wordArgsPtr bodyPtrBopRepresentationFrame exprBopSimProps
  exprSimProps exprSimArith valueTypingMemoryProps valueEncodingProofs
  vyperTypeEvalSoundness vyperTypeValues vyperTypeInvariants vyperValueOperation
  vyperEvalExprPreservesScopesDom loweringStateRelDefs loweringShapeDefs
  vyperTypeSystem vyperTyping vyperValue vyperContext vyperState
  loweringPosts bodyFullPostsMods bodyPtrDefs context compileEnv exprLoweringProps
  valueEncodingDefs vyperInterpreter arithmeticProps
  exprSimSubscriptArraySource exprSimHypsDefs vyperTypeExprSoundness
  vyperStorageFootprint ptrDiscipline finite_map words integer pair

(* A captured window is either in the preserved allocation interval or
   inside a local whose entire region is kept because the scopes are equal. *)
Theorem captured_window_bytes[local]:
  vv_at cenv cx a sa sm mid raw (LocatedValue a p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw mid = (INL v,mid) /\
  evaluate_type (get_tenv cx) a = SOME tv /\ eval_operand p.ptr_operand s = SOME w /\
  wb_frame cenv mid fin sm s it /\ fin.scopes = mid.scopes ==>
  mem_bytes_at (w2n w) (val_footprint tv v) it.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz it.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (`locals_kept cenv mid fin s it` by fs[wb_frame_def] >>
      `mem_bytes_at b sz it.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_x_assum `locals_kept _ _ _ _ _` mp_tac >>
         simp[locals_kept_def] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem captured_window_taint[local]:
  vv_at cenv cx a sa sm mid raw (LocatedValue a p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw mid = (INL v,mid) /\
  evaluate_type (get_tenv cx) a = SOME tv /\ eval_operand p.ptr_operand s = SOME w /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  w2n w <= j /\ j < w2n w + val_footprint tv v /\ j IN tni.t_mem ==>
  j IN tn1.t_mem
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[ghost_kept_at_def] >>
      `b <= j /\ j < b + sz` by decide_tac >> metis_tac[]) >>
  gvs[ghost_kept_at_def] >>
  `b <= j /\ j < b + sz` by decide_tac >> metis_tac[]
QED

Theorem framed_memory_read_frame[local]:
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  read_result cx raw mid = (INL v,mid) ==>
  read_result cx raw fin = (INL v,fin)
Proof
  strip_tac >>
  `FST (read_result cx raw fin) = FST (read_result cx raw mid)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  Cases_on `read_result cx raw fin` >> gvs[] >>
  drule read_result_state >> simp[]
QED

Theorem framed_memory_read_typed[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,fin) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  `call_evaluation_safe cx (int_calls_expr e)` by fs[expr_body_pre_mods_def] >>
  `env_consistent env cx es /\ state_well_typed es /\ context_well_typed cx /\
   accounts_well_typed es.accounts` by fs[runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound) >>
  disch_then (qspec_then `env` mp_tac) >> simp[value_runtime_typed_def]
QED

Theorem framed_memory_forced_key[local]:
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  (!t r t'. eval_expr cx idx t = (INL r,t') ==>
            t'.scopes = t.scopes /\ t'.immutables = t.immutables) ==>
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables
Proof
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[evaluation_state_accfupds]
QED

Theorem locmemory_place_ptr[local]:
  p.ptr_location = LocMemory ==>
  (vv_place_ptr_mods cenv cx ee s raw (LocatedValue a p) <=>
   vv_place_ptr cenv cx ee s raw (LocatedValue a p))
Proof
  strip_tac >> Cases_on `raw` >>
  simp[vv_place_ptr_mods_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def]
QED

Theorem captured_place_frame[local]:
  vv_place_ptr_mods cenv cx mid s raw (LocatedValue a p) /\
  p.ptr_location = LocMemory /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv mid fin sm s it /\
  eval_operand p.ptr_operand it = eval_operand p.ptr_operand s ==>
  vv_place_ptr_mods cenv cx fin it raw (LocatedValue a p)
Proof
  strip_tac >> fs[locmemory_place_ptr] >>
  `vv_place_ptr cenv cx fin s raw (LocatedValue a p)` by fs[vv_place_ptr_def] >>
  irule vv_place_ptr_vars_frame >> qexists_tac `s` >> simp[vv_operand_def] >>
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sm q` by
    (qpat_assum `local_ptrs_reserved cenv sm`
       (qspecl_then [`id`,`id`,`q`,`sz`,`sz`] mp_tac o cj 2 o
        REWRITE_RULE [local_ptrs_reserved_def]) >> simp[]) >>
  qpat_assum `wb_frame _ _ _ _ _ _`
    (qspecl_then [`q`,`w`] mp_tac o cj 1 o REWRITE_RULE [wb_frame_def]) >> simp[]
QED

Theorem captured_memory_transport[local]:
  vv_at cenv cx (ArrayT et (Fixed n)) sa sm mid raw (LocatedValue (ArrayT et (Fixed n)) p) s /\
  read_result cx raw mid = (INL av,mid) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME tv /\
  vv_holds cenv cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) mid s /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) mid G1 tn1 s /\
  ptr_buf_ok cenv obj p.ptr_operand G1 s /\
  vv_place_ptr_mods cenv cx mid s raw (LocatedValue (ArrayT et (Fixed n)) p) /\
  p.ptr_location = LocMemory /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\ (!l. p.ptr_operand <> Label l) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  wb_frame cenv mid fin sm s it /\
  local_ptrs_rel func cenv mid.scopes s /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_id <= st2.cs_next_id /\ ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni ==>
  vv_holds_mods cenv cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) fin it /\
  vv_at cenv cx (ArrayT et (Fixed n)) sa st2 fin raw (LocatedValue (ArrayT et (Fixed n)) p) it /\
  vv_place_ptr_mods cenv cx fin it raw (LocatedValue (ArrayT et (Fixed n)) p) /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) fin Gi tni it /\
  ptr_buf_ok cenv obj p.ptr_operand Gi it /\
  eval_operand p.ptr_operand it = eval_operand p.ptr_operand s
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand s = SOME w /\ val_in_memory tv av (w2n w) s.vs_memory` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >> simp[vv_holds_def, is_word_type_def]) >>
  `eval_operand p.ptr_operand it = eval_operand p.ptr_operand s` by
    (simp[] >> irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`sm`,`s`] >> fs[wb_frame_def]) >>
  `read_result cx raw fin = (INL av,fin)` by (irule framed_memory_read_frame >> metis_tac[]) >>
  `val_wf tv av` by
    (qpat_assum `vv_at _ _ _ _ _ _ _ _ _`
       (mp_tac o cj 2 o REWRITE_RULE [vv_at_def]) >>
     (impl_tac >- simp[]) >> disch_then (qspecl_then [`av`,`tv`] mp_tac) >> simp[]) >>
  drule_all_then assume_tac captured_window_bytes >>
  `val_in_memory tv av (w2n w) it.vs_memory` by
    (irule val_in_memory_footprint_agree >> simp[] >>
     qexists_tac `s.vs_memory` >> simp[EQ_SYM_EQ]) >>
  simp[] >> conj_tac >- simp[vv_holds_mods_def, vv_holds_def, is_word_type_def] >>
  conj_tac
  >- (irule vv_at_located_frame >> simp[] >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >> qexists_tac `func` >> fs[]) >>
  conj_tac >- (irule captured_place_frame >> metis_tac[]) >>
  `(!x. p.ptr_operand = Var x ==> FLOOKUP Gi x = FLOOKUP G1 x) /\
   op_taint tni p.ptr_operand = op_taint tn1 p.ptr_operand` by
    (Cases_on `p.ptr_operand` >> fs[ghost_kept_at_def, op_taint_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `ptr_vv_ok _ _ _ _ mid _ _ _` mp_tac >> simp[ptr_vv_ok_def] >> strip_tac >>
      irule bop_ptr_mem_ok_frame >> simp[] >>
      goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
      fs[] >> rpt strip_tac >> drule_all captured_window_taint >> simp[]) >>
  qpat_x_assum `ptr_buf_ok _ _ _ G1 _` mp_tac >> simp[ptr_buf_ok_def] >> metis_tac[]
QED

Theorem captured_vv_post_frame[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s ==>
  wb_frame cenv es mid sa s0 s
Proof
  rewrite_tac[vv_post_mods_def, wb_frame_def] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem framed_memory_base_endpoint[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw (LocatedValue (ArrayT et bd) p) s /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  p.ptr_location = LocMemory /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  vv_holds_mods cenv cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) fin it /\
  vv_at cenv cx (ArrayT et bd) sa st2 fin raw (LocatedValue (ArrayT et bd) p) it /\
  vv_place_ptr_mods cenv cx fin it raw (LocatedValue (ArrayT et bd) p) ==>
  vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa st2 s0 fin raw (LocatedValue (ArrayT et bd) p) it
Proof
  strip_tac >>
  drule_then assume_tac captured_vv_post_frame >>
  `wb_frame cenv mid fin sm s it` by metis_tac[expr_post_mods_def, expr_post_frame] >>
  `wb_frame cenv es fin sa s0 it` by (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 it` by
    (strip_tac >>
     `pure_frame cenv func es sa s0 s` by fs[vv_post_mods_def] >>
     `pure_frame cenv func mid sm s it` by metis_tac[expr_post_mods_def, expr_post_pure_frame] >>
     irule pure_frame_trans >> simp[] >> qexistsl_tac [`mid`,`sm`,`s`] >> fs[wb_frame_def]) >>
  `stmt_state_rel H ctx func cenv cx fin it /\ immutable_frame_mods func cenv cx fin it /\
   storage_well_formed_on cx fin (FST H)` by fs[expr_post_mods_def, expr_post_def] >>
  simp[vv_post_mods_def, post_value_type_def, vyperASTTheory.expr_type_def,
       vv_storage_live_def, vv_location_def, expr_has_effect_thm] >>
  fs[wb_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem framed_key_type[local]:
  well_typed_expr env (Subscript ann obj idx) /\ expr_type obj = ArrayT et bd ==>
  ann = et /\ is_int_type (expr_type idx)
Proof
  simp[Once well_typed_expr_def] >> strip_tac >>
  gvs[subscript_type_ok_def] >>
  drule type_place_expr_vtype_annotation >> strip_tac >> Cases_on `vt` >>
  gvs[vtype_annotation_ok_def, subscript_vtype_def, AllCaseEqs()]
QED

Theorem framed_key_word[local]:
  is_int_type (expr_type idx) /\ evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\
  value_has_type tv key /\ expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  ?i iw. key = IntV i /\ eval_operand iop it = SOME iw /\
         i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def, well_formed_type_def] >>
  Cases_on `key` >> gvs[value_has_type_def] >>
  fs[expr_post_mods_def, expr_post_def, expr_val_rel_def, evaluate_type_def, AllCaseEqs(),
     is_word_type_def, valueEncodingTheory.typed_val_to_w256_def,
     valueEncodingTheory.val_to_w256_def] >>
  mp_tac math_val_i2w >>
  disch_then (qspec_then `expr_type idx` (qspec_then `i` mp_tac)) >>
  gvs[arithmeticPropsTheory.math_val_def, is_signed_type_def, type_bits_def, within_int_bound_def]
QED

Theorem fixed_array_typed_view[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME tv /\ value_has_type tv v ==>
  ?etv av. tv = ArrayTV etv (Fixed n) /\ evaluate_type (get_tenv cx) et = SOME etv /\
    v = ArrayV av /\ val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
    array_length (ArrayTV etv (Fixed n)) av = n /\ n < dimword (:256)
Proof
  simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >> strip_tac >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  drule_then assume_tac value_has_type_memory_wf >>
  Cases_on `v` >> gvs[value_has_type_def] >> rename1 `val_wf _ (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def, type_slot_size_def, array_length_def] >>
  `n * 1 <= n * type_slot_size etv` by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  decide_tac
QED

Theorem captured_base_operand_facts[local]:
  compile_expr cenv ty obj sa = (LocatedValue a p,sm) /\
  expr_body_pre_mods mods cenv cx env obj es /\
  expr_type obj = ArrayT et bd /\ p.ptr_location = LocMemory /\
  local_ptrs_reserved cenv sa /\ sm.cs_next_var <= st2.cs_next_var ==>
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x /\ not_fresh_at st2 x) /\
  (!l. p.ptr_operand <> Label l)
Proof
  strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 compiler_compile_var) >> simp[vv_operand_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  irule compile_array_pointer_not_label >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `env` >>
  fs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >> first_assum ACCEPT_TAC
QED

Theorem captured_index_operand_facts[local]:
  lower_value compile_expr cenv ty idx sm = (iop,st2) /\
  local_ptrs_reserved cenv sm /\ expr_body_pre_mods mods cenv cx env idx mid ==>
  (!x. iop = Var x ==> not_fresh_at st2 x) /\ (!l. iop <> Label l)
Proof
  strip_tac >> conj_tac
  >- (drule compile_lower_value_var >> simp[]) >>
  irule lower_compile_expr_not_label >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> qexists_tac `env` >>
  fs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >> first_assum ACCEPT_TAC
QED

Theorem framed_base_not_storage[local]:
  eval_expr cx obj ss = (INL raw,mid) /\
  (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)),t)) ==>
  !tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)
Proof
  metis_tac[]
QED

Theorem framed_memory_base_shape[local]:
  compile_expr cenv ty obj sa = (bvv,sm) /\
  (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory) /\
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
  post_value_type cenv obj = ArrayT et bd ==>
  ?p v w. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocMemory /\
          read_result cx raw mid = (INL v,mid) /\ eval_operand p.ptr_operand s = SOME w
Proof
  strip_tac >>
  `vv_location bvv = SOME LocMemory` by
    (qpat_assum `compile_expr cenv ty obj sa = (bvv,sm)` (fn cut =>
       qpat_assum `!ty st. vv_location (FST (compile_expr cenv ty obj st)) = _`
         (qspecl_then [`ty`,`sa`] (ACCEPT_TAC o PURE_REWRITE_RULE [cut,FST])))) >>
  Cases_on `bvv` >> gvs[vv_location_def, vv_post_mods_def, vv_holds_mods_def,
                       vv_holds_def, is_bytestring_type_def] >>
  metis_tac[]
QED

Theorem framed_memory_reached_view_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_memory_case_mods cenv cx obj idx et bd /\
  expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1) /\
  expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2) /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
  ?n p etv av w i iw.
    bd = Fixed n /\ ann = et /\ bvv = LocatedValue (ArrayT et bd) p /\
    p.ptr_location = LocMemory /\ loc = LocMemory /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\ dynarray_free etv /\
    (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
    fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
    read_result cx raw mid = (INL (ArrayV av),mid) /\
    read_result cx raw fin = (INL (ArrayV av),fin) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\ val_wf (ArrayTV etv bd) (ArrayV av) /\
    array_length (ArrayTV etv bd) av = n /\ n < dimword (:256) /\
    eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand it = SOME w /\
    key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    (valid_index (ArrayTV etv bd) av i <=> idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
       vv_post_mods H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
         es sa st2 s0 fin raw bvv it /\ ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it) /\
    ptr_vv_ok cx (ArrayT et bd) raw bvv fin Gi tni it /\
    ptr_buf_ok cenv obj p.ptr_operand Gi it /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x /\ not_fresh_at st2 x) /\
    (!l. p.ptr_operand <> Label l) /\
    (!x. iop = Var x ==> not_fresh_at st2 x) /\ (!l. iop <> Label l) /\
    (!v. raw = Value v ==> vv_own cenv cx (ArrayT et bd) sa sm mid raw bvv s)
Proof
  strip_tac >>
  qpat_assum `linked_subscript_array_context_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  qpat_x_assum `subscript_array_framed_memory_case_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [subscript_array_framed_memory_case_mods_def]) >>
  qpat_assum `array_nocopy_cut_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  gvs[is_word_type_def, is_bytestring_type_def] >>
  drule_all_then strip_assume_tac framed_memory_forced_key >>
  drule_all_then assume_tac framed_base_not_storage >>
  qabbrev_tac `H0 = storage_trace_horizon fin.storage_trace` >>
  `valid_horizon cx st0 H0 fin.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_all_then (qx_choosel_then [`p`,`v`,`w`] strip_assume_tac) framed_memory_base_shape >>
  gvs[vv_location_def, vv_operand_def] >>
  drule_all_then strip_assume_tac captured_base_operand_facts >>
  drule_all_then strip_assume_tac captured_index_operand_facts >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (drule expr_body_pre_mods_well_typed >> strip_tac >> drule_all framed_key_type >> simp[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key` by
    (irule framed_memory_read_typed >>
     goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_body_pre_mods _ _ _ _ idx _`))) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (strip_assume_tac o UNDISCH)) >>
  drule_all_then strip_assume_tac framed_key_word >>
  `bind (eval_expr cx obj) (read_result cx) (es with gas_obs := gs1) = (INL v,mid)` by
    simp[bind_def] >>
  `?tv. evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME tv /\ value_has_type tv v` by
    (`expr_type obj = ArrayT et (Fixed n)` by first_assum ACCEPT_TAC >>
     qpat_assum `expr_body_pre_mods _ _ _ _ obj _` (mp_then Any mp_tac framed_memory_read_typed) >>
     disch_then (drule_at (Pat `bind _ _ _ = _`)) >> simp[]) >>
  drule_all_then strip_assume_tac fixed_array_typed_view >>
  suspend "endpoint"
QED

Resume framed_memory_reached_view_mods[endpoint]:
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  rename1 `v = ArrayV av` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = _`
       (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >>
     simp[evaluation_state_accfupds]) >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_then assume_tac captured_vv_post_frame >>
  `wb_frame cenv mid fin sm s it` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [expr_post_mods_def]) >>
     disch_then (mp_tac o MATCH_MP expr_post_frame) >> simp[]) >>
  `(!x. p.ptr_operand = Var x ==> not_fresh_at sm x)` by
    (rpt strip_tac >> qpat_assum `!x. p.ptr_operand = Var x ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `vv_holds_mods cenv cx (ArrayT et (Fixed n)) raw
       (LocatedValue (ArrayT et (Fixed n)) p) fin it /\
   vv_at cenv cx (ArrayT et (Fixed n)) sa st2 fin raw
       (LocatedValue (ArrayT et (Fixed n)) p) it /\
   vv_place_ptr_mods cenv cx fin it raw (LocatedValue (ArrayT et (Fixed n)) p) /\
   ptr_vv_ok cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) fin Gi tni it /\
   ptr_buf_ok cenv obj p.ptr_operand Gi it /\
   eval_operand p.ptr_operand it = eval_operand p.ptr_operand s` by
    (qpat_assum `vv_post_mods H0 _ _ _ _ obj _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     `local_ptrs_rel func cenv mid.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
     `vv_holds cenv cx (ArrayT et (Fixed n)) raw (LocatedValue (ArrayT et (Fixed n)) p) mid s` by
       (qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _`
          (mp_tac o REWRITE_RULE [vv_holds_mods_def]) >> simp[]) >>
     irule captured_memory_transport >> simp[] >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `read_result _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     qexists_tac `func` >> simp[] >>
     qpat_assum `post_value_type cenv obj = _` (fn ty_eq =>
       qpat_assum `vv_at _ _ _ _ _ _ _ _ _` (ACCEPT_TAC o REWRITE_RULE [ty_eq]))) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
     simp[] >> qexistsl_tac [`G1`,`mid`,`mid`,`s`,`sm`,`tn1`] >> simp[]) >>
  `read_result cx raw fin = (INL (ArrayV av),fin)` by
    (irule framed_memory_read_frame >> simp[] >> qexists_tac `mid` >> fs[]) >>
  qexistsl_tac [`etv`,`av`,`iw`] >> simp[idx_in_range_integer] >>
  conj_tac >- fs[] >>
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!H. _ ==> valid_horizon _ _ H mid.storage_trace /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  irule framed_memory_base_endpoint >> simp[] >>
  goal_assum (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
Finalise framed_memory_reached_view_mods

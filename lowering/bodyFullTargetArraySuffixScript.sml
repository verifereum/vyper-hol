(* Exact frozen-cut diagnostic boundary. No additional representation premise. *)
Theory bodyFullTargetArraySuffix
Ancestors
  bodyFullTargetSubscript bodyFullTargetArraySource bodyFullTargetArrayLoad
  bodyFullTargetArrayScalar bodyFullTargetAttribute targetSubscriptMemory
  targetSubscriptStorage bodyPtrDefs loweringPosts freshWrites fragGasOriginPtrDead
  targetSubscriptContinuation exprLowering exprSimArrayIndex
  finite_map pair list bodyFullTargetDefs venomState ptrDiscipline exprLoweringProps
  fragFuelExprHelpers
  targetSubscriptSplit bodyPtrBopInMemoryContents vyperTypeSystem
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants vyperTyping
  vyperValue compileEnv valueEncoding vyperTypeEnv vyperInterpreter vyperState

Definition array_tail_packet_def:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 <=>
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  type_place_target env (SubscriptTarget bt e) = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r, sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env mid1 /\ mid1.gas_obs = [] /\
  eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv, mid1) /\
  bind (eval_expr cx e) (read_result cx)
    (mid1 with gas_obs := index_gas) = (INL v, mid2) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2 /\
  storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
  ~t1.vs_halted /\ ~t2.vs_halted /\
  t1.vs_current_bb = sm.cs_current_bb /\
  t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
  t2.vs_current_bb = sn.cs_current_bb /\
  t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history func t1 /\ alloca_history func t2 /\
  s0.vs_alloca_next <= t1.vs_alloca_next /\
  t1.vs_alloca_next <= t2.vs_alloca_next /\
  (!H. valid_horizon cx st0 H mid2.storage_trace ==>
    target_post H ctx func cenv cx es sa sm s0 mid1 pv (Type (ArrayT et bd)) rb t1 /\
    ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
    target_ptr_ok cenv pv rb G1 tn1 t1 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
    expr_store_bound cx (expr_type e) v iop t2 /\
    ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
    ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) /\
    ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2)
End

Theorem array_tail_packet_base_at_index[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  ?w. eval_operand (FST rb) t2 = SOME w /\
      place_ptr_rel cenv cx t2 pv w (FST (SND rb)) (Type (ArrayT et bd)) /\
      op_taint tn2 (FST rb) = {} /\
      op_prov G2 (FST rb) = op_prov G1 (FST rb)
Proof
  simp[array_tail_packet_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[target_post_def] >> strip_tac >>
  `place_ptr_rel cenv cx t2 pv w (FST (SND rb)) (Type (ArrayT et bd))` by
    (irule target_place_ptr_values_frame >> qexistsl [`t1`, `sm`] >>
     fs[expr_post_def]) >>
  `!lbl. FST rb <> Label lbl` by
    metis_tac[target_subscript_typed_base_not_label] >>
  Cases_on `FST rb` >> gvs[eval_operand_def, target_ptr_ok_def,
    op_taint_def, op_prov_def, ghost_kept_at_def, expr_post_def] >>
  metis_tac[]
QED

(* Diagnostic: robust root layout supplies a clean current nested header. *)
Theorem array_tail_robust_path_header_clean[local]:
  !path tv a vs off mem k etv cap tn.
    value_has_type tv a /\ well_formed_type_value tv /\
    (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv a off m) /\
    evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
    mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic cap)) ==>
    mem_word_taint tn.t_mem (off + k) = {}
Proof
  rpt strip_tac >> irule dynarray_memory_header_clean >>
  qexistsl_tac [`cap`, `mem`, `etv`, `vs`] >>
  metis_tac[mem_path_offset_current_value]
QED

Theorem array_tail_packet_source_index:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  expr_sim_inv cenv cx env mid2 /\
  stmt_state_rel H ctx func cenv cx mid2 t2 /\
  ?i iw. v = IntV i /\ eval_operand iop t2 = SOME iw /\
    i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw))
Proof
  simp[array_tail_packet_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all target_array_source_cases >> strip_tac >>
  simp[] >> conj_tac >- fs[expr_post_def] >>
  `is_int_type (expr_type e)` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT ity)` >> Cases_on `ity` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def, evaluate_type_def, AllCaseEqs(),
     is_word_type_def, typed_val_to_w256_def, val_to_w256_def,
     post_value_type_def] >> strip_tac >>
  mp_tac exprSimArithTheory.math_val_i2w >>
  disch_then (qspec_then `expr_type e` (qspec_then `i` mp_tac)) >>
  gvs[arithmeticPropsTheory.math_val_def, is_signed_type_def,
      type_bits_def, within_int_bound_def]
QED

Theorem array_tail_packet_memory_source[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace /\
  pv = PlaceR (MemoryPlace id path) ==>
  ?entry etv av.
    evaluate_type (get_tenv cx) et = SOME etv /\
    lookup_scopes id mid2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
    subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV etv bd) /\
    array_length (ArrayTV etv bd) av < dimword (:256)
Proof
  strip_tac >>
  drule_all array_tail_packet_source_index >> strip_tac >>
  drule_all array_tail_packet_base_at_index >> strip_tac >>
  gvs[] >>
  `target_root bt = NameTarget id` by
    (fs[array_tail_packet_def] >>
     metis_tac[targetPlaceSimTheory.target_base_memory_root_ptr]) >>
  `?entry live. lookup_scopes id mid2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL live` by
    (fs[array_tail_packet_def] >>
     drule_all target_array_source_cases >> simp[]) >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd)` by
    (fs[place_ptr_rel_def, evaluate_type_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  Cases_on `live` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv bd) (ArrayV av)` >>
  metis_tac[target_memory_array_length_bound]
QED

Theorem array_tail_packet_storage_source[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace /\
  pv = PlaceR (StoragePlace tr slot tv) ==>
  ?etv. tv = ArrayTV etv bd /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    storage_read_live H tr (get_storage cx mid2 tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword (:256) /\
    bound_length bd < dimword (:256) /\
    (!cap. bd = Dynamic cap ==>
      w2n (lookup_storage slot (get_storage cx mid2 tr)) <= cap)
Proof
  strip_tac >>
  drule_all array_tail_packet_base_at_index >> strip_tac >> gvs[] >>
  `?etv. tv = ArrayTV etv bd /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    0 < type_slot_size etv /\
    type_slot_size (ArrayTV etv bd) < dimword (:256)` by
    fs[place_ptr_rel_def, evaluate_type_def, AllCaseEqs()] >>
  gvs[] >>
  `bound_length bd < dimword (:256)` by
    (Cases_on `bd` >> fs[type_slot_size_def, vyperASTTheory.bound_length_def] >>
     `n <= n * type_slot_size etv` by
       (Cases_on `type_slot_size etv` >> gvs[arithmeticTheory.MULT_CLAUSES]) >> decide_tac) >>
  fs[array_tail_packet_def] >> first_x_assum drule >> strip_tac >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `storage_well_formed_on cx mid2 (FST H)` by fs[expr_post_def] >>
  drule_all eval_base_place_storage_ready >> simp[]
QED

Theorem array_tail_packet_source_bounds:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  expr_sim_inv cenv cx env mid2 /\
  stmt_state_rel H ctx func cenv cx mid2 t2 /\
  ?i iw. v = IntV i /\ eval_operand iop t2 = SOME iw /\
    i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)) /\
    (!id path. pv = PlaceR (MemoryPlace id path) ==>
      ?entry etv av n.
        lookup_scopes id mid2.scopes = SOME entry /\
        evaluate_type (get_tenv cx) et = SOME etv /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
        subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
        value_has_type (ArrayTV etv bd) (ArrayV av) /\
        n = array_length (ArrayTV etv bd) av /\ n < dimword (:256) /\
        (idx_in_range (is_signed_type (expr_type e)) iw (n2w n) <=>
          0 <= i /\ Num i < n) /\
        extend_place cx pv (ValueSubscript v) mid2 =
          (if idx_in_range (is_signed_type (expr_type e)) iw (n2w n)
           then (INL (PlaceR (MemoryPlace id
                     (path ++ [ValueSubscript v]))),mid2)
           else (INR (Error (RuntimeError "evaluate_subscripts array_index")),mid2))) /\
    (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
      ?etv n.
        tv = ArrayTV etv bd /\ evaluate_type (get_tenv cx) et = SOME etv /\
        n = (case bd of Fixed cap => cap | Dynamic cap =>
                w2n (lookup_storage slot (get_storage cx mid2 tr))) /\
        n < dimword (:256) /\
        (idx_in_range (is_signed_type (expr_type e)) iw (n2w n) <=>
          0 <= i /\ Num i < n) /\
        extend_place cx pv (ValueSubscript v) mid2 =
          (if idx_in_range (is_signed_type (expr_type e)) iw (n2w n)
           then (INL (PlaceR (StoragePlace tr
             (slot + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 1) +
                          Num i * type_slot_size etv)) etv)),mid2)
           else (INR (Error (RuntimeError
             (case bd of Fixed cap => "array fixed oob" | Dynamic cap =>
                if 0 <= i /\ Num i < cap then "array dynamic length oob"
                else "array dynamic capacity oob"))),mid2)))
Proof
  strip_tac >> drule_all array_tail_packet_source_index >> strip_tac >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all array_tail_packet_memory_source >> strip_tac >>
      qexistsl_tac [`entry`, `etv`, `av`] >> simp[] >>
      `idx_in_range (is_signed_type (expr_type e)) iw
         (n2w (array_length (ArrayTV etv bd) av)) <=>
         0 <= i /\ Num i < array_length (ArrayTV etv bd) av` by
        (drule exprSimSubscriptArraySuffixTheory.idx_in_range_integer >>
         disch_then (qspecl_then [`iw`, `is_signed_type (expr_type e)`] mp_tac) >>
         simp[] >> Cases_on `0 <= i` >> simp[] >>
         metis_tac[integerTheory.NUM_LT, integerTheory.NUM_OF_INT,
                   integerTheory.INT_POS]) >>
      simp[] >> gvs[] >> irule extend_place_memory_array_index >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all array_tail_packet_storage_source >> strip_tac >>
  qexists `etv` >> simp[] >>
  qabbrev_tac `n = (case bd of Fixed cap => cap | Dynamic cap =>
       w2n (lookup_storage slot (get_storage cx mid2 tr)))` >>
  `n < dimword (:256)` by
    (Cases_on `bd` >> fs[Abbr `n`, vyperASTTheory.bound_length_def] >> decide_tac) >>
  simp[] >>
  `idx_in_range (is_signed_type (expr_type e)) iw (n2w n) <=>
     0 <= i /\ Num i < n` by
    (drule exprSimSubscriptArraySuffixTheory.idx_in_range_integer >>
     disch_then (qspecl_then [`iw`, `is_signed_type (expr_type e)`] mp_tac) >>
     simp[] >> Cases_on `0 <= i` >> simp[] >>
     metis_tac[integerTheory.NUM_LT, integerTheory.NUM_OF_INT,
               integerTheory.INT_POS]) >>
  simp[] >> gvs[] >>
  simp[extend_place_storage_array_index] >>
  Cases_on `bd` >> fs[Abbr `n`] >>
  rpt IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem array_tail_packet_index_post:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  target_post H ctx func cenv cx es sa sn s0 mid2 pv (Type (ArrayT et bd)) rb t2
Proof
  strip_tac >>
  `place_readable cx mid2 pv` by
    (drule_all array_tail_packet_source_bounds >> strip_tac >>
     Cases_on `pv` >> simp[place_readable_def] >>
     rename1 `PlaceR pl` >> Cases_on `pl` >> simp[place_readable_def] >>
     first_x_assum (qspecl_then [`s`, `l`] mp_tac) >> simp[] >> strip_tac >>
     simp[read_place_def, read_memory_path_def, get_scopes_def,
          bind_def, lift_option_type_def, lift_sum_def, return_def]) >>
  fs[array_tail_packet_def] >> first_x_assum drule >> strip_tac >>
  `!l. FST rb <> Label l` by
    metis_tac[target_subscript_typed_base_not_label] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_base_place_preserves_scopes_dom >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`bt`, `cenv`, `sa`] mp_tac) >> simp[ci_mono_def]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `storage_trace_frame (eval_base_place cx bt)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  drule_all target_post_index_frame >> simp[]
QED

Theorem array_tail_packet_index_kept:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  fs[array_tail_packet_def] >> first_x_assum drule >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_base_place_preserves_scopes_dom >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`bt`, `cenv`, `sa`] mp_tac) >> simp[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
     local_region cenv mid1.scopes t1 name b sz` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl [`s0`, `sa`, `es.scopes`] >> fs[target_post_def]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `storage_trace_frame (eval_base_place cx bt)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (first_x_assum drule >> simp[stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def]) >>
  `!name b sz. local_region cenv mid1.scopes t1 name b sz ==>
     local_region cenv es.scopes s0 name b sz` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame >>
     conj_tac >- metis_tac[] >>
     qexistsl [`sa`, `mid1.scopes`, `t1`] >> fs[target_post_def]) >>
  fs[ghost_kept_at_def, target_post_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `aid < sm.cs_next_id` by decide_tac >>
      `FLOOKUP t1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `!n b len. local_region cenv mid1.scopes t1 n b len ==>
         off + sz <= b \/ b + len <= off` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP t1.vs_allocas aid = _ /\ _ ==> _` irule >>
         metis_tac[]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` irule >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem array_tail_packet_memory_loader:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et (Dynamic cap)
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace /\
  pv = PlaceR (MemoryPlace id path) /\
  emit_op MLOAD [FST rb] sn = (Var out,sl) ==>
  ?a entry etv vs.
    eval_operand (FST rb) t2 = SOME a /\
    lookup_scopes id mid2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
    mload (w2n a) t2 = n2w (LENGTH vs) /\
    array_length_step_ok lo ctx func MLOAD [FST rb] (mload (w2n a) t2)
      sn out sl t2 G2 tn2 /\
    op_taint (step_taint (mk_inst sn.cs_next_id MLOAD [FST rb] [out])
      t2 (update_var out (mload (w2n a) t2) t2) tn2) (Var out) = {} /\
    op_prov (step_prov PG G2 (mk_inst sn.cs_next_id MLOAD [FST rb] [out])
      (update_var out (mload (w2n a) t2) t2)) (Var out) = NONE /\
    evaluate_type (get_tenv cx) et = SOME etv
Proof
  strip_tac >>
  drule_all array_tail_packet_memory_source >> strip_tac >>
  drule_all array_tail_packet_source_index >> strip_tac >>
  drule_all array_tail_packet_base_at_index >> strip_tac >>
  gvs[] >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  `evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) =
     SOME (ArrayTV etv (Dynamic cap))` by
    (fs[place_ptr_rel_def, evaluate_type_def, AllCaseEqs()] >> gvs[]) >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  conj_tac >- fs[valueEncodingDefsTheory.val_in_memory_def, GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  fs[array_tail_packet_def] >> first_x_assum drule >> strip_tac >>
  fs[place_ptr_rel_def] >>
  `tv0 = entry.type` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     qpat_x_assum `!id entry. lookup_scopes id mid2.scopes = _ ==> _`
       (qspecl_then [`id`, `entry`] mp_tac) >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     qpat_x_assum `!id ty. FLOOKUP env.var_types id = _ ==> cenv.ce_var_type id = _` drule >>
     strip_tac >> gvs[] >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes id mid2.scopes = _ ==> _` drule_all >>
     simp[]) >>
  `local_ptrs_rel func cenv mid2.scopes t2` by
    fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `?root. lookup_var p t2 = SOME root /\
     w2n root + sz <= t2.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
     strip_tac >> gvs[]) >>
  gvs[] >>
  `ptr_covers G2 tn2 p t2 sz` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `t2.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]) >>
  `w2n b + k + 32 <= t2.vs_alloca_next /\ w2n b + k < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `w2n (b + n2w k) = w2n b + k` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >>
     `k < dimword (:256)` by decide_tac >> simp[]) >>
  `mem_word_taint tn2.t_mem (w2n b + k) = {}` by
    (irule array_tail_robust_path_header_clean >>
     goal_assum (drule_at (Pos (el 3))) >>
     goal_assum (drule_at (Pos (el 3))) >>
     qexists_tac `t2.vs_memory` >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def, state_well_typed_def] >>
     conj_tac >-
       (fs[ghost_inv_at_def] >>
        qpat_x_assum `!name entry p sz. _ ==> _` drule_all >>
        strip_tac >> gen_tac >> strip_tac >> first_x_assum irule >> simp[]) >>
     drule_all vyperPlaceTypingTheory.lookup_scopes_well_typed_type >> strip_tac >>
     drule_all vyperTypeStatePreservationTheory.lookup_scopes_well_typed_value_has_type >>
     simp[]) >>
  `not_fresh_at sm p` by
    (irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     qpat_x_assum `!n1 n2 p sz1 sz2. _ ==> _` drule >> simp[]) >>
  `FLOOKUP G2 p = FLOOKUP G1 p` by fs[ghost_kept_at_def] >>
  `op_prov G2 (FST rb) = FLOOKUP G2 p` by
    (fs[target_ptr_ok_def] >> first_x_assum drule >> simp[]) >>
  fs[ptr_covers_def] >>
  simp[array_length_step_ok_def] >>
  reverse conj_tac >-
    (simp[op_taint_def, op_prov_def, step_taint_def, step_prov_def,
          venomInstTheory.mk_inst_def, set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
          mem_taint_def, memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def,
          out_taint_def, out_prov_def, FLOOKUP_DRESTRICT]) >>
  conj_tac >-
    simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.exec_read1_def] >>
  reverse conj_tac >-
    (conj_tac >- simp[ptrDisciplineTheory.taint_ok_def, venomInstTheory.mk_inst_def] >>
     conj_tac >- fs[ghost_inv_at_def] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          venomInstTheory.mk_inst_def]) >>
  simp[ptrDisciplineTheory.access_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def,
       venomInstTheory.mk_inst_def] >>
  strip_tac >> Cases_on `FST rb` >> gvs[op_prov_def] >>
  qexistsl_tac [`b'`, `sz'`] >>
  fs[type_memory_size_def] >> decide_tac
QED

Theorem array_tail_live_storage_header_clean[local]:
  storage_read_live (H : (bool # bytes32 # type_value) list # num list) tr st slot tv /\
  0 < type_slot_size tv /\
  storage_agree (storage_dead H tr st) st rt /\
  (!key b. (key,b) IN X ==> storage_dead H tr rt (w2n key) b) ==>
  key_taint X slot = {}
Proof
  strip_tac >>
  drule accountsRelPropsTheory.storage_agree_storage_dead >> strip_tac >>
  simp[key_taint_def, pred_setTheory.EXTENSION] >>
  metis_tac[accountsRelPropsTheory.storage_read_live_head]
QED

Theorem array_tail_packet_storage_loader:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et (Dynamic cap)
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  valid_horizon cx st0 H mid2.storage_trace /\
  pv = PlaceR (StoragePlace tr slot tv) /\
  emit_op (if tr then TLOAD else SLOAD) [FST rb] sn = (Var out,sl) ==>
  ?etv. tv = ArrayTV etv (Dynamic cap) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    eval_operand (FST rb) t2 = SOME slot /\
    storage_read_live H tr (get_storage cx mid2 tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword (:256) /\
    w2n (lookup_storage slot (get_storage cx mid2 tr)) <= cap /\
    (if tr then tload slot t2 else sload slot t2) =
      lookup_storage slot (get_storage cx mid2 tr) /\
    array_length_step_ok lo ctx func (if tr then TLOAD else SLOAD) [FST rb]
      (if tr then tload slot t2 else sload slot t2) sn out sl t2 G2 tn2 /\
    op_taint (step_taint (mk_inst sn.cs_next_id (if tr then TLOAD else SLOAD) [FST rb] [out])
      t2 (update_var out (if tr then tload slot t2 else sload slot t2) t2) tn2) (Var out) = {} /\
    op_prov (step_prov PG G2 (mk_inst sn.cs_next_id (if tr then TLOAD else SLOAD) [FST rb] [out])
      (update_var out (if tr then tload slot t2 else sload slot t2) t2)) (Var out) = NONE
Proof
  strip_tac >>
  drule_all array_tail_packet_storage_source >> strip_tac >>
  drule_all array_tail_packet_source_index >> strip_tac >>
  drule_all array_tail_packet_base_at_index >> strip_tac >>
  gvs[] >>
  `w = slot` by fs[place_ptr_rel_def] >> gvs[] >>
  `w2n slot + type_slot_size (ArrayTV etv (Dynamic cap)) <= dimword (:256)` by decide_tac >>
  drule_all target_storage_array_len_ok >> strip_tac >>
  simp[] >>
  `storage_agree (storage_dead H tr (get_storage cx mid2 tr))
     (get_storage cx mid2 tr) (if tr then contract_transient t2 else contract_storage t2)` by
    (Cases_on `tr` >> fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.storage_rel_def, loweringStateRelDefsTheory.transient_rel_def,
       vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def]) >>
  fs[array_tail_packet_def] >> first_x_assum drule >> strip_tac >>
  `key_taint (if tr then tn2.t_trans else tn2.t_stor) slot = {}` by
    (irule array_tail_live_storage_header_clean >>
     goal_assum (drule_at (Pos (el 4))) >>
     goal_assum (drule_at (Pos (el 3))) >>
     simp[type_slot_size_def] >>
     fs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def,
        sourceUnitExecutionTheory.cx_dead_def] >>
     qpat_x_assum `!H'. dead_sub _ _ /\ _` (qspec_then `H` strip_assume_tac) >>
     Cases_on `tr` >>
     gvs[venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
         pred_setTheory.SUBSET_DEF] >>
     rpt strip_tac >> first_x_assum drule >>
     rw[] >> gvs[vfmStateTheory.lookup_account_def]) >>
  Cases_on `tr` >>
  gvs[array_length_step_ok_def, op_taint_def, op_prov_def, step_taint_def, step_prov_def,
      venomInstTheory.mk_inst_def, set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
      mem_taint_def, memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def,
      out_taint_def, out_prov_def, FLOOKUP_DRESTRICT] >>
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.exec_read1_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, ghost_inv_at_def] >>
  fs[op_taint_def, ghost_inv_at_def]
QED

Theorem array_tail_bounds_uniform[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME iw /\ eval_operand len s = SOME nw /\
  fresh_vars_wrt sa s /\ ~ctx_has_dalloca ctx /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\ allocas_from lo s ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn') /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)) /\
    (!t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
      (t with vs_vars := s.vs_vars) = revert_state (set_returndata [] s) /\
      (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x))
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all array_bounds_check_certified >>
  disch_then (qspecl_then [`func`, `PG`, `ARB`] strip_assume_tac) >>
  simp[] >> qexistsl [`G'`, `tn'`] >> simp[] >>
  rpt strip_tac >>
  drule_all array_bounds_check_certified >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]
QED


Theorem array_tail_address_uniform[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME iw /\
  fresh_vars_wrt sa s /\ op_taint tn bop = {} /\ op_taint tn idx = {} /\
  op_prov G idx = NONE /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn') /\
    op_taint tn' p = {} /\ op_prov G' p = op_prov G bop /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x /\
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
    (t with vs_vars := s.vs_vars) = s /\
    eval_operand p t = SOME ((if dyn then b + n2w ws else b) + iw * n2w esz)
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all array_elem_ptr_certified >>
  disch_then (qspecl_then [`func`, `PG`, `ARB`] strip_assume_tac) >>
  simp[] >> qexistsl [`H`, `tm`] >> simp[] >>
  gen_tac >>
  drule_all array_elem_ptr_certified >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  metis_tac[fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique]
QED

(* Certify the scalar failure once with no dead bytes. Monotonicity then
   keeps the actual failing cursor fixed for every horizon mask. *)
Theorem array_tail_bounds_abort_uniform[local]:
  array_bounds_check idx len sgn sa = ((),sb) /\
  eval_operand idx s = SOME iw /\ eval_operand len s = SOME nw /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn iw nw /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  fn_has_code sa sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn') ==>
  ?t j. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),G',tn')
Proof
  strip_tac >>
  `inst_seq_ptr <| d_stor := K (K {}); d_trans := K (K {});
                   d_imm := K {}; d_ret := K {} |>
     lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by simp[] >>
  drule_all array_bounds_check_joint_abort >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  qexistsl_tac [`t`, `j`] >> simp[] >> gen_tac >>
  irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC
QED

Theorem array_tail_length_uniform[local]:
  (if dyn then compile_ptr_load ctor imm loc bop
   else comp_return (Lit (n2w cnt))) sa = (p,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (dyn ==> ?t G' tn'.
    array_length_loader_ok ctor imm loc bop w sa p sb lo ctx func PG
      s G tn t G' tn') ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand p t = SOME (if dyn then w else n2w cnt) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    array_length_frame sa s G tn t G' tn' /\
    (if dyn then
       array_length_loader_ok ctor imm loc bop w sa p sb lo ctx func PG
         s G tn t G' tn'
     else t = s /\ G' = G /\ tn' = tn)
Proof
  strip_tac >> drule_all array_length_joint >>
  disch_then (qspecl_then [`explicit`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >> gen_tac >>
  irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC
QED

Theorem array_tail_packet_compile_parts[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  ?loc len sl sc p.
    loc = (case FST (SND rb) of SOME l => l | NONE => LocMemory) /\
    SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
    (if (case bd of Dynamic _ => T | _ => F)
     then compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST rb)
     else comp_return (Lit (n2w (case bd of Fixed n => n | _ => 0)))) sn = (len,sl) /\
    array_bounds_check iop len (is_signed_type (expr_type e)) sl = ((),sc) /\
    array_elem_ptr (FST rb) iop (case bd of Dynamic _ => T | _ => F)
      (word_scale loc) (elem_size_in_location cenv loc et) sc = (p,sb) /\
    r = (p,FST (SND rb),SOME (ValPT et))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[array_tail_packet_def, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  drule_all array_tail_packet_index_post >> strip_tac >>
  `SND (SND rb) = SOME (ValPT (ArrayT et bd))` by
    fs[target_post_def, value_type_place_def] >>
  `target_subscript_suffix cenv e rb iop sn = (r,sb)` by
    (fs[array_tail_packet_def] >>
     drule target_subscript_compile_decompose >> strip_tac >> gvs[]) >>
  qpat_x_assum `target_subscript_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [target_subscript_suffix_def] >> strip_tac >>
  Cases_on `(if (case bd of Dynamic _ => T | _ => F)
     then compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
       (case FST (SND rb) of SOME l => l | NONE => LocMemory) (FST rb)
     else comp_return (Lit (n2w (case bd of Fixed n => n | _ => 0)))) sn` >>
  fs[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  Cases_on `_0` >> gvs[] >> metis_tac[]
QED

Theorem array_tail_packet_scalar_inputs[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  allocas_from lo t2 /\
  op_taint tn2 (FST rb) = {} /\ op_taint tn2 iop = {} /\
  op_prov G2 iop = NONE /\
  ?b iw. eval_operand (FST rb) t2 = SOME b /\ eval_operand iop t2 = SOME iw
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[array_tail_packet_def, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  drule_all array_tail_packet_base_at_index >> strip_tac >>
  drule_all array_tail_packet_source_index >> strip_tac >>
  fs[array_tail_packet_def] >> first_x_assum drule >> strip_tac >>
  `is_int_type (expr_type e)` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  fs[expr_post_def, ghost_inv_at_def, ptr_val_ok_def] >>
  `is_word_type (post_value_type cenv e)` by
    (Cases_on `expr_type e` >> gvs[is_int_type_def] >>
     rename1 `is_int_type (BaseT ity)` >> Cases_on `ity` >>
     gvs[is_int_type_def, post_value_type_def, is_word_type_def]) >>
  fs[] >> metis_tac[]
QED

Theorem array_tail_packet_operands_old[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  (!x. FST rb = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[array_tail_packet_def, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  drule_all array_tail_packet_index_post >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    (fs[array_tail_packet_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  conj_tac
  >- (fs[target_post_def, array_tail_packet_def] >>
      metis_tac[not_fresh_at_mono]) >>
  fs[array_tail_packet_def] >>
  metis_tac[exprOperandVarTheory.compile_lower_value_var]
QED

Theorem array_tail_length_frame_operand[local]:
  array_length_frame sa s G tn t G' tn' /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  eval_operand op t = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\
  op_prov G' op = op_prov G op
Proof
  Cases_on `op` >> simp[array_length_frame_def, eval_operand_def,
    op_taint_def, op_prov_def] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem array_tail_packet_dynamic_length[local]:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et (Dynamic cap)
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 /\
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
    (case FST (SND rb) of SOME l => l | NONE => LocMemory)
    (FST rb) sn = (len,sl) ==>
  ?w t G' tn'.
    array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca
      (case FST (SND rb) of SOME l => l | NONE => LocMemory)
      (FST rb) w sn len sl lo ctx func PG t2 G2 tn2 t G' tn' /\
    op_taint tn' len = {} /\ op_prov G' len = NONE
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[array_tail_packet_def, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  drule_all array_tail_packet_base_at_index >> strip_tac >>
  Cases_on `pv` >> fs[place_ptr_rel_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> fs[place_ptr_rel_def]
  >~ [`MemoryPlace id path`]
  >- (gvs[] >>
      `?out. len = Var out` by
        (gvs[contextTheory.compile_ptr_load_def, emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
            fresh_var_def, fresh_id_def, comp_return_def, emit_def]) >>
      gvs[] >>
      `emit_op MLOAD [FST rb] sn = (Var out,sl)` by fs[contextTheory.compile_ptr_load_def] >>
      drule array_tail_packet_memory_loader >> simp[] >>
      disch_then (qspecl_then [`PG`, `storage_trace_horizon mid2.storage_trace`] mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`mload (w2n (b + n2w k)) t2`,
        `update_var out (mload (w2n (b + n2w k)) t2) t2 with vs_inst_idx := LENGTH sl.cs_current_insts`,
        `step_prov PG G2 (mk_inst sn.cs_next_id MLOAD [FST rb] [out]) (update_var out (mload (w2n (b + n2w k)) t2) t2)`,
        `step_taint (mk_inst sn.cs_next_id MLOAD [FST rb] [out]) t2 (update_var out (mload (w2n (b + n2w k)) t2) t2) tn2`] >>
      simp[array_length_loader_ok_def, contextTheory.compile_ptr_load_def] >> metis_tac[]) >>
  rename1 `StoragePlace tr slot tv` >> gvs[] >>
  `?out. len = Var out` by
    (Cases_on `tr` >>
     gvs[slot_loc_def, contextTheory.compile_ptr_load_def, emitHelperTheory.emit_op_def,
         comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
         comp_return_def, emit_def]) >>
  gvs[] >>
  `emit_op (if tr then TLOAD else SLOAD) [FST rb] sn = (Var out,sl)` by
    (Cases_on `tr` >> fs[slot_loc_def, contextTheory.compile_ptr_load_def]) >>
  drule array_tail_packet_storage_loader >> simp[] >>
  disch_then (qspecl_then [`PG`, `storage_trace_horizon mid2.storage_trace`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`if tr then tload slot t2 else sload slot t2`,
    `update_var out (if tr then tload slot t2 else sload slot t2) t2 with vs_inst_idx := LENGTH sl.cs_current_insts`,
    `step_prov PG G2 (mk_inst sn.cs_next_id (if tr then TLOAD else SLOAD) [FST rb] [out]) (update_var out (if tr then tload slot t2 else sload slot t2) t2)`,
    `step_taint (mk_inst sn.cs_next_id (if tr then TLOAD else SLOAD) [FST rb] [out]) t2 (update_var out (if tr then tload slot t2 else sload slot t2) t2) tn2`] >>
  Cases_on `tr` >> gvs[slot_loc_def, array_length_loader_ok_def,
    contextTheory.compile_ptr_load_def] >> metis_tac[]
QED

Theorem array_tail_scalar_compiler_mono[local]:
  (array_bounds_check idx len sgn sa = ((),sb) ==> ci_mono sa sb) /\
  (array_elem_ptr bop idx dyn ws esz sa = (p,sb) ==> ci_mono sa sb)
Proof
  conj_tac
  >- (Cases_on `sgn` >>
      simp[array_bounds_check_def, array_bounds_valid_def, comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
          comp_return_def, emit_def, ci_mono_def, cs_extends_def] >>
      simp[GSYM APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]) >>
  Cases_on `dyn` >>
  simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  metis_tac[ci_mono_emit_op, pairTheory.SND, ci_mono_trans]
QED

Theorem array_tail_length_loader_unique[local]:
  array_length_loader_ok ctor imm loc bop w sa p sb lo ctx func PG s G tn t1 G1 tn1 /\
  array_length_loader_ok ctor imm loc bop w sa p sb lo ctx func PG s G tn t2 G2 tn2 ==>
  t1 = t2 /\ G1 = G2 /\ tn1 = tn2
Proof
  Cases_on `loc = LocCode /\ ctor /\ IS_SOME imm` >>
  simp[array_length_loader_ok_def, LET_THM] >> rpt strip_tac >>
  gvs[array_length_step_ok_def] >>
  gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, comp_return_def, emit_def, venomInstTheory.mk_inst_def] >>
  fs[FUN_EQ_THM] >>
  rpt (qpat_x_assum `!x. _ = _` (qspec_then `sa` mp_tac)) >>
  simp[comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def, compile_state_component_equality,
       venomInstTheory.instruction_component_equality]
QED

Theorem array_tail_packet_initialized:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  ?loc len sl sc p w t G tn b iw.
    loc = (case FST (SND rb) of SOME l => l | NONE => LocMemory) /\
    SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
    (if (case bd of Dynamic _ => T | _ => F)
     then compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST rb)
     else comp_return (Lit (n2w (case bd of Fixed n => n | _ => 0)))) sn = (len,sl) /\
    array_bounds_check iop len (is_signed_type (expr_type e)) sl = ((),sc) /\
    array_elem_ptr (FST rb) iop (case bd of Dynamic _ => T | _ => F)
      (word_scale loc) (elem_size_in_location cenv loc et) sc = (p,sb) /\
    r = (p,FST (SND rb),SOME (ValPT et)) /\
    fn_has_code sn sl func /\ fn_has_code sl sc func /\ fn_has_code sc sb func /\
    sn.cs_next_var <= sl.cs_next_var /\
    (!x. FST rb = Var x ==> not_fresh_at sn x) /\
    (!x. iop = Var x ==> not_fresh_at sn x) /\
    (!x. FST rb = Var x ==> not_fresh_at sl x) /\
    (!x. iop = Var x ==> not_fresh_at sl x) /\
    (!x. len = Var x ==> not_fresh_at sl x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t2,G2,tn2) [] (OK t,G,tn)) /\
    array_length_frame sn t2 G2 tn2 t G tn /\
    eval_operand (FST rb) t = SOME b /\ eval_operand iop t = SOME iw /\
    eval_operand len t = SOME w /\
    op_taint tn (FST rb) = {} /\ op_taint tn iop = {} /\
    op_taint tn len = {} /\ op_prov G iop = NONE /\ op_prov G len = NONE /\
    allocas_from lo t /\ ~t.vs_halted /\
    t.vs_current_bb = sl.cs_current_bb /\ t.vs_inst_idx = LENGTH sl.cs_current_insts
Proof
  strip_tac >>
  drule array_tail_packet_compile_parts >> strip_tac >>
  drule array_tail_packet_operands_old >> strip_tac >>
  drule array_tail_packet_scalar_inputs >> strip_tac >>
  `ci_mono sn sl` by
    (Cases_on `bd` >> gvs[comp_return_def] >>
     metis_tac[ci_mono_compile_ptr_load, pairTheory.SND, ci_mono_refl]) >>
  `ci_mono sl sc /\ ci_mono sc sb` by
    metis_tac[array_tail_scalar_compiler_mono] >>
  `fn_has_code sn sl func /\ fn_has_code sl sc func /\ fn_has_code sc sb func` by
    (fs[array_tail_packet_def] >>
     metis_tac[fragExecTheory.fn_has_code_split, ci_mono_def, cs_extends_trans]) >>
  `sn.cs_next_var <= sl.cs_next_var` by fs[ci_mono_def] >>
  `(!x. FST rb = Var x ==> not_fresh_at sl x) /\
   (!x. iop = Var x ==> not_fresh_at sl x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. len = Var x ==> not_fresh_at sl x` by
    (Cases_on `bd` >> gvs[comp_return_def] >>
     metis_tac[fragFuelExprHelpersTheory.compile_ptr_load_var,
       fragFuelTheory.var_below_def, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  Cases_on `bd`
  >- (gvs[comp_return_def] >>
      qexistsl_tac [`n2w n`, `t2`, `G2`, `tn2`, `b`, `iw`] >>
      simp[eval_operand_def, op_taint_def, op_prov_def, array_length_frame_def] >>
      fs[array_tail_packet_def] >> rpt strip_tac >>
      irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  gvs[] >>
  drule_all array_tail_packet_dynamic_length >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `compile_ptr_load _ _ loc _ _` >>
  `?tl Gl tnl.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (t2,G2,tn2) [] (OK tl,Gl,tnl)) /\
    eval_operand len tl = SOME w /\ ~tl.vs_halted /\
    tl.vs_current_bb = sl.cs_current_bb /\ tl.vs_inst_idx = LENGTH sl.cs_current_insts /\
    array_length_frame sn t2 G2 tn2 tl Gl tnl /\
    array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST rb)
      w sn len sl lo ctx func PG t2 G2 tn2 tl Gl tnl` by
    (irule (array_tail_length_uniform |> Q.INST [`dyn` |-> `T`] |> SRULE []) >>
     fs[array_tail_packet_def] >> metis_tac[]) >>
  `tl = t /\ Gl = G' /\ tnl = tn'` by
    metis_tac[array_tail_length_loader_unique] >>
  gvs[] >>
  drule_all array_tail_length_frame_operand >> strip_tac >>
  `eval_operand (FST rb) t = SOME b /\ op_taint tn' (FST rb) = {}` by
    metis_tac[array_tail_length_frame_operand] >>
  `eval_operand iop t = SOME iw /\ op_taint tn' iop = {} /\ op_prov G' iop = NONE` by
    metis_tac[array_tail_length_frame_operand] >>
  `allocas_from lo t` by
    (gvs[array_length_frame_def, allocas_from_def, venom_state_component_equality] >>
     metis_tac[]) >>
  qexistsl_tac [`w`, `t`, `G'`, `tn'`, `b`, `iw`] >>
  simp[]
QED

Theorem array_tail_scalar_uniform:
  array_bounds_check idx len sgn sa = ((),sc) /\
  array_elem_ptr bop idx dyn ws esz sc = (p,sb) /\
  eval_operand bop s = SOME b /\ eval_operand idx s = SOME iw /\
  eval_operand len s = SOME nw /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. idx = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  op_taint tn bop = {} /\ op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  same_blocks sa sc /\ same_blocks sc sb /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
  fn_has_code sa sc func /\ fn_has_code sc sb func /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sa sc) /\
  EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
               ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (if idx_in_range sgn iw nw then OK t else Abort Revert_abort t,H,tm)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
      FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
      (if idx_in_range sgn iw nw then s else revert_state (set_returndata [] s)) /\
    (idx_in_range sgn iw nw ==>
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      eval_operand p t = SOME ((if dyn then b + n2w ws else b) + iw * n2w esz) /\
      op_prov H p = op_prov G bop /\ op_taint tm p = {})
Proof
  strip_tac >>
  `sc.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all array_bounds_check_nonalias_uniform >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  reverse (Cases_on `idx_in_range sgn iw nw`) >> fs[]
  >- (qexistsl [`t with vs_inst_idx := j`, `H`, `tm`] >> simp[] >>
      qpat_x_assum `t with vs_vars := s.vs_vars = _` mp_tac >>
      simp[venom_state_component_equality, revert_state_def, set_returndata_def]) >>
  `ci_mono sa sc` by metis_tac[array_tail_scalar_compiler_mono] >>
  `(!x. bop = Var x ==> not_fresh_at sc x) /\
   (!x. idx = Var x ==> not_fresh_at sc x)` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  `eval_operand bop t = SOME b /\ eval_operand idx t = SOME iw /\
   op_taint tm bop = {} /\ op_taint tm idx = {} /\
   op_prov H idx = NONE /\ op_prov H bop = op_prov G bop` by
    (Cases_on `bop` >> Cases_on `idx` >>
     gvs[eval_operand_def, lookup_var_def, op_taint_def, op_prov_def] >>
     qpat_x_assum `t with vs_vars := s.vs_vars = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `allocas_from lo t /\ ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb` by
    (qpat_x_assum `t with vs_vars := s.vs_vars = s` mp_tac >>
     simp[venom_state_component_equality, allocas_from_def] >>
     metis_tac[allocas_from_def]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` kall_tac >>
  qabbrev_tac `sg = t with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `eval_operand bop sg = SOME b /\ eval_operand idx sg = SOME iw /\
   allocas_from lo sg` by
    (simp[Abbr `sg`, instIdxIndepTheory.eval_op_inst_idx, allocas_from_def] >>
     fs[allocas_from_def]) >>
  drule_all array_elem_ptr_nonalias_uniform >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sg,H,tm) []
      (OK (t' with vs_inst_idx := LENGTH sb.cs_current_insts),H',tm')` by
    (gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     simp[Abbr `sg`] >>
     qexistsl [`emitted_insts sc sb`, `sc`] >>
     gvs[same_blocks_def]) >>
  qexistsl [`t' with vs_inst_idx := LENGTH sb.cs_current_insts`, `H'`, `tm'`] >>
  simp[instIdxIndepTheory.eval_op_inst_idx] >>
  conj_tac
  >- (gen_tac >>
      `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
        (LENGTH (emitted_insts sa sc) + LENGTH (emitted_insts sc sb))` by gvs[] >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND_NIL]) >>
  conj_tac
  >- (rpt strip_tac >> fs[ci_mono_def, Abbr `sg`] >>
      metis_tac[not_fresh_at_mono]) >>
  qpat_x_assum `t' with vs_vars := sg.vs_vars = sg` mp_tac >>
  qpat_x_assum `t with vs_vars := s.vs_vars = s` mp_tac >>
  simp[Abbr `sg`, venom_state_component_equality, same_blocks_def] >>
  rpt strip_tac >> gvs[same_blocks_def]
QED

Theorem array_tail_packet_finite:
  array_tail_packet tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  ?loc b iw nw t3 G3 tn3.
    loc = (case FST (SND rb) of SOME l => l | NONE => LocMemory) /\
    eval_operand (FST rb) t2 = SOME b /\ eval_operand iop t2 = SOME iw /\
    (!H. valid_horizon cx st0 H mid2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t2,G2,tn2) []
        (if idx_in_range (is_signed_type (expr_type e)) iw nw
         then OK t3 else Abort Revert_abort t3,G3,tn3)) /\
    tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
    (!x. not_fresh_at sn x ==>
      FLOOKUP G3 x = FLOOKUP G2 x /\ FLOOKUP tn3.t_var x = FLOOKUP tn2.t_var x /\
      FLOOKUP t3.vs_vars x = FLOOKUP t2.vs_vars x) /\
    (t3 with <|vs_vars := t2.vs_vars; vs_inst_idx := t2.vs_inst_idx|>) =
      (if idx_in_range (is_signed_type (expr_type e)) iw nw
       then t2 else revert_state (set_returndata [] t2)) /\
    (idx_in_range (is_signed_type (expr_type e)) iw nw ==>
      ~t3.vs_halted /\ t3.vs_current_bb = sb.cs_current_bb /\
      t3.vs_inst_idx = LENGTH sb.cs_current_insts /\
      eval_operand (FST r) t3 = SOME
        ((if (case bd of Dynamic _ => T | _ => F) then b + n2w (word_scale loc) else b) +
         iw * n2w (elem_size_in_location cenv loc et)) /\
      op_prov G3 (FST r) = op_prov G2 (FST rb) /\ op_taint tn3 (FST r) = {})
Proof
  strip_tac >> drule array_tail_packet_initialized >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  `~ctx_has_dalloca ctx` by fs[array_tail_packet_def] >>
  `same_blocks sl sc /\
   sc.cs_current_insts = sl.cs_current_insts ++ emitted_insts sl sc /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
     ~is_terminator ins.inst_opcode) (emitted_insts sl sc)` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     simp[array_bounds_valid_def, comp_bind_def] >>
     Cases_on `is_signed_type (expr_type e)` >> simp[comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >> imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `same_blocks sc sb /\
   sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
     ~is_terminator ins.inst_opcode) (emitted_insts sc sb)` by
    (qpat_x_assum `sc.cs_current_insts = sl.cs_current_insts ++ _` kall_tac >>
     qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     simp[array_elem_ptr_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     Cases_on `bd` >> gvs[comp_return_def] >>
     imp_res_tac emit_op_extends >> imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  drule_all array_tail_scalar_uniform >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  `eval_operand (FST rb) t2 = SOME b /\ eval_operand iop t2 = SOME iw /\
   op_prov G (FST rb) = op_prov G2 (FST rb)` by
    metis_tac[array_tail_length_frame_operand] >>
  qexistsl [`loc`, `b`, `iw`, `w`, `t'`, `H`, `tm`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `idx_in_range (is_signed_type (expr_type e)) iw w` >> fs[] >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND_NIL]) >>
  fs[array_length_frame_def] >>
  conj_tac
  >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[not_fresh_at_mono]) >>
  qpat_x_assum `t' with <|vs_vars := _; vs_inst_idx := _|> = _` mp_tac >>
  qpat_x_assum `(t with vs_inst_idx := _) with vs_vars := _ = _` mp_tac >>
  Cases_on `idx_in_range (is_signed_type (expr_type e)) iw w` >>
  simp[venom_state_component_equality, revert_state_def, set_returndata_def] >>
  rpt strip_tac >> gvs[]
QED

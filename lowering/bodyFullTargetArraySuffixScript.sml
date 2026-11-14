(* Exact frozen-cut diagnostic boundary. No additional representation premise. *)
Theory bodyFullTargetArraySuffix
Ancestors
  bodyFullTargetSubscript bodyFullTargetArraySource bodyFullTargetArrayLoad
  bodyFullTargetArrayScalar bodyFullTargetAttribute targetSubscriptMemory
  targetSubscriptStorage bodyPtrDefs loweringPosts freshWrites
  finite_map pair list bodyFullTargetDefs venomState ptrDiscipline exprLoweringProps
  targetSubscriptSplit bodyPtrBopInMemoryContents vyperTypeSystem
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants vyperTyping
  vyperValue compileEnv valueEncoding vyperTypeEnv

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

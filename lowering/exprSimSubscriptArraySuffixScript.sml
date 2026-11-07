(* Source selection and counted suffix summaries for framed arrays. *)
Theory exprSimSubscriptArraySuffix
Ancestors
  exprSimSubscriptArrayEndpoint exprSimSubscriptArrayFramed
  exprSimSubscriptArraySource gasSummary exprSimDefs vyperState
  vyperPlaceTyping vyperValueOperation vyperArray integer_word words integer
  exprSimSource exprSimCopy exprSimLen valueEncodingProps valueEncoding

Theorem framed_array_select_error:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx r t' = (INL (ArrayV av),t') /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  ~valid_index (ArrayTV etv bd) av i ==>
  select_result cx (ArrayT et bd) r (ValueSubscript (IntV i)) t' =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),t')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac evaluate_array_subscript_oob >>
  Cases_on `r`
  >~ [`read_result cx (HashMapRef tr slot tv key) _ = _`] >-
    gvs[read_result_def, raise_def]
  >~ [`Value value`] >-
    (gvs[read_result_def, return_def] >>
     drule_all select_value_result >> simp[bind_def, lift_sum_def, raise_def]) >>
  drule_all expr_body_pre_place_metadata >> strip_tac >> gnvs[] >>
  `runtime_place_typed cx t' p (ArrayTV etv bd)` by
    (Cases_on `p`
     >~ [`StoragePlace tr slot vt`] >- metis_tac[]
     >~ [`MemoryPlace id path`] >-
       gvs[runtime_place_typed_memory] >>
     qpat_x_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `ALOOKUP t.immutables cx.txn.target` >>
     simp[runtime_place_typed_immutable, get_immutables_def,
          get_address_immutables_def, bind_def, ignore_bind_def, return_def, raise_def]) >>
  drule_all select_nonstorage_place_error >> simp[]
QED

Theorem select_result_nonstorage_gas_obs:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  select_result cx ty r sb (s with gas_obs := gs) =
    (FST (select_result cx ty r sb s), s with gas_obs := gs)
Proof
  strip_tac >> Cases_on `r`
  >~ [`Value v`] >-
    (simp[select_result_def, lift_option_type_def, lift_sum_def,
          bind_def, ignore_bind_def, return_def, raise_def] >>
     rpt (CASE_TAC >> simp[return_def, raise_def]))
  >~ [`HashMapRef tr slot kt vt`] >-
    (Cases_on `sb` >>
     simp[select_result_def, extend_place_def, lift_option_type_def,
          bind_def, ignore_bind_def, return_def, raise_def] >>
     rpt (CASE_TAC >> simp[bind_def, ignore_bind_def, return_def, raise_def])) >>
  Cases_on `p`
  >~ [`StoragePlace tr slot vt`] >- metis_tac[]
  >~ [`MemoryPlace id path`] >-
    (simp[select_result_def, extend_place_def, place_type_value_def,
          read_place_def, get_scopes_def, lift_option_type_def,
          lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def] >>
     rpt (CASE_TAC >> simp[bind_def, ignore_bind_def, return_def, raise_def])) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_immutables_def, get_address_immutables_def,
       lift_option_type_def, lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> simp[bind_def, ignore_bind_def, return_def, raise_def])
QED

Theorem select_result_counted_summary:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  select_result cx ty r sb es = (res,es) /\
  gas_marked_path F ctx func s 0 outcome /\
  ((?t. outcome = OK t /\ Q res (es with gas_obs := []) t) \/
   (exit_result outcome /\ expr_exit res outcome)) ==>
  gas_summary_at F (ctx,func) [] (select_result cx ty r sb) (es,s)
    Q (\res ee outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`,`es`,`outcome`] >> simp[] >>
  simp[gas_marked_exec_def] >>
  drule select_result_nonstorage_gas_obs >> simp[]
QED

Theorem idx_in_range_integer:
  n < dimword (:256) ==>
  (idx_in_range sgn w (n2w n) <=>
   0 <= (if sgn then w2i w else &(w2n w)) /\
   (if sgn then w2i w else &(w2n w)) < &n)
Proof
  strip_tac >> Cases_on `sgn` >>
  simp[exprSimArrayIndexTheory.idx_in_range_def, WORD_LTi, word_0_w2i, w2n_n2w] >>
  Cases_on `word_msb w` >>
  simp[w2i_def] >>
  Cases_on `w = 0w` >> gvs[]
QED

Theorem array_index_word_bounds:
  array_length (ArrayTV et bd) av < dimword (:256) /\
  i = (if sgn then w2i w else &(w2n w)) ==>
  (valid_index (ArrayTV et bd) av i <=>
   idx_in_range sgn w (n2w (array_length (ArrayTV et bd) av)))
Proof
  strip_tac >> drule idx_in_range_integer >> simp[]
QED

Theorem framed_array_element_summary:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  (vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode \/
   (?n. bd = Fixed n)) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue ann p) q /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (p.ptr_location = LocMemory ==> ?n. bd = Fixed n) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) /\
  gas_marked_path F ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all framed_array_select_read >> strip_tac >>
  drule_all vv_post_array_element >> strip_tac >>
  irule select_result_counted_summary >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED

Theorem framed_array_post_view:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\ expr_type obj = ArrayT et bd /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  vv_post ctx func cenv cx obj es sa sc s0 ee r (LocatedValue (ArrayT et bd) p) q /\
  (p.ptr_location = LocMemory \/ (~cenv.ce_is_ctor /\ p.ptr_location = LocCode)) ==>
  ?etv av w.
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    read_result cx r ee = (INL (ArrayV av),ee) /\
    val_wf (ArrayTV etv bd) (ArrayV av) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    eval_operand p.ptr_operand q = SOME w /\
    array_length (ArrayTV etv bd) av < dimword (:256) /\
    (!al. av = SArrayV al ==> ?n. bd = Fixed n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `?v w. read_result cx r ee = (INL v,ee) /\
           eval_operand p.ptr_operand q = SOME w` by
    (fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
        loweringPostsTheory.immutable_holds_def] >> metis_tac[]) >>
  `FST (read_result cx r ee) = FST (read_result cx r t)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `read_result cx r t = (INL v,t)` by
    (Cases_on `read_result cx r t` >> imp_res_tac read_result_state >> gvs[]) >>
  `value_has_type (ArrayTV tv bd) v` by metis_tac[] >>
  `val_wf (ArrayTV tv bd) v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `read_result cx r ee = (INL (ArrayV av),ee)` >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
      vyperValueTheory.type_slot_size_def, vyperValueOperationTheory.array_length_def] >>
  `n * 1 <= n * type_slot_size tv` by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  decide_tac
QED

Theorem framed_array_index_post_view:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\
  value_has_type tv iv /\
  expr_post ctx func cenv cx idx t sm sc u ee iv iop q ==>
  ?i iw. iv = IntV i /\ eval_operand iop q = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  `is_int_type (expr_type idx)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
         vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  Cases_on `expr_type idx` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[vyperTypeSystemTheory.is_int_type_def,
      vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
      vyperTypeSystemTheory.well_formed_type_def] >>
  Cases_on `iv` >> gvs[vyperTypingTheory.value_has_type_def] >>
  fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
     vyperValueTheory.evaluate_type_def, AllCaseEqs(),
     compileEnvTheory.is_word_type_def,
     valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def] >>
  mp_tac exprSimArithTheory.math_val_i2w >>
  disch_then (qspec_then `expr_type idx` (qspec_then `i` mp_tac)) >>
  gvs[arithmeticPropsTheory.math_val_def, compileEnvTheory.is_signed_type_def,
      compileEnvTheory.type_bits_def, vyperValueTheory.within_int_bound_def]
QED

(* Runtime code-array header, independent of the particular length loader. *)
Theorem framed_array_code_length_view:
  stmt_state_rel ctx func cenv cx ee q /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT et (Dynamic cap)) r w ee u /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) ==>
  word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n w) q.vs_data_section ++ REPLICATE 32 0w)) =
  n2w (array_length (ArrayTV etv (Dynamic cap)) av)
Proof
  strip_tac >> drule_all immutable_holds_data >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def, val_in_memory_dynarray,
      mem_word_at_def, vyperValueOperationTheory.array_length_def]
QED

Theorem vv_post_memory_footprint_bound:
  vv_post ctx func cenv cx e es sa sb s0 ee r (LocatedValue ann p) q /\
  p.ptr_location = LocMemory /\
  read_result cx r ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  post_value_type cenv e = expr_type e /\
  eval_operand p.ptr_operand q = SOME w ==>
  w2n w + val_footprint tv v < dimword (:256)
Proof
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_at_def] >>
  rpt strip_tac >>
  qpat_x_assum `post_value_type _ _ = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  first_x_assum (drule_then strip_assume_tac) >> gvs[]
  >- (irule (SIMP_RULE (srw_ss()) [] exprSimHashTheory.hash_live_footprint_bound) >>
      goal_assum (drule_at Any) >> metis_tac[]) 
  >- (irule (SIMP_RULE (srw_ss()) [] exprSimHashTheory.hash_live_footprint_bound) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  irule (SIMP_RULE (srw_ss()) [] (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_lt))
QED

Theorem fixed_array_index_footprint:
  val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v ==>
  Num i * type_memory_size etv <=
    val_footprint (ArrayTV etv (Fixed n)) (ArrayV av)
Proof
  strip_tac >> Cases_on `av` >>
  gvs[valueEncodingTheory.val_wf_def, vyperValueOperationTheory.array_index_def,
      loweringPostsTheory.val_footprint_def, type_memory_size_def,
      AllCaseEqs(), listTheory.oEL_THM] >>
  irule arithmeticTheory.LESS_MONO_MULT >> decide_tac
QED

Theorem fixed_array_element_nonwrapping:
  val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v /\
  w2n (w:bytes32) + val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) < dimword (:256) ==>
  w2n (w + n2w (Num i * type_memory_size etv)) =
    w2n w + Num i * type_memory_size etv
Proof
  strip_tac >> drule_all fixed_array_index_footprint >> strip_tac >>
  irule exprSimAttributePropsTheory.field_ptr_w2n >>
  qexistsl_tac [`0`, `val_footprint (ArrayTV etv (Fixed n)) (ArrayV av)`] >> simp[]
QED

Theorem framed_array_represented_suffix_summary:
  ((?ty. vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode) \/
   (?n. bd = Fixed n)) /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_body_pre cenv cx env obj es /\ expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL r,t) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  local_ptrs_reserved cenv sc /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func cenv cx ee s /\
  vv_post ctx func cenv cx obj es sa sc s0 ee r (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac array_index_word_bounds >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  drule_all_then assume_tac framed_array_select_error >>
  Cases_on `bd`
  >- (`array_length (ArrayTV etv (Fixed n)) av = n` by
        (Cases_on `av` >>
         gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
      fs[Excl "valid_index_def"] >>
      drule_all fixed_array_subscript_counted_oob >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      irule select_result_counted_summary >> simp[] >>
      goal_assum (drule_at Any) >>
      qexists_tac `INR (Error (RuntimeError "evaluate_subscripts array_index"))` >>
      metis_tac[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]) >>
  fs[Excl "valid_index_def"] >>
  `immutable_holds cenv cx (ArrayT et (Dynamic n)) r w ee s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def]) >>
  drule_all_then assume_tac framed_array_code_length_view >>
  `compile_ptr_load F cenv.ce_imm_alloca LocCode = compile_imm_load_word F cenv.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[Excl "valid_index_def"] >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw
     (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[] >>
  drule_all runtime_array_subscript_counted_oob >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume framed_array_represented_suffix_summary[valid]:
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >>
     gvs[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  drule array_index_valid >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `array_index (ArrayTV etv bd) av i = SOME v` >>
  `well_formed_type_value etv` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  `value_has_type etv v` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
  `val_wf etv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`env`,`es`] >> fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >>
     qpat_x_assum `i = _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[integer_wordTheory.w2i_def] >>
     Cases_on `word_msb iw` >> simp[] >>
     rw[] >> gvs[] ) >>
  qpat_x_assum `i = _` kall_tac >>
  Cases_on `bd`
  >- suspend "fixed_valid" >>
  suspend "dynamic_valid"
QED

Resume framed_array_represented_suffix_summary[fixed_valid]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  fs[Excl "valid_index_def"] >>
  drule_all fixed_array_subscript_counted_ok >> strip_tac >>
  `vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue (ArrayT et (Fixed n)) p) t'` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t' = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `eval_operand dst t' = SOME (w + n2w (Num i * type_memory_size etv))` by
    gvs[compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def,
        GSYM wordsTheory.word_mul_n2w] >>
  `p.ptr_location = LocMemory ==> w2n (w + n2w (Num i * type_memory_size etv)) =
      w2n w + Num i * type_memory_size etv` by
    (strip_tac >> irule fixed_array_element_nonwrapping >>
     goal_assum (drule_at Any) >> simp[] >>
     irule (SIMP_RULE (srw_ss()) [] vv_post_memory_footprint_bound) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  qpat_assum `p.ptr_location = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule framed_array_element_summary >> simp[] >>
  (conj_tac >- (qexists_tac `env` >> simp[]) >>
   qexistsl_tac [`ArrayT et (Fixed n)`,`t'`,`w`] >> simp[])
QED

Resume framed_array_represented_suffix_summary[dynamic_valid]:
  fs[Excl "valid_index_def"] >>
  `immutable_holds cenv cx (ArrayT et (Dynamic n)) r w ee s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def]) >>
  drule_all_then assume_tac framed_array_code_length_view >>
  `compile_ptr_load F cenv.ce_imm_alloca LocCode = compile_imm_load_word F cenv.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[Excl "valid_index_def"] >>
  `idx_in_range (is_signed_type (expr_type idx)) (n2w (Num i))
     (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[] >>
  drule_all runtime_array_subscript_counted_ok >> strip_tac >>
  `vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue (ArrayT ann (Dynamic n)) p) t'` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t' = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `eval_operand dst t' = SOME (w + n2w (32 + Num i * type_memory_size etv))` by
    (gvs[compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def,
        compileEnvTheory.word_scale_def, wordsTheory.word_mul_n2w,
        wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC] >>
     simp[GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC] >>
     simp[AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
  qpat_assum `p.ptr_location = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule framed_array_element_summary >> simp[] >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`ArrayT ann (Dynamic n)`,`t'`,`w`] >> simp[]
QED

Finalise framed_array_represented_suffix_summary

Theorem framed_array_suffix_summary:
  ((?ty. vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode) \/
   (?n. bd = Fixed n)) /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL r,t) /\
  eval_expr cx idx t = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  vv_post ctx func cenv cx obj es sa sb s0 t r (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s /\
  ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
  `value_has_type tvt iv` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt iv` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_x_assum `iv = IntV i` SUBST1_TAC >>
     rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def,
                          compileEnvTheory.is_word_type_def]) >>
  `stmt_state_rel ctx func cenv cx ee s` by
    fs[loweringPostsTheory.expr_post_def] >>
  `vv_post ctx func cenv cx obj es sa sc s0 ee r (LocatedValue (ArrayT et bd) p) s` by
    (irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `env` >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) framed_array_post_view >>
  disch_then (qspecl_then [`t`,`env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `eval_result_typed _ ir _` kall_tac >>
  qpat_x_assum `!v. read_result cx ir ee = _ ==> _` kall_tac >>
  qpat_x_assum `value_has_type tvt iv` kall_tac >>
  qpat_x_assum `evaluate_type _ (expr_type idx) = _` kall_tac >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\
   sc.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ sc = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     simp[] >> disch_then (SUBST1_TAC o SYM) >>
     rewrite_tac[GSYM exprLoweringPropsTheory.ci_mono_def] >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue (ArrayT et bd) p) q` by
    (rpt strip_tac >>
     qpat_x_assum `vv_post _ _ _ _ _ _ sa sc _ _ _ _ _` kall_tac >>
     irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `env` >> simp[]) >>
  qpat_x_assum `vv_post _ _ _ _ _ _ sa sb _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ es s0` kall_tac >>
  qpat_x_assum `MAP FDOM _ = _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ idx t` kall_tac >>
  qpat_x_assum `eval_expr cx idx t = _` kall_tac >>
  qpat_x_assum `read_result cx ir ee = _` kall_tac >>
  qpat_x_assum `iv = IntV i` SUBST1_TAC >>
  irule framed_array_represented_suffix_summary >>
  simp[SF SFY_ss] >>
  qexistsl_tac [`iop`,`iw`,`sc`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!x. p.ptr_operand = Var x ==> _` drule >>
  simp[compileEnvTheory.not_fresh_at_def]
QED

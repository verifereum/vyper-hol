(* Storage-specific readonly suffix execution and source observation packaging. *)
Theory exprSimSubscriptArrayLiveStorageSuffix
Ancestors
  exprSimSubscriptArrayLiveStorageEndpoint exprSimSubscriptArrayLiveStorageElement
  exprSimSubscriptArrayCompose exprSimSubscriptArraySuffix targetSubscriptStorage targetSubscriptMemory
  exprSimSubscriptArraySource gasSummary gasOutcome exprSimDefs vyperState
  vyperStorageBackend loweringPosts exprLoweringProps accountsRelProps
  context compileEnv vyperAST vyperValue vyperTyping finite_map

Theorem storage_array_select_counted_summary[local]:
  select_result cx ty (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (ValueSubscript (IntV i)) es = (res,es) /\
  gas_marked_path F ctx func s 0 outcome /\
  ((?t. outcome = OK t /\ Q res (es with gas_obs := []) t) \/
   (exit_result outcome /\ expr_exit res outcome)) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx ty (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
      (ValueSubscript (IntV i))) (es,s) Q (\res ee outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`,`es`,`outcome`] >> simp[] >>
  simp[gas_marked_exec_def] >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  Cases_on `bd` >> Cases_on `tr` >>
  simp[select_result_def, extend_place_storage_array_index, get_storage_def] >>
  rpt IF_CASES_TAC >> simp[get_storage_def]
QED

Theorem live_storage_array_represented_suffix_summary[local]:
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  well_formed_type_value etv /\ ee.gas_obs = [] /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand iop s = SOME (i2w i) /\
  storage_read_live cx tr (get_storage cx ee tr) slot (ArrayTV etv bd) /\
  slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV etv bd) /\
  (!n. bd = Dynamic n ==> w2n (lookup_storage slot (get_storage cx ee tr)) <= n) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 1 (type_slot_size etv)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr)) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved cenv sc /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
         (PlaceR (StoragePlace tr slot (ArrayTV etv bd))) (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
      (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst (slot_loc tr))) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee s /\ eval_operand p.ptr_operand s = SOME slot` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [vv_post_def, vv_place_ptr_def]) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `w2n slot + type_slot_size (ArrayTV etv bd) <= dimword (:256)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_place_ptr_def,
          vyperASTTheory.expr_type_def] >> strip_tac >> Cases_on `tr` >>
     gvs[loweringPostsTheory.vv_holds_def, slot_loc_def, loweringPostsTheory.storage_holds_def,
         accountsRelPropsTheory.storage_range_agree_def]) >>
  Cases_on `bd` >- suspend "fixed" >> suspend "dynamic"
QED
Resume live_storage_array_represented_suffix_summary[fixed]:
  gvs[] >>
  drule target_storage_array_type_bound >> simp[bound_length_def] >> strip_tac >>
  `idx_in_range (is_signed_type (expr_type idx)) (i2w i) (n2w n) <=>
   0 <= i /\ Num i < n` by
    (irule target_typed_index_range >> metis_tac[]) >>
  Cases_on `0 <= i /\ Num i < n`
  >- suspend "fixed_ok" >>
  `~idx_in_range (is_signed_type (expr_type idx)) (i2w i) (n2w n)` by simp[] >>
  `?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)` by
    (fs[slot_loc_def] >> drule target_storage_array_abort_path >> simp[] >> metis_tac[]) >>
  irule storage_array_select_counted_summary >>
  qexistsl_tac [`Abort Revert_abort q`,`INR (Error (RuntimeError "array fixed oob"))`] >>
  simp[select_result_def, extend_place_storage_array_index, expr_exit_def, fragExecTheory.exit_result_def]
QED
Resume live_storage_array_represented_suffix_summary[fixed_ok]:
  `idx_in_range (is_signed_type (expr_type idx)) (i2w i) (n2w n)` by simp[] >>
  `?q. gas_marked_path F ctx func s 0 (OK q) /\
       eval_operand dst q = SOME (slot + i2w i * n2w (type_slot_size etv)) /\
       stmt_state_rel ctx func cenv cx ee q /\
       (!x v. not_fresh_at sc x /\ lookup_var x s = SOME v ==> lookup_var x q = SOME v) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ ~q.vs_halted /\
       q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (fs[slot_loc_def] >> drule target_storage_array_path >> simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx) es sa sd s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed n))))
    (LocatedValue (ArrayT et (Fixed n)) p) q` by (first_x_assum irule >> simp[]) >>
  qpat_x_assum `0 <= i /\ Num i < n` strip_assume_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  `i2w i = n2w (Num i) : bytes32` by simp[integer_wordTheory.i2w_def] >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
    (PlaceR (StoragePlace tr (slot + n2w (Num i * type_slot_size etv)) etv))
    (LocatedValue et (mk_ptr dst (slot_loc tr))) q` by
    (irule live_storage_array_element_post >> simp[bound_length_def, wordsTheory.word_mul_n2w] >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[evaluation_state_component_equality]) >>
  irule storage_array_select_counted_summary >>
  qexistsl_tac [`OK q`, `INL (PlaceR (StoragePlace tr (slot + n2w (Num i * type_slot_size etv)) etv))`] >>
  simp[select_result_def, extend_place_storage_array_index] >> metis_tac[]
QED
Resume live_storage_array_represented_suffix_summary[dynamic]:
  gvs[] >>
  drule target_storage_array_type_bound >> simp[bound_length_def] >> strip_tac >>
  `idx_in_range (is_signed_type (expr_type idx)) (i2w i)
      (if tr then tload slot s else sload slot s) <=>
    0 <= i /\ Num i < n /\ Num i < w2n (lookup_storage slot (get_storage cx ee tr))` by
    (irule (SRULE [] (Q.INST [`dyn` |-> `T`] target_storage_array_live_range)) >> goal_assum (drule_at Any) >> simp[] >>
     qpat_x_assum `type_slot_size _ + w2n _ <= _` mp_tac >>
     simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  Cases_on `0 <= i /\ Num i < n /\ Num i < w2n (lookup_storage slot (get_storage cx ee tr))`
  >- suspend "dynamic_ok" >>
  `~idx_in_range (is_signed_type (expr_type idx)) (i2w i)
      (if tr then tload slot s else sload slot s)` by simp[] >>
  `?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)` by
    (fs[slot_loc_def] >> drule target_storage_array_abort_path >> simp[] >> metis_tac[]) >>
  irule storage_array_select_counted_summary >>
  qexists_tac `Abort Revert_abort q` >>
  Cases_on `0 <= i /\ Num i < n`
  >- (qexists_tac `INR (Error (RuntimeError "array dynamic length oob"))` >>
      simp[select_result_def, extend_place_storage_array_index, expr_exit_def, fragExecTheory.exit_result_def] >> metis_tac[]) >>
  qexists_tac `INR (Error (RuntimeError "array dynamic capacity oob"))` >>
  simp[select_result_def, extend_place_storage_array_index, expr_exit_def, fragExecTheory.exit_result_def] >>
  `~(0 <= i) \/ ~(Num i < n)` by metis_tac[] >> simp[]
QED
Resume live_storage_array_represented_suffix_summary[dynamic_ok]:
  `idx_in_range (is_signed_type (expr_type idx)) (i2w i)
    (if tr then tload slot s else sload slot s)` by simp[] >>
  `?q. gas_marked_path F ctx func s 0 (OK q) /\
       eval_operand dst q = SOME ((slot + 1w) + i2w i * n2w (type_slot_size etv)) /\
       stmt_state_rel ctx func cenv cx ee q /\
       (!x v. not_fresh_at sc x /\ lookup_var x s = SOME v ==> lookup_var x q = SOME v) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ ~q.vs_halted /\
       q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (fs[slot_loc_def] >> drule target_storage_array_path >> simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et (Dynamic n)) obj idx) es sa sd s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic n))))
    (LocatedValue (ArrayT et (Dynamic n)) p) q` by (first_x_assum irule >> simp[]) >>
  qpat_x_assum `0 <= i /\ Num i < n /\ _` strip_assume_tac >>
  `eval_operand dst q = SOME (slot + n2w (1 + Num i * type_slot_size etv))` by
    metis_tac[target_storage_array_offset] >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
    (PlaceR (StoragePlace tr (slot + n2w (1 + Num i * type_slot_size etv)) etv))
    (LocatedValue et (mk_ptr dst (slot_loc tr))) q` by
    (irule live_storage_array_element_post >> simp[bound_length_def] >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[evaluation_state_component_equality]) >>
  irule storage_array_select_counted_summary >>
  qexistsl_tac [`OK q`, `INL (PlaceR (StoragePlace tr (slot + n2w (1 + Num i * type_slot_size etv)) etv))`] >>
  conj_tac
  >- (simp[select_result_def, extend_place_storage_array_index] >>
      simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]) >>
  simp[] >>
  qpat_x_assum `vv_post _ _ _ _ (Subscript et obj idx) _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]
QED
Finalise live_storage_array_represented_suffix_summary

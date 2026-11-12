Theory bodyPtrSubscriptCurrentRootEndpoint
Ancestors
  bodyPtrSubscriptNamedRoot bodyPtrSubscriptIndexRefresh
  bodyPtrSubscriptPendingInit vyperTypeValues vyperValue
  loweringPosts bodyPtrDefs vyperState exprSimDefs vyperTyping
  exprSimSource exprSimHypsDefs vyperInterpreter exprLoweringProps compileEnv loweringStateRelDefs words
  vyperValueOperation valueEncoding list arithmetic vyperTypeSystem vyperAST
  exprBopSimProps integer_word loweringSlice exprSimHyps exprWordOperand
  vyperTypeCallGraph

(* Source invariant preservation refreshes the Name precondition at the
   SAME successful index endpoint; the old array value is never retained. *)
Theorem dynamic_root_at_index_endpoint:
  expr_body_pre cenv cx env (Name (ArrayT et (Dynamic cap)) id) es /\
  expr_body_pre cenv cx env idx es /\
  vyperState$bind (eval_expr cx idx) (\result. read_result cx result) es = (INL iv,ee) /\
  expr_post ctx func cenv cx idx es sa sb s0 ee iv iop s /\
  ghost_inv d cenv cx ee G tn s ==>
  ?entry p sz a tv vs.
    lookup_scopes id ee.scopes = SOME entry /\
    entry.type = ArrayTV tv (Dynamic cap) /\
    entry.value = ArrayV (DynArrayV vs) /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    cap < dimword (:256) /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME a /\
    w2n a + sz < dimword (:256) /\
    type_memory_size (ArrayTV tv (Dynamic cap)) <= sz /\
    ptr_covers G tn p s sz /\
    read_result cx (PlaceR (MemoryPlace id [])) ee =
      (INL (ArrayV (DynArrayV vs)),ee) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_x_assum `expr_body_pre _ _ _ (Name _ _) _` kall_tac >>
     drule_all expr_body_pre_eval >> simp[]) >>
  `expr_body_pre cenv cx env (Name (ArrayT et (Dynamic cap)) id) ee` by
    fs[expr_body_pre_def] >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  drule_all named_root_preparation >> strip_tac >>
  `w2n a + sz < dimword (:256)` by
    (`local_ptrs_rel func cenv ee.scopes s /\ alloca_room ctx func s` by
       fs[stmt_state_rel_def, state_rel_def] >>
     drule alloca_room_next_lt >> strip_tac >>
     qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac) >>
  drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  `cap < dimword (:256)` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = _`
       (mp_then Any mp_tac (cj 1 evaluate_type_well_formed)) >>
     simp[well_formed_type_value_def]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  rename1 `value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  drule current_root_read >> simp[]
QED

(* Bounds use the CURRENT typed array.  They remain valid for zero-sized
   element types; strict address no-wrap comes from the root allocation. *)
Theorem dynamic_root_selected_bounds:
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  cap < dimword (:256) /\
  array_index (ArrayTV tv (Dynamic cap)) (DynArrayV vs) i = SOME v /\
  type_memory_size (ArrayTV tv (Dynamic cap)) <= sz /\
  w2n (a:bytes32) + sz < dimword (:256) ==>
  0 <= i /\ Num i < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  v = EL (Num i) vs /\
  32 + Num i * type_memory_size tv + type_memory_size tv <= sz /\
  w2n a + 32 + Num i * type_memory_size tv < dimword (:256)
Proof
  simp[value_has_type_def, array_index_def, AllCaseEqs(),
       oEL_THM, type_memory_size_def] >>
  rpt strip_tac >> gvs[] >>
  `Num i + 1 <= cap` by decide_tac >>
  `(Num i + 1) * type_memory_size tv <= cap * type_memory_size tv` by
    simp[] >>
  qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
  pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

Theorem dynamic_named_subscript_index_type:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Dynamic cap)) id) idx) es ==>
  ann = et /\ is_int_type (expr_type idx)
Proof
  simp[expr_body_pre_def, well_typed_expr_def, subscript_type_ok_def,
       expr_type_def] >> metis_tac[]
QED

Theorem integer_index_endpoint_operand:
  expr_body_pre cenv cx env idx es /\
  expr_post ctx func cenv cx idx es sa sb s0 ee (IntV i) op s /\
  ptr_val_ok cx (expr_type idx) (IntV i) op G tn s /\
  is_int_type (expr_type idx) /\ 0 <= i ==>
  eval_operand op s = SOME (n2w (Num i)) /\
  op_taint tn op = {} /\ op_prov G op = NONE
Proof
  strip_tac >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[is_int_type_def, is_word_type_def] >>
     Cases_on `b` >> gvs[is_int_type_def, is_word_type_def]) >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type idx))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  `expr_val_rel cx (expr_type idx) (IntV i) op s` by fs[expr_post_def] >>
  `word_value (IntV i)` by simp[word_value_def] >>
  drule_all expr_val_rel_word >>
  gvs[val_to_w256_def, ptr_val_ok_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >> simp[integer_wordTheory.i2w_def]
QED

Theorem dynamic_root_selection_success:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\
  select_result cx ty (PlaceR (MemoryPlace id []))
    (ValueSubscript iv) es = (INL rr,ee) ==>
  ?i child. iv = IntV i /\
    array_index (ArrayTV tv (Dynamic cap)) (DynArrayV vs) i = SOME child /\
    rr = PlaceR (MemoryPlace id [ValueSubscript (IntV i)]) /\ ee = es
Proof
  strip_tac >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, lift_option_type_def, bind_def,
       return_def, subscripts_type_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, ignore_bind_def, extend_memory_place_def] >>
  Cases_on `iv` >> simp[evaluate_subscripts_def, AllCaseEqs(), raise_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `array_index (ArrayTV tv (Dynamic cap)) (DynArrayV vs) i` >>
  gvs[return_def, raise_def]
QED

(* All numerical and representation premises belong to the same ordinary
   index endpoint. No representation-preservation callback is assumed. *)
Theorem dynamic_root_successful_index_endpoint:
  expr_body_pre cenv cx env
    (Subscript ann (Name (ArrayT et (Dynamic cap)) id) idx) es /\
  expr_body_pre cenv cx env (Name (ArrayT et (Dynamic cap)) id) es /\
  expr_body_pre cenv cx env idx es /\
  vyperState$bind (eval_expr cx idx) (\result. read_result cx result) es = (INL iv,ee) /\
  expr_post ctx func cenv cx idx es sa sb s0 ee iv iop s /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_val_ok cx (expr_type idx) iv iop G tn s /\
  lower_value compile_expr cenv ty idx sa = (iop,sb) /\
  local_ptrs_reserved cenv sb /\
  select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id []))
    (ValueSubscript iv) ee = (INL rr,ef) ==>
  ?entry p sz a tv vs i child.
    lookup_scopes id ee.scopes = SOME entry /\
    entry.type = ArrayTV tv (Dynamic cap) /\
    entry.value = ArrayV (DynArrayV vs) /\
    evaluate_type (get_tenv cx) et = SOME tv /\ ann = et /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME a /\ w2n a + sz < dimword (:256) /\
    ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
    iv = IntV i /\ 0 <= i /\
    eval_operand iop s = SOME (n2w (Num i)) /\
    op_taint tn iop = {} /\ op_prov G iop = NONE /\
    Num i < LENGTH vs /\ LENGTH vs < dimword (:256) /\
    child = EL (Num i) vs /\
    rr = PlaceR (MemoryPlace id [ValueSubscript (IntV i)]) /\ ef = ee /\
    type_memory_bytes cenv et = type_memory_size tv /\
    32 + Num i * type_memory_size tv + type_memory_size tv <= sz /\
    w2n a + 32 + Num i * type_memory_size tv < dimword (:256) /\
    not_fresh_at sb p /\ (!q. iop = Var q ==> not_fresh_at sb q) /\
    (!l. iop <> Label l)
Proof
  strip_tac >>
  drule_all dynamic_root_at_index_endpoint >> strip_tac >>
  drule_all dynamic_root_selection_success >> strip_tac >> gvs[] >>
  `w2n a + sz < dimword (:256)` by decide_tac >>
  drule_all dynamic_root_selected_bounds >> strip_tac >>
  drule_all dynamic_named_subscript_index_type >> strip_tac >> gvs[] >>
  `eval_operand iop s = SOME (n2w (Num i)) /\
   op_taint tn iop = {} /\ op_prov G iop = NONE` by
    (drule_all integer_index_endpoint_operand >> simp[]) >>
  `type_memory_bytes cenv ann = type_memory_size tv` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     fs[expr_body_pre_def] >> metis_tac[]) >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[is_int_type_def, is_word_type_def] >>
     Cases_on `b` >> gvs[is_int_type_def, is_word_type_def]) >>
  `expr_sim_pre cenv cx env (Name (ArrayT ann (Dynamic cap)) id) es` by
    fs[expr_sim_pre_def, expr_body_pre_def, int_calls_expr_def] >>
  drule expr_sim_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env idx` by fs[expr_body_pre_def] >>
  drule_all lower_value_word_shape >> strip_tac >>
  `not_fresh_at sb p` by metis_tac[local_ptrs_reserved_def] >>
  simp[]
QED

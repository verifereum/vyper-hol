Theory bodyPtrSubscriptSeamArrayMemoryEndpoint
Ancestors
  bodyPtrDefs bodyPtrSubscriptCurrentMemory exprSimProps valueEncoding valueEncodingDefs
  loweringPosts venomState ptrDiscipline finite_map
  exprSimSubscriptArraySuffix exprSimSubscriptArrayFramed words
  bodyPtrEnvBuiltinsBoundary context

Theorem ptr_mem_ok_array_child:
  ptr_mem_ok cx ty (ArrayV av) op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv (ArrayV av) /\
  array_index tv av i = SOME v /\
  mem_step_offset tv (ValueSubscript (IntV i)) = SOME (j,etv) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ val_wf etv v /\
  eval_operand op s = SOME w /\ eval_operand (Var out) sf = SOME dw /\
  w2n dw = w2n w + j /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  ptr_covers Gf tnf out sf (type_memory_size etv) ==>
  ptr_mem_ok cx et v (Var out) Gf tnf sf
Proof
  strip_tac >>
  `val_store_size etv v <= type_memory_size etv` by metis_tac[val_store_size_le] >>
  simp[ptr_mem_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      `val_in_memory tv (ArrayV av) (w2n w) mem` by
        (qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
         simp[ptr_mem_ok_def] >> metis_tac[]) >>
      drule_all array_index_in_memory >> simp[]) >>
  strip_tac >> gvs[ptr_covers_def, eval_operand_def] >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem ptr_vv_ok_array_child:
  ptr_vv_ok cx ty r (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\ read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv (ArrayV av) /\
  array_index tv av i = SOME v /\
  mem_step_offset tv (ValueSubscript (IntV i)) = SOME (j,etv) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ val_wf etv v /\
  read_result cx child es = (INL v,es) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand (Var out) sf = SOME dw /\
  w2n dw = w2n w + j /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  ptr_covers Gf tnf out sf (type_memory_size etv) ==>
  ptr_vv_ok cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) es Gf tnf sf
Proof
  strip_tac >>
  `ptr_mem_ok cx ty (ArrayV av) p.ptr_operand G tn s` by gvs[ptr_vv_ok_def] >>
  `ptr_mem_ok cx et v (Var out) Gf tnf sf` by
    (irule ptr_mem_ok_array_child >> metis_tac[]) >>
  simp[ptr_vv_ok_def, contextTheory.mk_ptr_def] >>
  gvs[ptr_covers_def]
QED

Theorem fixed_array_child_bounds:
  val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v /\
  w2n (w:bytes32) + val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) < dimword (:256) ==>
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    SOME (Num i * type_memory_size etv,etv) /\
  Num i * type_memory_size etv + type_memory_size etv <=
    type_memory_size (ArrayTV etv (Fixed n)) /\
  w2n w + Num i * type_memory_size etv < dimword (:256) /\
  w2n (w + n2w (Num i * type_memory_size etv)) =
    w2n w + Num i * type_memory_size etv
Proof
  strip_tac >>
  `0 <= i /\ Num i < n` by
    (Cases_on `av` >>
     gvs[vyperValueOperationTheory.array_index_def, val_wf_def,
         listTheory.oEL_THM, AllCaseEqs()]) >>
  `mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    SOME (Num i * type_memory_size etv,etv)` by simp[mem_step_offset_def] >>
  `mem_path_offset (ArrayTV etv (Fixed n)) [ValueSubscript (IntV i)] =
    SOME (Num i * type_memory_size etv,etv)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> strip_tac >> simp[] >>
  conj_tac
  >- (drule_all fixed_array_index_footprint >> decide_tac) >>
  metis_tac[fixed_array_element_nonwrapping]
QED

Theorem fixed_array_child_endpoint:
  vv_post ctx func cenv cx obj es sa sb s0 ee r
    (LocatedValue ann p) sf /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) r (LocatedValue ann p) ee G tn s /\
  expr_type obj = ArrayT et (Fixed n) /\ post_value_type cenv obj = expr_type obj /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v /\ val_wf etv v /\
  value_has_type etv v /\ read_result cx child ee = (INL v,ee) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand sf = SOME w /\
  eval_operand (Var out) sf = SOME (w + n2w (Num i * type_memory_size etv)) /\
  w2n (w + n2w (Num i * type_memory_size etv)) =
    w2n w + Num i * type_memory_size etv /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    SOME (Num i * type_memory_size etv,etv) /\
  sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  ptr_covers Gf tnf out sf (type_memory_size etv) /\
  type_memory_bytes cenv (lowered_value_type cenv (Subscript et obj idx)) <=
    type_memory_size etv ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sb s0 ee child
    (LocatedValue et (mk_ptr (Var out) LocMemory)) sf /\
  ptr_vv_ok cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) ee Gf tnf sf /\
  ptr_buf_ok cenv (Subscript et obj idx) (Var out) Gf sf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (drule vv_post_array_element >> simp[] >>
      disch_then irule >> simp[] >> qexists_tac `i` >> simp[]) >>
  conj_tac
  >- (irule ptr_vv_ok_array_child >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule ptr_covers_buf_ok >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `tnf` >> simp[]
QED

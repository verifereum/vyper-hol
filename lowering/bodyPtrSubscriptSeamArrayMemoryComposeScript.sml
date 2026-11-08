Theory bodyPtrSubscriptSeamArrayMemoryCompose
Ancestors
  bodyPtrSubscriptSeamArrayMemorySuffix bodyPtrSubscriptSeamArrayMemoryEndpoint
  bodyPtrSubscriptSeamArrayMemoryFrame bodyPtrSubscriptSeamArrayMemoryTyping
  bodyPtrSubscriptSeamArrayMemoryPrepare bodyPtrSubscriptMarkedCompose
  exprSimSubscriptArraySuffix exprSimSubscriptArrayFramed
  fragGasPathPtr gasSummary exprSimDefs vyperState

Theorem select_result_counted_summary_ptr:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  select_result cx ty r sb es = (res,es) /\
  gas_path_ptr D 0 ctx func PG G0 tn0 s 0 G tn outcome /\
  ((?t. outcome = OK t /\ Q res (es with gas_obs := []) G tn t) \/
   (exit_result outcome /\ R res (es with gas_obs := []) (G,tn) outcome)) ==>
  gas_summary_ptr_at D (ctx,func) PG [] (select_result cx ty r sb)
    (es,s,G0,tn0) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`res`,`es`,`G`,`tn`,`outcome`] >> simp[] >>
  drule select_result_nonstorage_gas_obs >> simp[]
QED

Theorem fixed_array_element_summary_ptr:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et (Fixed n) /\ post_value_type cenv obj = expr_type obj /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue ann p) sf /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) r (LocatedValue ann p) ee G tn s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv (Fixed n)) (ArrayV av) /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV av) /\
  array_index (ArrayTV etv (Fixed n)) av i = SOME v /\ val_wf etv v /\
  value_has_type etv v /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand p.ptr_operand sf = SOME w /\
  eval_operand (Var out) sf = SOME (w + n2w (Num i * type_memory_size etv)) /\
  w2n (w + n2w (Num i * type_memory_size etv)) = w2n w + Num i * type_memory_size etv /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    SOME (Num i * type_memory_size etv,etv) /\
  sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  ptr_covers Gf tnf out sf (type_memory_size etv) /\
  type_memory_bytes cenv (lowered_value_type cenv (Subscript et obj idx)) <=
    type_memory_size etv /\
  gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
  sf.vs_current_bb = sd.cs_current_bb /\ sf.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ghost_inv d cenv cx ee Gf tnf sf /\ ghost_kept cenv es sa G0 tn0 s0 Gf tnf ==>
  gas_summary_ptr_at D (ctx,func) PG []
    (select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i))) (ee,s,G,tn)
    (\res ee' H tm q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr (Var out) LocMemory)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
      ghost_inv d cenv cx ee' H tm q /\
      ptr_vv_ok cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) ee' H tm q /\
      ptr_buf_ok cenv (Subscript et obj idx) (Var out) H q /\
      ghost_kept cenv es sa G0 tn0 s0 H tm)
    (\res ee' gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?child. select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i)) ee =
     (INL child,ee) /\ read_result cx child ee = (INL v,ee)` by
    (irule framed_array_select_read >> simp[] >> metis_tac[]) >>
  drule_all fixed_array_child_endpoint >> strip_tac >>
  irule select_result_counted_summary_ptr >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED

Theorem fixed_array_rejected_summary_ptr:
  expr_body_pre cenv cx env obj es /\ eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et (Fixed n) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  ~valid_index (ArrayTV etv (Fixed n)) av i /\
  compile_array_subscript base_op idx F n ws elem_size sgn loader sc = (op,sd) /\
  fn_has_code sc sd func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand idx s = SOME iw /\
  ~((sgn ==> 0 <= w2i iw) /\ w2n iw < w2n (n2w n:bytes32)) /\
  op_taint tn idx = {} /\
  (!q. idx = Var q ==> not_fresh_at sc q) /\ (!l. idx <> Label l) ==>
  gas_summary_ptr_at D (ctx,func) PG []
    (select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i))) (ee,s,G,tn)
    Q (\res ee' gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i)) ee =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)` by
    (irule framed_array_select_error >> simp[] >>
     gvs[vyperArrayTheory.valid_index_def] >> metis_tac[]) >>
  drule_all static_selector_rejects_counted >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  irule select_result_counted_summary_ptr >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[expr_exit_def, fragExecTheory.exit_result_def]
QED

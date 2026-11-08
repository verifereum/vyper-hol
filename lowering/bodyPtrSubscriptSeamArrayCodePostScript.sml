(* Source-selection boundary for the counted pointer suffix. *)
Theory bodyPtrSubscriptSeamArrayCodePost
Ancestors
  bodyPtrSubscriptSeamArrayCodeSuffix exprSimSubscriptArraySuffix
  bodyPtrDefs gasSummary fragGasPathPtr vyperState
  exprSimSubscriptArrayFramed exprSimSubscriptArraySource

Theorem select_result_ptr_counted_summary:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  select_result cx ty r sb es = (res,es) /\
  gas_path_ptr D 0 ctx func PG G0 tn0 s 0 G tn outcome /\
  ((?t. outcome = OK t /\ Q res (es with gas_obs := []) G tn t) \/
   (exit_result outcome /\ expr_exit res outcome)) ==>
  gas_summary_ptr_at D (ctx,func) PG [] (select_result cx ty r sb) (es,s,G0,tn0)
    Q (\res ee gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [`res`,`es`,`G`,`tn`,`outcome`] >> simp[] >>
  drule select_result_nonstorage_gas_obs >> simp[]
QED

Theorem code_array_element_ptr_summary:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue ann p) q /\
  p.ptr_location = LocCode /\ eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w + n2w j) /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  gas_path_ptr D 0 ctx func PG G0 tn0 s 0 G tn (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
  ghost_inv d cenv cx ee G tn q /\ ghost_kept cenv es sa Ginit tninit s0 G tn ==>
  gas_summary_ptr_at D (ctx,func) PG []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s,G0,tn0)
    (\res ee' G tn q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst LocCode)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
      ghost_inv d cenv cx ee' G tn q /\
      ptr_vv_ok cx (post_value_type cenv (Subscript et obj idx)) child
        (LocatedValue et (mk_ptr dst LocCode)) ee' G tn q /\
      ghost_kept cenv es sa Ginit tninit s0 G tn)
    (\res ee' gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?child. select_result cx (ArrayT et bd) r (ValueSubscript (IntV i)) ee =
      (INL child,ee) /\ read_result cx child ee = (INL v,ee)` by
    (irule framed_array_select_read >> simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee child
     (LocatedValue et (mk_ptr dst p.ptr_location)) q` by
    (irule vv_post_array_element >> simp[] >> metis_tac[]) >>
  irule select_result_ptr_counted_summary >> simp[] >>
  qexistsl [`G`,`OK q`,`tn`] >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  gvs[ptr_vv_ok_def, contextTheory.mk_ptr_def]
QED

Theorem code_array_rejection_ptr_summary:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\ expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  ~valid_index (ArrayTV etv bd) av i /\
  gas_path_ptr D 0 ctx func PG G0 tn0 s 0 G tn
    (Abort Revert_abort (revert_state (set_returndata [] q))) ==>
  gas_summary_ptr_at D (ctx,func) PG []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s,G0,tn0)
    Q (\res ee' gt outcome. expr_exit res outcome)
Proof
  strip_tac >> drule_all framed_array_select_error >> strip_tac >>
  irule select_result_ptr_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Theorem code_array_bound_view:
  stmt_state_rel ctx func cenv cx ee s /\ ~cenv.ce_is_ctor /\
  vv_post ctx func cenv cx obj es sa sc s0 ee r (LocatedValue ann p) s /\
  post_value_type cenv obj = ArrayT et bd /\ p.ptr_location = LocCode /\
  eval_operand p.ptr_operand s = SOME w /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  (case bd of Fixed n => n2w n | Dynamic cap =>
    word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))) =
  n2w (array_length (ArrayTV etv bd) av)
Proof
  strip_tac >> Cases_on `bd`
  >- (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,
       vyperValueOperationTheory.array_length_def]) >>
  simp[] >> irule framed_array_code_length_view >> simp[] >>
  goal_assum (drule_at Any) >>
  gvs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def] >> metis_tac[]
QED

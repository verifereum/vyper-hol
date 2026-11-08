(* Entry gas adapters: evaluation keeps its actual marked observations. *)
Theory bodyPtrSubscriptSeamArrayCodeGas
Ancestors
  bodyPtrSubscriptSeamArrayCodeSummary exprSimSubscriptArraySuffix
  bodyPtrEnvBuiltinsEntryFrame exprSimSource exprSimProps

Theorem code_array_marked_post_view:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj (es with gas_obs := gs) = (INL r,t) /\
  expr_type obj = ArrayT et bd /\
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
  irule framed_array_post_view >> simp[] >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  simp[vv_post_initial_gas] >> metis_tac[]
QED

Theorem code_array_marked_suffix_ptr_summary:
  expr_body_pre cenv cx env obj es /\ expr_type obj = ArrayT et bd /\
  post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj (es with gas_obs := gs) = (INL r,t) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode /\
  ~cenv.ce_is_ctor /\ p.ptr_location = LocCode /\
  local_ptrs_reserved cenv sc /\ sa.cs_next_var <= sc.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x. p.ptr_operand = Var x \/ iop = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l /\ iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32 (type_memory_size etv)
    sgn (compile_imm_load_word F cenv.ce_imm_alloca) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func cenv cx ee s /\
  vv_post ctx func cenv cx obj es sa sc s0 ee r (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
  op_taint tn iop = {} /\ op_prov G iop = NONE /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Ginit tninit s0 G tn /\
  (!q. (!x. not_fresh_at sc x ==> lookup_var x q = lookup_var x s) /\
       q.vs_allocas = s.vs_allocas /\ q.vs_memory = s.vs_memory /\
       stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx obj es sa sd s0 ee r (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_ptr_at D (ctx,func) PG []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s,G,tn)
    (\res ee' Gf tnf q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst LocCode)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
      ghost_inv d cenv cx ee' Gf tnf q /\
      ptr_vv_ok cx (post_value_type cenv (Subscript et obj idx)) child
        (LocatedValue et (mk_ptr dst LocCode)) ee' Gf tnf q /\
      ghost_kept cenv es sa Ginit tninit s0 Gf tnf)
    (\res ee' gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (code_array_suffix_ptr_summary
    |> Q.GEN `es` |> Q.SPEC `es with gas_obs := gs`
    |> SIMP_RULE (srw_ss())
      [expr_body_pre_gas_obs, vv_post_initial_gas, ghost_kept_entry_gas_obs]) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

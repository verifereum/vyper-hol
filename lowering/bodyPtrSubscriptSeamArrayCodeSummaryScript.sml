(* Public semantic/ghost boundary for the runtime code selector. *)
Theory bodyPtrSubscriptSeamArrayCodeSummary
Ancestors
  bodyPtrSubscriptSeamArrayCodePost bodyPtrSubscriptSeamArrayCodeSuffix
  exprSimSubscriptArraySuffix exprSimSubscriptArrayFramed exprSimSubscriptArraySource
  bodyPtrDefs bodyPtrEnvBuiltinsEdges appendStorageGhostPtr
  exprLoweringProps loweringPosts compileEnv ptrDiscipline venomState
  bodyPtrSubscriptReadOnly
  vyperAssignPreservesType valueTypingMemoryProps integer_word vyperArray

Theorem code_array_suffix_ptr_summary:
  expr_body_pre cenv cx env obj es /\ expr_type obj = ArrayT et bd /\
  post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL r,t) /\
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
  `post_value_type cenv obj = ArrayT et bd` by simp[] >>
  drule_all code_array_bound_view >> strip_tac >>
  drule_all array_index_word_bounds >> strip_tac >>
  ` (if (case bd of Fixed _ => F | Dynamic _ => T) then
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))
     else n2w (case bd of Fixed n => n | Dynamic _ => 0)) =
      n2w (array_length (ArrayTV etv bd) av)` by (Cases_on `bd` >> gvs[]) >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  `~idx_in_range sgn iw (if (case bd of Fixed _ => F | Dynamic _ => T) then
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))
     else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by metis_tac[] >>
  drule_all code_selector_counted_oob >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`q`] strip_assume_tac) >>
  irule code_array_rejection_ptr_summary >> goal_assum (drule_at Any) >>
  simp[Excl "valid_index_def"] >>
  metis_tac[]
QED

Resume code_array_suffix_ptr_summary[valid]:
  drule array_index_valid >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `array_index (ArrayTV etv bd) av i = SOME v` >>
  `well_formed_type_value etv` by metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  `value_has_type etv v` by metis_tac[array_index_has_type] >>
  `val_wf etv v` by metis_tac[value_has_type_memory_wf] >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >>
     qpat_x_assum `i = _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `sgn` >> simp[integer_wordTheory.w2i_def] >>
     Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
  `idx_in_range sgn (n2w (Num i))
     (if (case bd of Fixed _ => F | Dynamic _ => T) then
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w))
      else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by metis_tac[] >>
  `eval_operand iop s = SOME (n2w (Num i))` by metis_tac[] >>
  drule_all code_selector_counted_ok >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`q`] strip_assume_tac) >>
  suspend "endpoint"
QED

Resume code_array_suffix_ptr_summary[endpoint]:
  `stmt_state_rel ctx func cenv cx ee q` by metis_tac[] >>
  `vv_post ctx func cenv cx obj es sa sd s0 ee r
      (LocatedValue (ArrayT et bd) p) q` by
    (qpat_x_assum `!q. _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` irule >>
     simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx ee Gf tnf q` by
    (irule ghost_inv_register_transport >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa Ginit tninit s0 Gf tnf` by
    (irule ghost_kept_suffix_compose >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `eval_operand p.ptr_operand q = SOME w` by
    metis_tac[reserved_operand_read_only] >>
  `eval_operand dst q = SOME (w + n2w
      ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv))` by
    (`(if (case bd of Fixed _ => F | Dynamic _ => T) then 32 else 0) =
      (case bd of Fixed _ => 0 | Dynamic _ => 32)` by
       (Cases_on `bd` >> simp[NoAsms]) >> metis_tac[]) >>
  irule code_array_element_ptr_summary >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `i = _` kall_tac >>
  simp[Excl "valid_index_def"] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise code_array_suffix_ptr_summary

(* Each declared literal member accepts the child's actual physical post. *)
Theory bodyPtrPhysicalMemberOutcome
Ancestors
  bodyPtrPhysicalChildStore bodyPtrPhysicalMemberStore
  bodyPtrMakeArrayConsSource bodyPtrMakeArrayConsBind bodyPtrMakeArrayConsInvariant
  bodyPtrDefs exprSimHyps exprSimHypsDefs exprSimProps valueCopyBytes
  memoryLocalRhsProps vyperTypeArgFits valueTypingMemoryProps
  valueEncoding valueEncodingDefs compileEnv context gasSummaryComposePtr
  exprLowering exprLoweringProps emitHelperProps freshWrites loweringPosts
  bodySim exprSimWordArgs wordArgsPtr fragExec fragGasPath fragGasPathPtr
  venomState vyperState eventTopicValueProps list pair option

Theorem literal_flat_member_outcome_ptr_physical[local]:
  body_inv tops ctx ce cx /\
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) dty (lowered_value_type ce e) su = ((),sb) /\
  arg_type_fits (expr_type e) dty /\
  (dty = expr_type e \/ is_bytestring_type dty /\ is_bytestring_type (expr_type e)) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\ evaluate_type (get_tenv cx) dty = SOME tv /\
  k = type_memory_bytes ce dty /\ off+k <= capacity /\
  (pure ==> ~expr_has_effect e) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame pure ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `dty = expr_type e`
  >- (gvs[] >> irule (SRULE [] literal_cons_outcome_ptr_physical) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  fs[] >>
  `~is_word_type dty /\ ~is_word_type (expr_type e)` by
    metis_tac[bytestring_type_not_word] >>
  `compile_store_memory ce op (Var dst) (expr_type e)
    (lowered_value_type ce e) su = ((),sb)` by gvs[compile_store_memory_def] >>
  `type_memory_bytes ce (expr_type e) <= k` by
    metis_tac[arg_type_fits_bytestring_memory_bytes] >>
  drule expr_body_pre_type_evaluates >>
  rewrite_tac[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `stv` assume_tac) >>
  mp_tac (Q.INST [`tv` |-> `stv`, `k` |-> `type_memory_bytes ce (expr_type e)`]
    (SPEC_ALL literal_cons_outcome_ptr_physical)) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  drule gas_outcome_ptr_conseq >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `literal_prefix_ok [(stv,v,_,_)] tm z` >>
  suspend "retag"
QED

Resume literal_flat_member_outcome_ptr_physical[retag]:
  markerLib.RESUME_TAC >>
  `value_has_type tv v` by
    (mp_tac (Q.SPECL [`expr_type e`, `dty`, `stv`, `tv`, `v`]
      (Q.INST [`tenv` |-> `get_tenv cx`] (cj 1 arg_type_fits_value_has_type))) >>
     simp[]) >>
  `val_wf tv v` by
    (irule value_has_type_memory_wf >> simp[]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_size tv = type_memory_bytes ce dty` by
    metis_tac[expr_sim_inv_memory_size] >>
  `val_footprint tv v <= type_memory_bytes ce dty` by
    metis_tac[val_footprint_le] >>
  `literal_prefix_ok cells tm z /\
   (!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
     val_in_memory stv v (addr+off) m)` by
    fs[literal_prefix_cell] >>
  `!m. mem_agree_outside tm.t_mem z.vs_memory m ==>
     val_in_memory tv v (addr+off) m` by
    (rpt strip_tac >> irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl [`expr_type e`, `dty`, `get_tenv cx`, `stv`] >> simp[]) >>
  simp[literal_prefix_cell] >>
  irule literal_loop_frame_retag >> simp[] >>
  qexistsl [`type_memory_bytes ce (expr_type e)`, `stv`] >>
  simp[arithmeticTheory.ADD_COMM]
QED
Finalise literal_flat_member_outcome_ptr_physical


Theorem literal_typed_member_outcome_ptr_physical[local]:
  body_inv tops ctx ce cx /\
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) dty (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\ evaluate_type (get_tenv cx) dty = SOME tv /\
  arg_type_fits (expr_type e) dty /\ ~is_word_type dty /\ ~is_bytestring_type dty /\
  k = type_memory_bytes ce dty /\ off+k <= capacity /\
  (pure ==> ~expr_has_effect e) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame pure ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono si sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code si sm func` by metis_tac[fn_has_code_split, ci_mono_def] >>
  drule literal_loop_frame_runtime >> strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  drule_all post_value_type_widens >> strip_tac >>
  `~is_word_type (expr_type e) ==> ~is_word_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  irule literal_result_bind_outcome_ptr >>
  qexists `\raw ee H tm z.
    vv_post ctx func ce cx e es si sm s0 ee raw vv z /\
    z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d ce cx ee H tm z /\ ptr_vv_ok cx (post_value_type ce e) raw vv ee H tm z /\
    (!t arg. vv = StackValue t arg /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok ce e arg H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    ghost_kept ce es si G0 tn0 s0 H tm` >>
  conj_tac >- suspend "normal" >> suspend "child"
QED

Resume literal_typed_member_outcome_ptr_physical[child]:
  drule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >> disch_then irule >>
  simp[] >> rpt strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >> metis_tac[]
QED

Resume literal_typed_member_outcome_ptr_physical[normal]:
  rpt gen_tac >> strip_tac >> fs[] >>
  `ee with gas_obs := [] = ee` by
    (simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `?atv. evaluate_type (get_tenv cx) (expr_type e) = SOME atv` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  drule literal_marked_child_materialises >> simp[] >>
  disch_then drule_all >> strip_tac >>
  `value_has_type tv v'` by
    (mp_tac (Q.SPECL [`expr_type e`, `dty`, `atv`, `tv`, `v'`]
       (Q.INST [`tenv` |-> `get_tenv cx`] (cj 1 arg_type_fits_value_has_type))) >>
     simp[]) >>
  `val_wf tv v'` by (irule value_has_type_memory_wf >> first_assum ACCEPT_TAC) >>
  qmatch_asmsub_abbrev_tac `eval_expr cx e marked = _` >>
  `literal_loop_frame pure ctx func ce cx d root aid addr capacity
     ees fr sf Gf tnf marked si G0 tn0 s0 cells off` by
    (gvs[Abbr `marked`, literal_loop_frame_def, bodyPtrDefsTheory.ghost_inv_def,
        bodyPtrDefsTheory.ghost_kept_def, exprSimWordArgsTheory.wb_frame_gas_obs] >>
        metis_tac[]) >>
  `ghost_kept ce marked si G0 tn0 s0 G tn` by
    (gvs[Abbr `marked`, bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  `expr_body_pre ce cx env e marked` by simp[Abbr `marked`] >>
  `lookup_var root t = SOME (n2w addr)` by
    (gvs[literal_loop_frame_def, vv_post_def] >> metis_tac[]) >>
  `ptr_covers G tn root t capacity /\ FLOOKUP G root = SOME (addr,capacity)` by
    (gvs[literal_loop_frame_def, bodyPtrDefsTheory.ghost_kept_def,
         bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
     metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal]) >>
  `off+k <= capacity` by decide_tac >>
  drule_at (Pat `eval_expr _ _ _ = _`) literal_cons_typed_member_endpoint_physical >>
  disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >> simp[] >>
  disch_tac >>
  `?z H tm. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 H tm (OK z) /\
     literal_loop_frame pure ctx func ce cx d root aid addr capacity
       ees fr sf Gf tnf ee sb H tm z
         (cells ++ [(tv,v',addr+off,type_memory_bytes ce dty)])
         (off+type_memory_bytes ce dty) /\
     literal_prefix_ok (cells ++ [(tv,v',addr+off,type_memory_bytes ce dty)]) tm z` by
    (qpat_x_assum `!pg dead. ?z H tm. gas_path_ptr dead 0 ctx func pg G tn t 0 H tm (OK z) /\ _`
       (fn th => POP_ASSUM_LIST (K (simp[] >> metis_tac[th])))) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL v'`, `ee`, `H`, `tm`, `OK z`] >> gvs[]
QED
Finalise literal_typed_member_outcome_ptr_physical


Theorem literal_member_outcome_ptr_physical:
  body_inv tops ctx ce cx /\
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) dty (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\ evaluate_type (get_tenv cx) dty = SOME tv /\
  arg_type_fits (expr_type e) dty /\
  k = type_memory_bytes ce dty /\ off+k <= capacity /\
  (pure ==> ~expr_has_effect e) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame pure ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `dty = expr_type e`
  >- (gvs[] >> irule (SRULE [] literal_cons_outcome_ptr_physical) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by simp[vyperTypeSystemTheory.type_widens_to_def, vyperTypeSystemTheory.well_formed_type_def] >>
  `~is_word_type dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  gvs[] >>
  Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type (expr_type e)` by
        metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
      irule (SRULE [] literal_flat_member_outcome_ptr_physical) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule (SRULE [] literal_typed_member_outcome_ptr_physical) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

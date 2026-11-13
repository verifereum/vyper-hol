(* Flat member widening changes the reserved slot, not the bytestring copy. *)
Theory bodyPtrMakeArrayMemberCons
Ancestors
  bodyPtrMakeArrayConsOutcome bodyPtrMakeArrayConsInvariant
  bodyPtrDefs exprSimHyps exprSimHypsDefs exprSimProps valueCopyBytes
  memoryLocalRhsProps vyperTypeArgFits valueTypingMemoryProps
  valueEncoding valueEncodingDefs compileEnv context gasSummaryComposePtr
  eventTopicValueProps list pair

Theorem literal_flat_member_outcome_ptr:
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
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
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
  >- (gvs[] >> irule (SRULE [] literal_cons_outcome_ptr) >>
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
    (SPEC_ALL literal_cons_outcome_ptr)) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  drule gas_outcome_ptr_conseq >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `literal_prefix_ok [(stv,v,_,_)] tm z` >>
  suspend "retag"
QED

Resume literal_flat_member_outcome_ptr[retag]:
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
Finalise literal_flat_member_outcome_ptr

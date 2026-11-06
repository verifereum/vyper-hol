(* Saved operand transport across keyword evaluation. *)
Theory rawCallKeywordPrefixPtr
Ancestors
  rawCallOperandPrefixPtr stmtSimLogArgs bodyPtrDefs loweringPosts

Theorem saved_value_footprint_taint_kept:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn.t_mem ==>
  i IN tn0.t_mem
Proof
  simp[expr_val_at_def] >> strip_tac >>
  first_x_assum (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >> gvs[]
  >- (fs[ghost_kept_def] >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      simp[] >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[])
  >> fs[ghost_kept_def, log_arg_clear_def] >>
  qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
  simp[] >> qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!tv n j k. _` drule_all >> strip_tac >> decide_tac
QED

Theorem saved_value_footprint_clean:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  log_arg_clear cenv cx ty v /\ eval_operand op s = SOME w /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn0.t_mem) ==>
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i NOTIN tn.t_mem
Proof
  metis_tac[saved_value_footprint_taint_kept]
QED

Theorem saved_dynamic_bytes_across_word_args:
  typed_args_post ctx func cenv cx es sb s es' args xs vs t /\
  ghost_kept cenv es sb (G0 : string |-> num # num) tn0 s G tn /\
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sa sb es
    (BytesV bs) (Var x) s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  not_fresh_at sb x /\ eval_operand (Var x) s = SOME (n2w b) /\
  (b:num) < dimword (:256) /\ FLOOKUP G0 x = SOME (region_base,sz) /\
  (region_base:num) <= b /\ b+32+LENGTH bs <= region_base+(sz:num) /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn0.t_mem) ==>
  eval_operand (Var x) t = SOME (n2w b) /\
  FLOOKUP G x = SOME (region_base,sz) /\ op_taint tn (Var x) = op_taint tn0 (Var x) /\
  mem_bytes_at b (32+LENGTH bs) t.vs_memory =
    mem_bytes_at b (32+LENGTH bs) s.vs_memory /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `wb_frame cenv es sb s t` by
    fs[exprSimPrecompilesTheory.typed_args_post_def] >>
  `log_arg_clear cenv cx (BaseT (BytesT (Dynamic n))) (BytesV bs)` by
    metis_tac[log_arg_clear_base] >>
  conj_tac >- (irule log_frame_operand >> simp[] >> metis_tac[]) >>
  `FLOOKUP G x = FLOOKUP G0 x /\
   op_taint tn (Var x) = op_taint tn0 (Var x)` by fs[ghost_kept_def] >>
  simp[] >> conj_tac
  >- (`~is_word_type (BaseT (BytesT (Dynamic n)))` by
        simp[compileEnvTheory.is_word_type_def] >>
      drule_all log_argument_footprint_kept >>
      simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
        wordsTheory.w2n_n2w]) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `i IN tn0.t_mem` suffices_by (gvs[] >> metis_tac[]) >>
  irule saved_value_footprint_taint_kept >>
  first_assum (irule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`n2w b`, `BaseTV (BytesT (Dynamic n))`, `tn`, `G0`, `G`] >>
  simp[compileEnvTheory.is_word_type_def, loweringPostsTheory.val_footprint_def,
    wordsTheory.w2n_n2w]
QED

Theorem raw_call_word_args_ready_ptr:
  !args.
    body_exprs_ptr_ok cx args /\ body_inv tops ctx cenv cx /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) args /\
    (!e es. MEM e args /\ expr_sim_inv cenv cx env es ==>
       expr_body_pre cenv cx env e es) ==>
    typed_args_ready_ptr dep ctx PG func cenv cx (K (BaseT (UintT 256)))
      (expr_sim_inv cenv cx env) args
Proof
  Induct >> simp[typedOperandsPtrTheory.typed_args_ready_ptr_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env h es` by metis_tac[] >>
      `body_expr_ptr_ok cx h` by fs[bodyPtrPredsTheory.body_exprs_ptr_ok_def] >>
      fs[bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
      simp[compileEnvTheory.is_word_type_def] >> rpt conj_tac
      >- metis_tac[]
      >- metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates,
                   optionTheory.IS_SOME_DEF]
      >- metis_tac[exprSimHashTheory.expr_body_pre_base_result]
      >> metis_tac[exprSimHashTheory.expr_body_pre_base_result]) >>
  strip_tac >> first_x_assum irule >>
  fs[bodyPtrPredsTheory.body_exprs_ptr_ok_def] >> metis_tac[]
QED

Theorem typed_args_ready_ptr_inv:
  !args es vs es'.
    typed_args_ready_ptr dep ctx PG func cenv cx arg_ty Inv args /\ Inv es /\
    eval_exprs cx args es = (INL vs,es') ==>
    Inv es'
Proof
  Induct >> simp[exprSimWordArgsTheory.eval_exprs_nil] >>
  rpt gen_tac >> strip_tac >>
  gvs[exprSimWordArgsTheory.eval_exprs_cons_action, vyperStateTheory.bind_def,
    vyperStateTheory.return_def, AllCaseEqs()] >>
  drule_all typedOperandsPtrTheory.typed_args_ready_ptr_head >> strip_tac >>
  qpat_x_assum `!es vs es'. _` irule >>
  reverse conj_tac
  >- (fs[typedOperandsPtrTheory.typed_args_ready_ptr_def] >> metis_tac[]) >>
  goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[vyperStateTheory.bind_def] >> metis_tac[]
QED

Theorem gas_outcome_ptr_nonhalted:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\ ~t.vs_halted) R
Proof
  simp[fragGasPathPtrTheory.gas_outcome_ptr_def,
    fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]
QED

Theorem typed_args_outcome_inv_ptr:
  typed_args_ready_ptr dep ctx PG func cenv cx arg_ty Inv args /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  gas_outcome_ptr D tops (ctx,func) PG (eval_exprs cx args) (es,s0,G0,tn0) Q R /\
  (!rr ee G tn t. Q rr ee G tn t ==> ?vs. rr = INL vs) ==>
  gas_outcome_ptr D tops (ctx,func) PG (eval_exprs cx args) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\ Inv ee /\ ~t.vs_halted) R
Proof
  strip_tac >> drule gas_outcome_ptr_nonhalted >> strip_tac >>
  irule operandOutcomePtrTheory.gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?vs. res = INL vs` by metis_tac[] >> gvs[] >>
  irule typed_args_ready_ptr_inv >>
  first_assum (irule_at (Pat `typed_args_ready_ptr _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`vs`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
  conj_tac >- metis_tac[] >>
  fs[gasSummaryTheory.gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[combinTheory.o_DEF]
QED

Theorem raw_call_kwargs_execution_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx kws /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es0 /\
  expr_sim_inv cenv cx env es /\ raw_call_kws_ok flags kws /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sa = ((vo,go,ig),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv dep cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx kws) (es,s0,G0,tn0)
    (\rr ee G tn t. ?vs xs. rr = INL vs /\
      typed_args_post ctx func cenv cx es sa s0 ee kws xs vs t /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ig = NONE /\
      EVERY (\x. op_taint tn x = {}) xs /\
      EVERY (\x. !v. x = Var v ==> not_fresh_at sb v) xs /\
      stmt_state_rel ctx func cenv cx ee t /\ expr_sim_inv cenv cx env ee /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      ghost_inv dep cenv cx ee G tn t /\
      wb_frame cenv es sa s0 t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
      sa.cs_next_id <= sb.cs_next_id)
    (\rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by
    (fs[vyperTypeSystemTheory.raw_call_kws_ok_def] >>
     metis_tac[listTheory.LENGTH_MAP]) >>
  drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >> strip_tac >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, compileEnvTheory.is_word_type_def]) >>
  `typed_args_ready_ptr dep ctx PG func cenv cx (K (BaseT (UintT 256)))
     (expr_sim_inv cenv cx env) kws` by
    (irule raw_call_word_args_ready_ptr >> simp[] >> metis_tac[]) >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule exprSimPrecompilesTheory.typed_stack_args_shape >> metis_tac[]) >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
     expr_sim_inv cenv cx env (ee with gas_obs := gs)` by simp[] >>
  drule_all typedOperandsPtrTheory.lower_typed_args_sim_ptr >> strip_tac >>
  suspend "posts"
QED

Resume raw_call_kwargs_execution_ptr[posts]:
  `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx kws) (es,s0,G0,tn0)
    (\rr ee G tn t. (?vs. rr = INL vs /\
      typed_args_post ctx func cenv cx es sa s0 ee kws xs vs t /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv dep cenv cx ee G tn t /\ EVERY (\x. op_taint tn x = {}) xs /\
      ghost_kept cenv es sa G0 tn0 s0 G tn) /\
      expr_sim_inv cenv cx env ee /\ ~t.vs_halted)
    (\rr ee gt r. wb_args_exit rr r)` by
    (ho_match_mp_tac (Q.INST [`arg_ty` |-> `K (BaseT (UintT 256))`] typed_args_outcome_inv_ptr) >>
     first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  qexistsl_tac [`vs`, `xs`] >>
  fs[exprSimPrecompilesTheory.typed_args_post_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  qpat_x_assum `!x. MEM x xs ==> (_ /\ _)` drule >> simp[]
QED

Finalise raw_call_kwargs_execution_ptr

Theorem raw_call_kwargs_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx kws /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es0 /\
  expr_sim_inv cenv cx env es /\ raw_call_kws_ok flags kws /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sa = ((vo,go,ig),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv dep cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sd sa es
    (BytesV bs) (Var x) s0 /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  not_fresh_at sa x /\ eval_operand (Var x) s0 = SOME (n2w b) /\
  (b:num) < dimword (:256) /\ FLOOKUP G0 x = SOME (region_base,sz) /\
  (region_base:num) <= b /\ b+32+LENGTH bs <= region_base+(sz:num) /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn0.t_mem) /\
  (!op. MEM op saved ==> (!z. op = Var z ==> not_fresh_at sa z) /\
    (!l. op <> Label l)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx kws) (es,s0,G0,tn0)
    (\rr ee G tn t. ?vs xs. rr = INL vs /\
      typed_args_post ctx func cenv cx es sa s0 ee kws xs vs t /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ig = NONE /\
      EVERY (\op. op_taint tn op = {}) xs /\
      EVERY (\op. !z. op = Var z ==> not_fresh_at sb z) xs /\
      stmt_state_rel ctx func cenv cx ee t /\ expr_sim_inv cenv cx env ee /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      ghost_inv dep cenv cx ee G tn t /\
      wb_frame cenv es sa s0 t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
      expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sd sb ee
        (BytesV bs) (Var x) t /\
      eval_operand (Var x) t = SOME (n2w b) /\
      FLOOKUP G x = SOME (region_base,sz) /\
      op_taint tn (Var x) = op_taint tn0 (Var x) /\
      mem_bytes_at b (32+LENGTH bs) t.vs_memory =
        mem_bytes_at b (32+LENGTH bs) s0.vs_memory /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      (!op. MEM op saved ==> op_prov G op = op_prov G0 op /\
        op_taint tn op = op_taint tn0 op /\
        (!w. eval_operand op s0 = SOME w ==> eval_operand op t = SOME w)))
    (\rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all raw_call_kwargs_execution_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  drule_all saved_dynamic_bytes_across_word_args >> strip_tac >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sd sb ee
     (BytesV bs) (Var x) t` by
    (irule log_frame_placement >> simp[] >> goal_assum (drule_at Any) >>
     simp[] >> fs[exprSimPrecompilesTheory.typed_args_post_def] >> metis_tac[]) >>
  qexistsl_tac [`vs`, `xs`] >> simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  gen_tac >> strip_tac >>
  `(!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l)` by metis_tac[] >>
  conj_tac
  >- (Cases_on `op` >>
      fs[ptrDisciplineTheory.op_prov_def, bodyPtrDefsTheory.ghost_kept_def]) >>
  conj_tac
  >- (Cases_on `op` >>
      fs[ptrDisciplineTheory.op_taint_def, bodyPtrDefsTheory.ghost_kept_def]) >>
  rpt strip_tac >> irule log_frame_operand >> simp[] >> metis_tac[]
QED

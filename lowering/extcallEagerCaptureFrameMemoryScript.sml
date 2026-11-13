(* Captured values survive later effect-free operands without another read. *)
Theory extcallEagerCaptureFrameMemory
Ancestors
  extcallCaptureValueMemory extcallCaptureMemory exprSimIfExpWidenedAdapter
  noEffectSourceFrame exprSafeOperand exprBopSimProps
  exprSimMemDefs exprSimProps exprSimConvert loweringPosts exprLowering exprLoweringProps compileEnv context
  vyperInterpreter vyperState venomState loweringStateRelDefs

Theorem eager_captured_value_frame:
  vv_holds ce cx ty (Value v) vv es s /\
  vv_at ce cx ty ca cb es (Value v) vv s /\
  vv_store_bound cx ty ty es (Value v) vv s /\ vv_storage_live cx vv es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (is_word_type ty ==> ?tag op. vv = StackValue tag op) /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr. get_storage cx ee tr = get_storage cx es tr) /\
  stmt_state_rel ctx func ce cx ee t /\
  pure_frame ce func es st s t /\ cb.cs_next_id <= st.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!name b sz. local_region ce es.scopes t name b sz <=>
    local_region ce es.scopes s name b sz) ==>
  vv_holds ce cx ty (Value v) vv ee t /\
  vv_at ce cx ty ca cb ee (Value v) vv t /\
  vv_store_bound cx ty ty ee (Value v) vv t /\ vv_storage_live cx vv ee t
Proof
  strip_tac >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  conj_tac
  >- (Cases_on `is_word_type ty`
      >- (`?tag op. vv = StackValue tag op` by metis_tac[] >>
          gvs[vv_holds_def,expr_val_rel_def,vv_operand_def,
              read_result_def,return_def] >> metis_tac[]) >>
      Cases_on `vv`
      >- (rename1 `StackValue tag op` >>
          `?w. eval_operand op s = SOME w` by fs[vv_holds_def,expr_val_rel_def] >>
          irule extcall_captured_nonword_stack_holds_frame >>
          goal_assum (drule_at Any) >> fs[vv_operand_def] >>
          metis_tac[]) >>
      rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location`
      >- (`?w. eval_operand p.ptr_operand s = SOME w` by fs[vv_holds_def] >>
          irule extcall_captured_nonword_memory_holds_frame >>
          goal_assum (drule_at Any) >> fs[vv_operand_def] >> metis_tac[])
      >- (gvs[vv_holds_def,vv_operand_def] >>
          rename1 `storage_holds cx F ty (Value v) w es s` >>
          mp_tac (Q.INST [`tr` |-> `F`]
            (SPEC_ALL extcall_captured_storage_holds_refresh)) >>
          (impl_tac >- (simp[] >> metis_tac[])) >> simp[])
      >- (gvs[vv_holds_def,vv_operand_def] >>
          rename1 `storage_holds cx T ty (Value v) w es s` >>
          mp_tac (Q.INST [`tr` |-> `T`]
            (SPEC_ALL extcall_captured_storage_holds_refresh)) >>
          (impl_tac >- (simp[] >> metis_tac[])) >> simp[])
      >- (gvs[vv_holds_def,vv_operand_def,immutable_holds_def,
              read_result_def,return_def] >> metis_tac[]) >>
      fs[vv_holds_def]) >>
  conj_tac
  >- (`vv_at ce cx ty ca cb es (Value v) vv t` by
        (irule vv_at_alloc_mono_frame >> qexistsl_tac [`s`,`cb`] >> simp[]) >>
      Cases_on `vv` >>
      gvs[vv_at_def,expr_val_at_def,read_result_def,return_def]) >>
  conj_tac
  >- (irule extcall_vv_bound_read_transport >> goal_assum (drule_at Any) >>
      simp[read_result_def,return_def] >> qexists_tac `es` >> simp[]) >>
  Cases_on `vv` >> fs[vv_operand_def] >> metis_tac[]
QED

Theorem eager_captured_expr_frame:
  ~expr_has_effect e /\ eval_expr cx e es = (INL raw,ee) /\
  vv_post ctx func ce cx e es st sn s ee raw out t /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  cb.cs_next_id <= st.cs_next_id /\ s.vs_alloca_next <= t.vs_alloca_next /\
  vv_holds ce cx ty (Value v) saved es s /\
  vv_at ce cx ty ca cb es (Value v) saved s /\
  vv_store_bound cx ty ty es (Value v) saved s /\
  vv_storage_live cx saved es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (is_word_type ty ==> ?tag op. saved = StackValue tag op) /\
  safe_operand st (vv_operand saved) /\
  IS_SOME (eval_operand (vv_operand saved) s) ==>
  vv_holds ce cx ty (Value v) saved ee t /\
  vv_at ce cx ty ca cb ee (Value v) saved t /\
  vv_store_bound cx ty ty ee (Value v) saved t /\
  vv_storage_live cx saved ee t
Proof
  strip_tac >> drule_all no_effect_eval_expr_frame >> strip_tac >>
  `local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w` by fs[vv_post_def] >>
  `eval_operand (vv_operand saved) t = eval_operand (vv_operand saved) s` by
    (fs[optionTheory.IS_SOME_EXISTS,safe_operand_def] >>
     drule_all eval_operand_frame >> simp[]) >>
  `!name b sz. local_region ce es.scopes t name b sz <=>
     local_region ce es.scopes s name b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac >>
     metis_tac[local_region_frame,local_region_frame_fwd]) >>
  mp_tac (Q.INST [`vv` |-> `saved`] (SPEC_ALL eager_captured_value_frame)) >>
  (impl_tac >- (fs[vv_post_def] >> metis_tac[])) >> simp[]
QED

Theorem eager_word_snapshot_unwrap:
  is_word_type ty /\ vv_holds ce cx ty (Value v) vv es s /\
  compile_snapshot_vv ce F (ext_call_arg_value ty vv) sa = (saved,sb) ==>
  ?tag op. saved = StackValue tag op /\ unwrap_value ce vv sa = (op,sb)
Proof
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue tag src` >> Cases_on `is_word_type tag` >>
      gvs[compile_snapshot_vv_def,ext_call_arg_value_def,vv_type_def,
          unwrap_value_def,comp_bind_def,comp_return_def]) >>
  rename1 `LocatedValue tag p` >>
  `tag = ty` by
    (fs[vv_holds_def] >> metis_tac[is_word_type_not_bytestring]) >> gvs[] >>
  gvs[compile_snapshot_vv_def,ext_call_arg_value_def,vv_type_def,
      comp_bind_def,comp_return_def] >>
  pairarg_tac >> gvs[]
QED

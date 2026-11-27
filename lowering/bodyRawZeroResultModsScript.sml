(* Zero-capacity raw requests have a scalar result. The already fetched
   call's success bit and ghost witness are used by the actual finish code. *)
Theory bodyRawZeroResultMods
Ancestors
  bodyFullRawCallZero bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  allocaHistory bodyFullHashKeccakFixed exprLoweringProps
  loweringPosts loweringStateRelDefs exprSimRawCall bodyPtrDefs
  exprSimDefs exprSimMemDefs exprSimProps vyperTypeSystem vyperValue vyperState valueEncoding
  compileEnv context fragGasOriginPtr ptrDiscipline venomState

Theorem raw_zero_jump_frames[local]:
  (wb_frame cenv es ee sa s0 (jump_to lbl s) <=> wb_frame cenv es ee sa s0 s) /\
  (immutable_frame_mods func cenv cx ee (jump_to lbl s) <=>
   immutable_frame_mods func cenv cx ee s) /\
  (allocas_below_fmp (jump_to lbl s) <=> allocas_below_fmp s) /\
  (ghost_inv_at_mods D lo d cenv cx ee G tn (jump_to lbl s) <=>
   ghost_inv_at_mods D lo d cenv cx ee G tn s)
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def,
       immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def, local_region_def,
       ghost_inv_at_mods_def, ptr_covers_def, stor_taint_ok_at_def,
       allocas_from_def, allocas_below_fmp_def, jump_to_def, lookup_var_def] >>
  Cases_on `d` >> simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem raw_zero_stack_post[local]:
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = (if rev then NoneT else BaseT BoolT) /\
  (rev ==> result = Lit 0w) /\
  eval_operand result t = SOME (if rev then 0w else if success then 1w else 0w) /\
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sf s0 t ==>
  vv_post_mods H ctx func cenv cx e es sf sb s0 ee
    (Value (if rev then NoneV else BoolV success)) (StackValue ann result) t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ee (Value (if rev then NoneV else BoolV success)) (StackValue ann result) t /\
  vv_own cenv cx (post_value_type cenv e) sf sb ee
    (Value (if rev then NoneV else BoolV success)) (StackValue ann result) t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e result G t)
Proof
  strip_tac >>
  `vv_post H ctx func cenv cx e es sf sb s0 ee
     (Value (if rev then NoneV else BoolV success)) (StackValue ann result) t` by
    (Cases_on `rev` >> gvs[]
     >- (irule raw_call_none_post >> simp[]) >>
     irule raw_call_bool_post >>
     simp[expr_val_rel_def, is_word_type_def, evaluate_type_def,
          typed_val_to_w256_def, val_to_w256_def]) >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
           vv_place_ptr_mods_def, vv_place_ptr_def, AC CONJ_ASSOC CONJ_COMM] >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `rev` >>
  gvs[vv_store_bound_def, is_word_type_def, evaluate_type_def,
      read_result_def, return_def, val_store_size_def, val_footprint_def,
      type_memory_size_def, ptr_buf_ok_def, type_memory_bytes_def,
      vv_own_def, expr_val_own_def]
QED

(* [s,G,tn] is the actual fetched CALL endpoint. No new provenance or
   taint state is selected: the non-reverting finish is empty, and the
   successful reverting finish only moves the cursor to the good block. *)
Theorem raw_zero_result_path_mods:
  flags.rcf_max_outsize = 0 /\
  compile_raw_call_finish to_op dp dl gas_op val_op call_ty 0
    flags.rcf_revert_on_failure ov op sa = (result,sb) /\
  (case call_ty of
    RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit 0w]
  | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit 0w]
  | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit 0w]) sa = (ok,sc) /\
  (flags.rcf_revert_on_failure ==> success) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ op_prov G ok = NONE /\ fn_has_code sc sb func /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ wb_frame cenv es ee sf s0 s /\
  ghost_kept_at lo cenv es sf G0 tn0 s0 G tn /\ expr_has_effect e /\
  post_value_type cenv e = expr_type e /\ lowered_value_type cenv e = expr_type e /\
  expr_type e = raw_call_return_type flags /\
  res = INL (Value (if flags.rcf_revert_on_failure then NoneV else BoolV success)) ==>
  ?t. (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK t,G,tn)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      ghost_kept_at lo cenv es sf G0 tn0 s0 G tn /\
      (!H D. stmt_state_rel H ctx func cenv cx ee s /\
             immutable_frame_mods func cenv cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at_mods D lo d cenv cx ee G tn s ==>
        ?tv. res = INL tv /\
          vv_post_mods H ctx func cenv cx e es sf sb s0 ee tv
            (StackValue (raw_call_return_type flags) result) t /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
            ee tv (StackValue (raw_call_return_type flags) result) t /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at_mods D lo d cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv e) tv
            (StackValue (raw_call_return_type flags) result) ee G tn t /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sf sb ee tv
                 (StackValue (raw_call_return_type flags) result) t) /\
          (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e result G t))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `rev = flags.rcf_revert_on_failure` >>
  qabbrev_tac `t = if rev then jump_to sb.cs_current_bb s else s` >>
  `t = if rev then jump_to sb.cs_current_bb s else s` by simp[Abbr `t`] >>
  drule_all raw_call_zero_normal_suffix_joint >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [FORALL_AND_THM]) >>
  qpat_x_assum `t = if rev then _ else _` kall_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by (Cases_on `rev` >> simp[Abbr `t`,jump_to_def]) >>
  `alloca_history func t` by
    (Cases_on `rev` >> simp[Abbr `t`] >> irule alloca_history_jump >>
     simp[jump_to_def] >> qexists_tac `s` >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     Cases_on `rev` >> simp[NoAsms,Abbr `t`,raw_zero_jump_frames]) >>
  `rev ==> result = Lit 0w` by simp[] >>
  qpat_x_assum `result = if rev then _ else _` kall_tac >>
  qexists_tac `t` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_type e = if rev then NoneT else BaseT BoolT` by
    simp[Abbr `rev`,raw_call_return_type_def] >>
  `wb_frame cenv es ee sf s0 t /\ stmt_state_rel H ctx func cenv cx ee t /\
   immutable_frame_mods func cenv cx ee t /\ ghost_inv_at_mods D lo d cenv cx ee G tn t` by
    (Cases_on `rev` >> simp[Abbr `t`, raw_zero_jump_frames, stmt_state_rel_jump_to]) >>
  drule_all raw_zero_stack_post >>
  disch_then (qspecl_then [`sb`, `raw_call_return_type flags`, `G`] strip_assume_tac) >>
  `post_value_type cenv e = if rev then NoneT else BaseT BoolT` by
    simp[Abbr `rev`,raw_call_return_type_def] >>
  `ptr_vv_ok cx (post_value_type cenv e) (Value (if rev then NoneV else BoolV success))
     (StackValue (raw_call_return_type flags) result) ee G tn t` by
    (qpat_assum `post_value_type cenv e = if rev then _ else _`
       (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
     first_assum irule) >>
  gvs[]
QED

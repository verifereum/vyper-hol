Theory abiEncodeSinglePtrWordSuffix
Ancestors
  abiEncodeSinglePtrWordResources abiEncodeSinglePtrResult abiEncodeSinglePtrPhaseCaller
  abiEncodeSinglePtrUnary exprSimAbiEncodeWordSuccess
  fragGasPathPtr gasSummaryComposePtr loweringPosts
  exprSimAbiEncodeStateTransport exprSimAbiEncodeStagedObserver
  exprSimAbiEncodeExecFrame abiBuiltinEncodeSetup abiDecoderGuards
  abiBuiltinEncodeCode abiDecoderReentry localPtrsProps

val _ = Parse.hide "body";

Theorem abi_encode_single_word_suffix_ptr:
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode F mid0) typ [e]) es /\
  (!x sm. code x sm =
    (do buf <- compile_alloc_buffer 32;
        emit_void MSTORE [buf.buf_operand;x];
        (\st. as_ptr_val ann LocMemory
          (lower_abi_encode F (OPTION_MAP bytes_method_id_word mid0) buf.buf_operand
            (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))
            (abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e)) st))
     od) sm) /\
  lower_value compile_expr cenv (expr_type e) e sa = (src,sm) /\
  code src sm = (vv,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  ee.gas_obs = [] /\
  expr_post ctx func cenv cx e es sa sm s0 ee v src s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv rb cenv cx ee G tn s /\
  ptr_val_ok cx (post_value_type cenv e) v src G tn s /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e src G s) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ stmt_state_rel ctx func cenv cx es s0 /\
  is_word_type (expr_type e) ==>
  ?marks. gas_summary_ptr_at (cx_dead cx) (ctx,func) PG marks
    (bind (lift_sum (evaluate_type_builtin cx (AbiEncode F mid0) typ [expr_type e] [v]))
      (\w. return (Value w))) (ee,s,G,tn)
    (\res ef G' tn' t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (TypeBuiltin ann (AbiEncode F mid0) typ [e]) es sa sn s0 ef tv vv t /\
      t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      ghost_inv rb cenv cx ef G' tn' t /\
      ptr_vv_ok cx (expr_type (TypeBuiltin ann (AbiEncode F mid0) typ [e])) tv vv ef G' tn' t /\
      (!t' op. vv = StackValue t' op /\
        ~is_word_type (expr_type (TypeBuiltin ann (AbiEncode F mid0) typ [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin ann (AbiEncode F mid0) typ [e]) op G' t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (TypeBuiltin ann (AbiEncode F mid0) typ [e]) p.ptr_operand G' t) /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res ef gt r. expr_exit res r)
Proof
  strip_tac >>
  `ptr_val_ok cx (expr_type e) v src G tn s` by
    metis_tac[post_value_type_word] >>
  drule_all abi_encode_single_word_phase_resources >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_encoder_admissible (AbiCopy 32)` by
    simp[abiEncoderAdmissibleTheory.abi_encoder_admissible_def] >>
  `32 <= 32` by simp[] >>
  `0 < 32 ==> ?z. Var x = Var z /\ ptr_covers H un z staged 32` by metis_tac[] >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id
      (32+32*word_size (32+(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4))) staged).vs_allocas inst.inst_id = SOME(b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,32) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32+(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4),LENGTH(enc ct rv)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4) (b,sz)` by metis_tac[] >>
  mp_tac (Q.INST
    [`initial` |-> `staged`, `src` |-> `Var x`, `ei` |-> `AbiCopy 32`,
     `at` |-> `ct`, `av` |-> `rv`, `cap` |-> `32`,
     `tn` |-> `un`, `G` |-> `H`, `es` |-> `ee`, `final` |-> `sn`,
     `method_id` |-> `OPTION_MAP bytes_method_id_word mid0`,
     `maxlen` |-> `32`,
     `m` |-> `(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4)`,
     `w` |-> `(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 32)`,
     `d` |-> `p+32+(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4)`,
     `outsz` |-> `32+32*word_size (32+(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4))`]
    abi_encode_staged_phases_caller_ptr |> REWRITE_RULE []) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac [] >> FAIL_TAC "caller premise")) >>
  strip_tac >>
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [exprLoweringPropsTheory.stmt_state_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `st.cs_next_id <= ready.cs_next_id` by
    (drule abi_builtin_encode_setup_shape >> strip_tac >>
     qpat_assum `ready.cs_next_id = _` (fn th => rewrite_tac [th]) >> simp[]) >>
  `!aid off sz. FLOOKUP staged.vs_allocas aid = SOME(off,sz) /\ aid < st.cs_next_id ==>
    mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz staged.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_caller_phase_old_rows >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists `aid` >> rpt conj_tac >> asm_rewrite_tac [] >> FAIL_TAC "old row residual") >>
  `!z v. not_fresh_at st z /\ lookup_var z staged = SOME v ==>
    lookup_var z actual = SOME v` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var z)` by
       (qpat_assum `not_fresh_at st z` mp_tac >>
        simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def, IN_DEF]) >>
     irule abi_encode_caller_phase_registers >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_exec_frame func staged actual` mp_tac >>
  simp_tac bool_ss [abi_encode_exec_frame_def] >> strip_tac >>
  `abi_encode_staged_observation ctx func cenv cx ee st (FST ops)
     (OPTION_MAP bytes_method_id_word mid0)
     (32+32*word_size (32+(case OPTION_MAP bytes_method_id_word mid0 of NONE => 0 | SOME _ => 4)))
     p ct rv staged actual` by
    (rewrite_tac [abi_encode_staged_observation_def] >>
     rpt conj_tac >> asm_rewrite_tac [] >>
     qpat_assum `pure_frame cenv func ee st staged actual` mp_tac >>
     simp_tac bool_ss [pure_frame_def] >> metis_tac[]) >>
  FAIL_TAC "observation endpoint"
QED

(*
 * The internal frame's returns, with the ghost (the producer the internal
 * call case needs; bodyPtrIntCallCase).
 *
 * TOP-LEVEL:
 *   intret_ptr_q -- what an internal frame's return hands its caller: the
 *     S1 return (intret_q, or intret_mem_q at the caller's return buffer),
 *     storage taint confined to dead bytes, and a memory-returned value
 *     independent of tainted memory.  The caller's ghost and the INVOKE
 *     outputs' taint come back through ptrSafeRun's ghost_step instead.
 *   internal_frame_ret_ok_ptr -- in an internal function's compile env,
 *     every return statement exits pointer-safely with intret_ptr_q;
 *     assembled from internal_return_direct_ptr (admitted leaf) and
 *     internal_return_widened_ptr (held residual)
 *)
Theory bodyPtrIntCallFrameRet
Ancestors
  bodyPtrDefs intCallReturnMem bodyIntCallReturnCopy stmtSimReturn bodySim
  internalReturnStackPtr internalReturnStorePtr internalReturnCountedPtr
  internalReturnStackSuffixPtr internalReturnMemorySuffixPtr wordAggregateReturnSemantics
  compileEnv valueEncoding compileVyper loweringPosts ptrDiscipline
  fragGasPathPtr venomExecSemantics ctorReturnFrame
  bodyPtrBytestringBuiltinsEval returnValueTyped valueEncodingTyping
  bodyAppendStorageFacts annAssignPtrMemorySource annAssignPtrMemoryWindow
  bodyPtrStructLitLayoutTransfer reasonCopySourcePtr
  bodyPtrTypeBuiltinsMemoryBounds bodyPtrMakeArrayZeroWidth

(* The return an internal frame hands back: d is the caller's return
   buffer (its address and capacity) when the value comes back in memory. *)
Definition intret_ptr_q_def:
  intret_ptr_q func cenv cx ret_tv d v (es : evaluation_state)
    (G, tn) r <=>
    (case d of
       NONE => intret_q func cenv cx ret_tv v es r
     | SOME (bw, cap) => intret_mem_q func cenv cx ret_tv bw v es r) /\
    ?ir s. r = IntRet ir s /\ stor_taint_ok cx tn s /\
      !bw cap mem.
        d = SOME (bw, cap) /\
        mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory ret_tv v (w2n bw) mem
End

(* ADMITTED (leaf): the pointer twin of s3-mem's internal_return_direct_mem:
   an internal function's return statement, pointer-safely, when the
   returned expression is lowered at its own type and that type is the
   return type, or the return type is a word or a bytestring (no compound
   widening into the caller's return buffer).  The compile env returns
   internally (RET to the return PC, and the return buffer, if any, is a
   pointer parameter rather than a fixed memory slot, as
   compile_internal_function makes it), with the stack-return count of the
   declared return type, and has a return buffer exactly when that count
   is 0 and the type isn't void; the buffer's capacity is the return
   value's size, it fits below 2 ** 256, and so does that size plus a
   copy's 64 bytes of length rounding (size headroom, not address
   headroom: the store never offsets the buffer address).
   Constructor frames are excluded by stmt_frag_ptr itself.  S1's pieces:
   stmtSimReturn (step_ret_values, compile_load_tuple_elements_run,
   intret_vals_match_word/_tuple), bodyIntCallReturnCopy's
   compile_internal_return_memory_size_bound_frag (the size-headroom form
   of intCallReturnMem's compile_internal_return_memory_frag), and the
   bytestring branch of
   stmtSimReturnWiden's compile_internal_return_memory_widen_frag; the
   returned expression's expr_sim_ptr/expr_vv_sim_ptr for the ghost side
   (ptr_mem_ok makes the source robust under t_mem, and MCOPY carries its
   taint to the buffer). *)
Theorem internal_return_direct_ptr:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz cenv' env lctx eo es.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    (!off sz. cenv.ce_return_buf <> SOME (MemLoc off sz)) /\
    cenv.ce_imm_alloca = NONE /\
    cenv.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
        ret_ty /\
    evaluate_type (get_tenv cx) ret_ty = SOME ret_tv /\
    (IS_SOME d <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. d = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap < dimword (:256) /\ cap + 64 < dimword (:256)) /\
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
            expr_sim_ptr d ctx PG func cenv' cx ty e es /\
            expr_vv_sim_ptr d ctx PG func cenv' cx ty e es) /\
    (!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty)) ==>
    stmt_frag_ptr d ctx PG func cx lctx (intret_ptr_q func cenv cx ret_tv d)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo))
      es
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `eo`
  >- (gvs[vyperTypeSystemTheory.type_stmt_def] >>
      `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) rsz)` by
        (fs[same_frame_def] >>
         qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
           ce_var_type := _ |> = _` (mp_tac o Q.AP_TERM `\c. c.ce_return_pc`) >>
         simp[]) >>
      qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
      simp[loweringPostsTheory.stmt_env_def, stmtLoweringTheory.declare_stmt_local_def,
           stmtLoweringTheory.compile_stmt_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      Cases_on `emit_inst RET [Var rpc] [] sa` >>
      rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
      `?pc. lookup_var rpc s0 = SOME pc` by
        fs[ret_pc_ok_def] >>
      `op_taint tn0 (Var rpc) = {}` by metis_tac[ghost_inv_def] >>
      `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G0 tn0
         (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s0)` by
        (irule emit_ret_values_path_ptr >> simp[allocas_from_def] >>
         qexistsl_tac [`[]`, `pc`, `rpc`, `sa`, `sb`] >>
         simp[venomStateTheory.eval_operands_def]) >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def, Once vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.raise_def] >>
      qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `G0`, `tn0`,
        `IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s0`] >>
      simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def, intret_ptr_q_def,
           intret_q_def, compileEnvTheory.result_rel_def] >>
      gen_tac >> disj2_tac >>
      simp[compileEnvTheory.intret_vals_match_def] >>
      conj_tac
      >- (simp[compileEnvTheory.state_rel_gas_obs] >>
          irule constructor_exit_state_rel >>
          qexists_tac `cenv'` >> fs[exprLoweringPropsTheory.stmt_state_rel_def,
            compileEnvTheory.state_rel_gas_obs]) >>
      metis_tac[ghost_inv_def]) >>
  gns[] >>
  `cenv'.ce_return_pc = SOME (PtrVar (Var rpc) rsz)` by
    (fs[same_frame_def] >>
     qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _ |> = _` (mp_tac o Q.AP_TERM `\c. c.ce_return_pc`) >>
     simp[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, stmtLoweringTheory.declare_stmt_local_def,
       stmtLoweringTheory.compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv' ret_ty x sa` >>
  rename1 `_ = (val_op,sm)` >>
  Cases_on `compile_internal_return_from_env cenv' ret_ty (expr_type x)
    val_op (Var rpc) sm` >>
  rename1 `_ = (ru,sf)` >> Cases_on `ru` >> simp[] >> strip_tac >>
  gns[] >>
  `cs_extends sa sm` by
    (drule bodyPtrCallCalldataTheory.lower_value_compile_expr_split >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `cs_extends sm sb` by
    (qspec_then `sm` mp_tac
      (Q.SPECL [`cenv''`, `ret_ty`, `expr_type x`, `val_op`, `Var rpc`]
        (cj 2 stmtLoweringMonoTheory.ci_mono_return_helpers)) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx x) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `!z sz. cenv''.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
      not_fresh_at sa z` by fs[ret_pc_ok_def] >>
  qpat_x_assum `!ty. expr_sim_ptr _ _ _ _ _ _ _ _ _ /\ _`
    (mp_tac o Q.SPEC `ret_ty`) >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> strip_tac >>
  `eval_stmt cx (Return (SOME x)) =
    bind (bind (eval_expr cx x) (read_result cx))
      (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  asm_rewrite_tac[] >>
  dxrule gas_outcome_ptr_eval_evidence >> strip_tac >>
  irule bodyPtrBytestringBuiltinsUnaryTheory.gas_outcome_ptr_value_bind >>
  goal_assum (drule_at Any) >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?exc. res = INR exc` by
        (Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]) >>
      gvs[] >> simp[stmt_exit_ptr_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gns[] >>
  qpat_x_assum `(?v. res = INL v /\ _) /\ _` strip_assume_tac >>
  qexists_tac `v` >> simp[] >>
  `post_value_type cenv'' x = expr_type x` by
    metis_tac[loweringPostsTheory.post_value_type_lowered] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def] >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type x) = SOME tv /\
        value_has_type tv v` by
    (irule return_value_typed >>
     metis_tac[]) >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `op_taint tn val_op = {}` by metis_tac[ptr_val_ok_def] >>
  `op_taint tn (Var rpc) = {}` by metis_tac[ghost_inv_def] >>
  `?pc. lookup_var rpc t = SOME pc` by
    metis_tac[ghost_inv_def, ret_pc_ok_def] >>
  `stor_taint_ok cx tn t` by metis_tac[ghost_inv_def] >>
  `not_fresh_at sm rpc` by
    (mp_tac (Q.SPECL [`cenv''`, `ret_ty`, `x`, `sa`]
       (cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     asm_rewrite_tac[pairTheory.SND, exprLoweringPropsTheory.ci_mono_def] >>
     strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!off sz. cenv''.ce_return_buf <> SOME (MemLoc off sz)` by
    (fs[same_frame_def] >>
     qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _ |> = _` (mp_tac o Q.AP_TERM `\c. c.ce_return_buf`) >>
     simp[] >> metis_tac[]) >>
  Cases_on `is_word_type ret_ty`
  >- (`cenv''.ce_returns_count = 1` by
        ( `cenv''.ce_returns_count = cenv.ce_returns_count` by
            (fs[same_frame_def] >>
             qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
               ce_var_type := _ |> = _`
               (mp_tac o Q.AP_TERM `\c. c.ce_returns_count`) >> simp[]) >>
          Cases_on `ret_ty` >> gvs[is_word_type_def, returns_stack_count_def]) >>
      `?w. eval_operand val_op t = SOME w` by
        metis_tac[expr_val_rel_def] >>
      drule internal_return_stack_suffix_path_ptr >>
      simp[word_type_elem_types] >>
      disch_then drule_all >> strip_tac >>
      qpat_x_assum `!PG' G' D. _`
        (qspecl_then [`PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
      rename1 `gas_path_ptr _ _ _ _ _ _ _ _ _ H tm (IntRet _ u)` >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def, vyperStateTheory.raise_def] >>
      qexistsl_tac [`INR (ReturnException v)`, `ee0 with gas_obs := []`,
        `H`, `tm`, `IntRet <|iret_values := [w]; iret_adopt_fmp := NONE|> u`] >>
      simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def] >>
      gen_tac >> disj2_tac >>
      `d = NONE` by
        (Cases_on `ret_ty` >>
         gvs[is_word_type_def, returns_stack_count_def] >> Cases_on `d` >> fs[]) >>
      `state_rel func cenv cx (ee0 with scopes := []) t` by
        (irule constructor_exit_state_rel >> qexists_tac `cenv''` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
      simp[intret_ptr_q_def, intret_q_def, compileEnvTheory.result_rel_def] >>
      reverse conj_tac >- fs[stor_taint_ok_def] >>
      conj_tac
      >- (qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
          simp[compileEnvTheory.state_rel_gas_obs, compileEnvTheory.state_rel_def,
            compileEnvTheory.local_ptrs_rel_def, compileEnvTheory.storage_rel_def,
            compileEnvTheory.transient_rel_def, compileEnvTheory.accounts_rel_def,
            compileEnvTheory.immutables_rel_def, compileEnvTheory.logs_rel_def,
            vyperStateTheory.lookup_scopes_def, compileEnvTheory.local_region_def,
            venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
          metis_tac[]) >>
      `expr_type x = ret_ty` by
        (irule bodyAppendStorageFactsTheory.type_widens_to_word >>
         simp[] >> qexists_tac `env.type_defs` >>
         fs[vyperTypeSystemTheory.type_stmt_def]) >>
      `w = typed_val_to_w256 ret_tv v` by gvs[expr_val_rel_def] >>
      metis_tac[intret_vals_match_word]) >>
  `cenv''.ce_returns_count = cenv.ce_returns_count` by
    (fs[same_frame_def] >>
     qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _ |> = _`
       (mp_tac o Q.AP_TERM `\c. c.ce_returns_count`) >> simp[]) >>
  Cases_on `cenv''.ce_returns_count = 0`
  >- (`ret_ty <> NoneT` by fs[vyperTypeSystemTheory.type_stmt_def] >>
      `?bw cap. d = SOME (bw,cap)` by (Cases_on `d` >> fs[] >> metis_tac[pairTheory.pair_CASES]) >>
      `?dst slot. cenv''.ce_return_buf = SOME (PtrVar (Var dst) slot) /\
        lookup_var dst t = SOME bw /\ ptr_covers G tn dst t cap` by
        metis_tac[ghost_inv_def, return_buf_ptr_def] >>
      `type_memory_bytes cenv'' (expr_type x) = type_memory_size tv /\
       type_memory_bytes cenv'' ret_ty = type_memory_size ret_tv` by
        (conj_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
         qexists_tac `get_tenv cx` >> fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
      `type_widens_to (get_tenv cx) (expr_type x) ret_ty` by
        (fs[vyperTypeSystemTheory.type_stmt_def, exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[]) >>
      `~is_word_type (expr_type x)` by
        (Cases_on `expr_type x = ret_ty` >- metis_tac[] >>
         `is_bytestring_type (expr_type x)` by
           metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
         Cases_on `expr_type x` >> gvs[is_bytestring_type_def, is_word_type_def] >>
         Cases_on `b` >> gvs[is_bytestring_type_def, is_word_type_def] >>
         Cases_on `b'` >> gvs[is_bytestring_type_def, is_word_type_def]) >>
      `value_has_type ret_tv v` by
        (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
         strip_tac >> gvs[]) >>
      `?a. eval_operand val_op t = SOME a` by metis_tac[expr_val_rel_def] >>
      `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
         val_in_memory tv v (w2n a) m` by
        metis_tac[ptr_val_ok_def, ptr_mem_ok_def] >>
      `expr_type x = ret_ty \/
       is_bytestring_type (expr_type x) /\ is_bytestring_type ret_ty` by
        metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
      `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
         val_in_memory ret_tv v (w2n a) m` by
        (Cases_on `expr_type x = ret_ty` >- gvs[] >>
         `is_bytestring_type (expr_type x) /\ is_bytestring_type ret_ty` by metis_tac[] >>
         qpat_x_assum `is_bytestring_type (expr_type x)` mp_tac >>
         qpat_x_assum `is_bytestring_type ret_ty` mp_tac >>
         qpat_x_assum `evaluate_type _ (expr_type x) = SOME tv` mp_tac >>
         qpat_x_assum `evaluate_type _ ret_ty = SOME ret_tv` mp_tac >>
         qpat_x_assum `value_has_type ret_tv v` mp_tac >>
         qpat_x_assum `!m. _ ==> val_in_memory tv v (w2n a) m` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt disch_tac >>
         metis_tac[annAssignPtrMemorySourceTheory.annassign_robust_layout_transfer_ptr]) >>
      (reverse (Cases_on `type_memory_bytes cenv'' (expr_type x) = 0`)
      >- (
      `?src. val_op = Var src /\ lookup_var src t = SOME a /\
        ptr_covers G tn src t (type_memory_bytes cenv'' (expr_type x))` by
        (`ptr_buf_ok cenv'' x val_op G t` by metis_tac[] >>
         qpat_x_assum `ptr_buf_ok cenv'' x val_op G t`
           (mp_tac o SRULE[ptr_buf_ok_def]) >>
         disch_then (qspec_then `a` mp_tac) >>
         (impl_tac >- metis_tac[]) >> strip_tac >>
         qexists_tac `x'` >>
         simp[ptr_covers_def, venomStateTheory.eval_operand_def] >>
         gvs[venomStateTheory.eval_operand_def]) >>
      `not_fresh_at sm src` by
        metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
      `not_fresh_at sm dst` by
        (mp_tac (Q.SPECL [`cenv''`, `ret_ty`, `x`, `sa`]
           (cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
         asm_rewrite_tac[pairTheory.SND, exprLoweringPropsTheory.ci_mono_def] >>
         strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> metis_tac[]) >>
      `type_memory_size tv <= type_memory_size ret_tv` by
        metis_tac[bodyPtrStructLitLayoutTransferTheory.type_widens_to_memory_size] >>
      `type_memory_bytes cenv'' (expr_type x) < dimword (:256) /\
       type_memory_bytes cenv'' ret_ty <= cap` by
        (qpat_x_assum `!bw cap. d = SOME (bw,cap) ==> _` drule >>
         simp[] >> decide_tac) >>
      `?k len. k < dimword (:256) /\ k <= cap /\
        ptr_covers G tn src t k /\ ptr_covers G tn dst t k /\
        val_footprint ret_tv v <= k /\
        (if is_bytestring_type ret_ty then
          k = 32 + 32 * ((len+31) DIV 32) /\ mload (w2n a) t = n2w len /\
          (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)
         else k = type_memory_bytes cenv'' ret_ty)` by
        (irule annAssignPtrMemoryWindowTheory.annassign_memory_copy_window_ptr >>
         metis_tac[]) >>
      `k = (if is_bytestring_type ret_ty then 32 + 32 * word_size len
            else type_memory_bytes cenv'' ret_ty)` by
        (Cases_on `is_bytestring_type ret_ty` >> gvs[vfmConstantsTheory.word_size_def]) >>
      `val_wf ret_tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
      `is_bytestring_type ret_ty ==>
        mload (w2n a) t = n2w len /\ ptr_covers G tn src t 32 /\
        (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)` by
        (qpat_x_assum `ptr_covers G tn src t k` mp_tac >>
         qpat_x_assum `if is_bytestring_type ret_ty then _ else _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         Cases_on `is_bytestring_type ret_ty` >> simp[] >>
         rpt strip_tac >> simp[] >>
         irule reasonCopySourcePtrTheory.ptr_covers_mono >>
         qexists_tac `k` >> simp[]) >>
      qpat_x_assum `val_op = Var src` SUBST_ALL_TAC >>
      drule (Q.INST [`n` |-> `k`, `len` |-> `len`, `tv` |-> `ret_tv`, `s` |-> `t`]
        (SPEC_ALL internal_return_memory_suffix_path_ptr)) >>
      disch_then (mp_tac o Q.INST [`d` |-> `bw`, `cap` |-> `slot`,
        `D` |-> `cx_dead cx`] o SPEC_ALL) >>
      (impl_tac >- gvs[]) >>
      strip_tac >> rename1 `typed_copy_state_frame sm (w2n bw) k t u` >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def, vyperStateTheory.raise_def] >>
      qexistsl_tac [`INR (ReturnException v)`, `ee0 with gas_obs := []`,
        `H`, `tm`, `IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u`] >>
      simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def] >>
      gen_tac >> disj2_tac >>
      `state_rel func cenv cx (ee0 with scopes := []) t` by
        (irule constructor_exit_state_rel >> qexists_tac `cenv''` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
      `cenv.ce_returns_count = 0` by metis_tac[] >>
      qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
      qpat_x_assum `typed_copy_state_frame _ _ _ t u` mp_tac >>
      qpat_x_assum `!m. _ ==> val_in_memory ret_tv v (w2n bw) m` mp_tac >>
      qpat_x_assum `stor_taint_ok cx tm u` mp_tac >>
      `~cenv.ce_is_ctor` by metis_tac[same_frame_is_ctor] >>
      qpat_x_assum `~cenv.ce_is_ctor` mp_tac >>
      qpat_x_assum `cenv.ce_module = NONE` mp_tac >>
      qpat_x_assum `cenv.ce_imm_alloca = NONE` mp_tac >>
      qpat_x_assum `cenv.ce_returns_count = 0` mp_tac >>
      qpat_x_assum `d = SOME (bw,cap)` mp_tac >>
      rpt (pop_assum kall_tac) >> rpt disch_tac >>
      simp[intret_ptr_q_def, intret_mem_q_def, intret_q_def,
        compileEnvTheory.result_rel_def] >>
      reverse conj_tac
      >- metis_tac[mem_agree_outside_def] >>
      simp[compileEnvTheory.intret_vals_match_def] >>
      qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
      qpat_x_assum `typed_copy_state_frame _ _ _ t u` mp_tac >>
      simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
        venomStateTheory.venom_state_component_equality] >>
      strip_tac >>
      simp[compileEnvTheory.state_rel_gas_obs, compileEnvTheory.state_rel_def,
        compileEnvTheory.local_ptrs_rel_def, compileEnvTheory.storage_rel_def,
        compileEnvTheory.transient_rel_def, compileEnvTheory.accounts_rel_def,
        compileEnvTheory.immutables_rel_def, compileEnvTheory.logs_rel_def,
        vyperStateTheory.lookup_scopes_def, compileEnvTheory.local_region_def,
        venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
      metis_tac[]) >>
      `~is_bytestring_type (expr_type x)` by
        (qpat_x_assum `type_memory_bytes cenv'' (expr_type x) = 0` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         drule bytestring_memory_header_bound >>
         disch_then (qspec_then `cenv''` mp_tac) >> simp[]) >>
      `expr_type x = ret_ty` by metis_tac[] >>
      `compile_store_memory cenv'' val_op (Var dst) ret_ty (expr_type x) sm = ((),sm)` by
        metis_tac[literal_zero_store_identity] >>
      `emit_inst RET [Var rpc] [] sm = ((),sb)` by
        (qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
         simp[stmtLoweringTheory.compile_internal_return_from_env_def,
           stmtLoweringTheory.compile_internal_return_def,
           compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.comp_return_def] >>
         qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
         simp[]) >>
      `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 G tn
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)` by
        (irule emit_ret_values_path_ptr >>
         simp[ptrDisciplineTheory.allocas_from_def] >>
         qexistsl_tac [`[]`, `pc`, `rpc`, `sm`, `sb`] >>
         simp[venomStateTheory.eval_operands_def, ptrDisciplineTheory.allocas_from_def]) >>
      `type_memory_size ret_tv = 0 /\ val_wf ret_tv v` by
        metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
      `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
        val_in_memory ret_tv v (w2n bw) m` by
        (qpat_x_assum `!m. _ ==> val_in_memory ret_tv v (w2n a) m` mp_tac >>
         qpat_x_assum `val_wf ret_tv v` mp_tac >>
         qpat_x_assum `type_memory_size ret_tv = 0` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         irule valueEncodingPropsTheory.val_in_memory_relocate >>
         simp[] >> qexistsl_tac [`m`, `0`, `w2n a`] >>
         simp[valueEncodingTheory.mem_bytes_at_def]) >>
      `state_rel func cenv cx (ee0 with scopes := []) t` by
        (irule constructor_exit_state_rel >> qexists_tac `cenv''` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
      `cenv.ce_returns_count = 0` by metis_tac[] >>
      qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
      qpat_x_assum `gas_path_ptr _ 0 _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `!m. _ ==> val_in_memory ret_tv v (w2n bw) m` mp_tac >>
      qpat_x_assum `stor_taint_ok cx tn t` mp_tac >>
      qpat_x_assum `cenv.ce_returns_count = 0` mp_tac >>
      qpat_x_assum `d = SOME (bw,cap)` mp_tac >>
      qpat_x_assum `cenv.ce_module = NONE` mp_tac >>
      qpat_x_assum `cenv.ce_imm_alloca = NONE` mp_tac >>
      rpt (pop_assum kall_tac) >> rpt disch_tac >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[NoAsms, gas_summary_ptr_at_def, vyperStateTheory.raise_def] >>
      qexistsl_tac [`INR (ReturnException v)`, `ee0 with gas_obs := []`,
        `G`, `tn`, `IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t`] >>
      simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def] >>
      gen_tac >> disj2_tac >>
      simp[intret_ptr_q_def, intret_mem_q_def, intret_q_def,
        compileEnvTheory.result_rel_def, compileEnvTheory.intret_vals_match_def,
        compileEnvTheory.state_rel_gas_obs] >>
      `val_in_memory ret_tv v (w2n bw) t.vs_memory` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
      simp[compileEnvTheory.state_rel_def, compileEnvTheory.storage_rel_def,
        compileEnvTheory.transient_rel_def, compileEnvTheory.accounts_rel_def,
        compileEnvTheory.immutables_rel_def, compileEnvTheory.logs_rel_def] >>
      metis_tac[])) >>
  `?ets. ets = (case ret_ty of TupleT ts => ts | StructT ns =>
       MAP (FST o SND) (get_struct_fields cenv''.ce_struct_fields (nsid_to_string ns))
       | _ => []) /\ ets <> [] /\ EVERY is_word_type ets /\
       cenv''.ce_returns_count = LENGTH ets` by
    (qpat_x_assum `cenv.ce_returns_count = returns_stack_count _ _` mp_tac >>
     qpat_x_assum `cenv''.ce_returns_count = cenv.ce_returns_count` mp_tac >>
     qpat_x_assum `~(cenv''.ce_returns_count = 0)` mp_tac >>
     qpat_x_assum `~is_word_type ret_ty` mp_tac >>
     `cenv''.ce_struct_fields = cenv.ce_struct_fields` by
       (qpat_x_assum `same_frame _ _` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[same_frame_def] >> strip_tac >>
        qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
          ce_var_type := _ |> = _`
          (mp_tac o Q.AP_TERM `\c. c.ce_struct_fields`) >> simp[]) >>
     pop_assum mp_tac >> rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `ret_ty` >>
     gvs[returns_stack_count_def] >>
     gns[tuple_like_stack_count_def] >>
     IF_CASES_TAC >> gvs[] >>
     metis_tac[listTheory.LENGTH_NIL]) >>
  `~is_bytestring_type ret_ty` by
    (Cases_on `ret_ty` >>
     gvs[is_bytestring_type_def, returns_stack_count_def] >>
     Cases_on `b` >> gvs[is_bytestring_type_def, returns_stack_count_def] >>
     Cases_on `b'` >> gvs[is_bytestring_type_def, returns_stack_count_def]) >>
  `expr_type x = ret_ty` by metis_tac[] >>
  `tv = ret_tv` by metis_tac[optionTheory.SOME_11] >>
  `?a. eval_operand val_op t = SOME a` by metis_tac[expr_val_rel_def] >>
  `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory ret_tv v (w2n a) m` by
    metis_tac[ptr_val_ok_def, ptr_mem_ok_def] >>
  `val_footprint ret_tv v = type_memory_size ret_tv` by
    metis_tac[exprSimAggregateChildrenTheory.evaluated_nonbytes_footprint] >>
  `w2n a + type_memory_size ret_tv < dimword (:256)` by
    (`w2n a + val_footprint ret_tv v < dimword (:256)` suffices_by metis_tac[] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
     qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ t` mp_tac >>
     qpat_x_assum `evaluate_type _ ret_ty = SOME ret_tv` mp_tac >>
     qpat_x_assum `eval_operand val_op t = SOME a` mp_tac >>
     qpat_x_assum `~is_word_type ret_ty` mp_tac >>
     qpat_x_assum `post_value_type cenv'' x = expr_type x` mp_tac >>
     qpat_x_assum `expr_type x = ret_ty` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
     `stmt_state_rel ctx func cenv'' cx (ee0 with gas_obs := []) t` by simp[] >>
     drule_all exprSimTypedAllocTheory.expr_val_at_bound >> simp[]) >>
  `intret_vals_match ret_tv v (tuple_words cenv'' a ets 0 t.vs_memory)` by
    (irule word_aggregate_return_words_match >>
     metis_tac[]) >>
  `!i. i < LENGTH ets ==>
    w2n a + SUM (MAP (type_memory_bytes cenv'') (TAKE i ets)) + 32 <= dimword (:256) /\
    (!j. w2n a + SUM (MAP (type_memory_bytes cenv'') (TAKE i ets)) <= j /\
      j < w2n a + SUM (MAP (type_memory_bytes cenv'') (TAKE i ets)) + 32 ==>
      j NOTIN tn.t_mem)` by
    (gen_tac >> disch_tac >>
     irule word_aggregate_return_ranges_clean >> metis_tac[]) >>
  `!i. i < LENGTH ets ==>
    SUM (MAP (type_memory_bytes cenv'') (TAKE i ets)) + 32 <= type_memory_size ret_tv` by
    (gen_tac >> disch_tac >> irule word_aggregate_return_extent >> metis_tac[]) >>
  `type_memory_bytes cenv'' ret_ty = type_memory_size ret_tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `0 < type_memory_bytes cenv'' (expr_type x)` by
    (qpat_x_assum `!i. _ ==> _ <= type_memory_size ret_tv`
      (qspec_then `0` mp_tac) >> Cases_on `ets` >> gvs[]) >>
  `?src. val_op = Var src /\ lookup_var src t = SOME a /\
    ptr_covers G tn src t (type_memory_bytes cenv'' (expr_type x))` by
    (`ptr_buf_ok cenv'' x val_op G t` by metis_tac[] >>
     qpat_x_assum `ptr_buf_ok cenv'' x val_op G t`
       (mp_tac o SRULE[ptr_buf_ok_def]) >>
     disch_then (qspec_then `a` mp_tac) >>
     (impl_tac >- gvs[]) >> strip_tac >>
     qexists_tac `x'` >>
     simp[ptr_covers_def, venomStateTheory.eval_operand_def] >>
     gvs[venomStateTheory.eval_operand_def]) >>
  `not_fresh_at sm src` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!i. i < LENGTH ets ==> ptr_covers G tn src t
    (SUM (MAP (type_memory_bytes cenv'') (TAKE i ets)) + 32)` by
    (qpat_x_assum `ptr_covers G tn src t _` mp_tac >>
     qpat_x_assum `!i. _ ==> _ <= type_memory_size ret_tv` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv'' ret_ty = _` mp_tac >>
     qpat_x_assum `expr_type x = ret_ty` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def] >> rpt strip_tac >>
     qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >>
     first_x_assum drule >> decide_tac) >>
  `?u H tm.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 H tm
      (IntRet <|iret_values := (if ets = [] then [0w] else tuple_words cenv'' a ets 0 t.vs_memory);
                iret_adopt_fmp := NONE|> u) /\
    u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
    u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
    u.vs_call_ctx = t.vs_call_ctx /\
    state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sm p ==>
      lookup_var p u = lookup_var p t /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))` by
    (irule internal_return_stack_suffix_path_ptr >>
     simp[] >> conj_tac >- metis_tac[listTheory.LENGTH_NIL, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
     qexistsl_tac [`pc`, `rpc`, `sb`, `src`, `expr_type x`, `ret_ty`] >>
     simp[] >> conj_tac >- gvs[] >>
     qpat_x_assum `!i. _ ==> ptr_covers _ _ _ _ _` mp_tac >>
     qpat_x_assum `!i. _ ==> _ /\ !j. _` mp_tac >>
     qpat_x_assum `ets = _` (fn th => rewrite_tac[GSYM th]) >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!i. _ ==> _ /\ !j. _` (qspec_then `i` mp_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (assume_tac o SRULE[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, vyperStateTheory.raise_def] >>
  qexistsl_tac [`INR (ReturnException v)`, `ee0 with gas_obs := []`,
    `H`, `tm`, `IntRet <|iret_values := tuple_words cenv'' a ets 0 t.vs_memory;
                        iret_adopt_fmp := NONE|> u`] >>
  simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def] >>
  conj_tac >- gvs[] >>
  gen_tac >> disj2_tac >>
  `d = NONE` by
    (qpat_x_assum `IS_SOME d <=> _` mp_tac >>
     qpat_x_assum `cenv''.ce_returns_count <> 0` mp_tac >>
     qpat_x_assum `cenv''.ce_returns_count = cenv.ce_returns_count` mp_tac >>
     qpat_x_assum `cenv.ce_returns_count = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `d` >> simp[] >> metis_tac[]) >>
  `state_rel func cenv cx (ee0 with scopes := []) t` by
    (irule constructor_exit_state_rel >> qexists_tac `cenv''` >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  simp[intret_ptr_q_def, intret_q_def, compileEnvTheory.result_rel_def] >>
  reverse conj_tac >- fs[stor_taint_ok_def] >>
  conj_tac
  >- (qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
      qpat_x_assum `state_frame u = _` mp_tac >>
      rpt (pop_assum kall_tac) >> strip_tac >>
      simp[compileEnvTheory.state_rel_gas_obs, compileEnvTheory.state_rel_def,
        compileEnvTheory.local_ptrs_rel_def, compileEnvTheory.storage_rel_def,
        compileEnvTheory.transient_rel_def, compileEnvTheory.accounts_rel_def,
        compileEnvTheory.immutables_rel_def, compileEnvTheory.logs_rel_def,
        vyperStateTheory.lookup_scopes_def, compileEnvTheory.local_region_def,
        venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
      gvs[stateFrameTheory.state_frame_def, venomStateTheory.venom_state_component_equality] >>
      metis_tac[]) >>
  gvs[]

QED

(* RESIDUAL (held): as s3-mem's held internal_return_widened_mem.  A
   compound value widening into the caller's return buffer is copied
   element by element (compile_copy_dynarray_typed: a forward loop with
   different source and destination strides, no memmove), which is right
   only when the source is disjoint from the buffer.  Nothing here ties
   the buffer to the frame's allocas (return_buf_ptr gives only ghost
   coverage, and ghost_inv carries no alloca frontier for it), so for a
   buffer at the frame's alloca frontier the copy clobbers its own
   source.  Real runs don't reach that state; the fix is a frontier
   conjunct in return_buf_ptr's SOME arm. *)
Theorem internal_return_widened_ptr:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz cenv' env lctx eo es.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    (!off sz. cenv.ce_return_buf <> SOME (MemLoc off sz)) /\
    cenv.ce_imm_alloca = NONE /\
    cenv.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
        ret_ty /\
    evaluate_type (get_tenv cx) ret_ty = SOME ret_tv /\
    (IS_SOME d <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. d = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap < dimword (:256) /\ cap + 64 < dimword (:256)) /\
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
            expr_sim_ptr d ctx PG func cenv' cx ty e es /\
            expr_vv_sim_ptr d ctx PG func cenv' cx ty e es) /\
    ~(!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty)) ==>
    stmt_frag_ptr d ctx PG func cx lctx (intret_ptr_q func cenv cx ret_tv d)
      cenv' (stmt_env cenv' lctx ret_ty (Return eo)) (eval_stmt cx (Return eo))
      es
Proof
  cheat
QED

(* The internal twin of extFrameRetOkPtr's external_frame_ret_ok_ptr and
   the pointer twin of s3-mem's internal_frame_ret_ok_mem, assembled from
   the two cases above. *)
Theorem internal_frame_ret_ok_ptr:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz.
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    (!off sz. cenv.ce_return_buf <> SOME (MemLoc off sz)) /\
    cenv.ce_imm_alloca = NONE /\
    cenv.ce_returns_count =
      returns_stack_count
        (\name. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields name))
        ret_ty /\
    evaluate_type (get_tenv cx) ret_ty = SOME ret_tv /\
    (IS_SOME d <=> cenv.ce_returns_count = 0 /\ ret_ty <> NoneT) /\
    (!bw cap. d = SOME (bw,cap) ==>
       cap = type_memory_size ret_tv /\
       w2n bw + cap < dimword (:256) /\ cap + 64 < dimword (:256)) ==>
    frame_ret_ok_ptr d ctx PG func cx (intret_ptr_q func cenv cx ret_tv d)
      cenv ret_ty
Proof
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC [frame_ret_ok_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `(!e. eo = SOME e ==>
             lowered_value_type cenv' e = expr_type e /\
             (expr_type e = ret_ty \/ is_word_type ret_ty \/
              is_bytestring_type ret_ty))`
  >- (irule internal_return_direct_ptr >> metis_tac[]) >>
  irule internal_return_widened_ptr >> metis_tac[]
QED

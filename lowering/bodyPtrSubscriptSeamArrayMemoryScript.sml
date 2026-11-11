(*
 * Seam of bodyPtrSubscript's subscript_expr_ptr_ok: an element of a static
 * array in memory, laid out at its own type, whose index frames the base.
 *
 * TOP-LEVEL:
 *   subscript_array_framed_memory_ptr
 *)
Theory bodyPtrSubscriptSeamArrayMemory
Ancestors
  bodyPtrSubscriptRejectedSelector bodyPtrSubscriptSignedBounds
  bodyPtrSubscriptCountedAdd bodyPtrSubscriptSeamArrayMemoryFinish
  bodyPtrSubscriptSeamArrayMemoryPrepare bodyPtrSubscriptSeamArrayMemoryTyping
  exprSimSubscriptArrayFramed exprSimSubscriptArrayEndpoint
  exprSimSubscriptArraySource exprSimSource exprSimHyps exprLoweringProps
  exprSimUnwrap gasSummaryComposePtr fragGasPathPtr fragExec gasContext
  gasOutcome gasExemptCert freshWrites exprOperandVar exprWordOperand
  exprSimSubscriptArrayOrigin
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts context
  exprLowering vyperInterpreter vyperState vyperContext vyperAST

(* The memory half of the pointer twin of S1's
   compile_subscript_array_framed_base_case (exprSimSubscriptArray): a
   static array with no dynamic array inside it, lowered to a memory
   pointer and laid out at its own type (an internal call whose site widens
   the callee's return type is the residual
   bodyPtrSubscriptWidenedResidual), whose source result is no storage
   place, and whose index leaves the source locals and immutables as they
   were.  compile_subscript lowers the base, then the index (lower_value at
   ty), then compile_array_subscript with is_dynamic = F: the bounds check
   against the literal static count (SLT for a signed index, LT, ISZERO,
   OR, ISZERO, ASSERT) and the element address base + idx * elem_size.  The
   base's bytes lie in one of its own allocations or in a live local's
   region and hold no length word, so the index's expr_post and ghost_kept
   keep them and their taint.  The bounds check compares the index with a
   literal count (LT [idx; Lit n]), outside access_ok's two-variable
   comparison clause; the index's ptr_val_ok (a word: untainted, no
   provenance) serves the taint checks, and MUL gives no provenance.
   Hints: the S1 proof is exprSimSubscriptArrayFramed and the
   exprSimSubscriptArray{Compose,Suffix,Source,Frame,Endpoint,Origin}
   theories in this tree; the lane helpers bodyPtrSubscriptBoundsRun,
   bodyPtrSubscriptSignedBounds, bodyPtrSubscriptRejectedSelector and
   bodyPtrSubscriptCountedAdd have the counted bounds check, its abort and
   the address arithmetic. *)
Theorem subscript_array_framed_memory_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es et n.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et (Fixed n) /\
    place_type cenv e1 = ValPT (ArrayT et (Fixed n)) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t r t'. eval_expr cx e2 t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t.
       eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ann = et` by metis_tac[array_subscript_index_type] >> gvs[] >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty e1 es` by
    (irule array_subscript_base_sim_ptr >> metis_tac[]) >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty e1 sa = (bvv,sm)` >>
  `vv_location bvv = SOME LocMemory` by metis_tac[pairTheory.FST] >>
  `loc = LocMemory` by simp[] >> gvs[] >>
  suspend "compile"
QED

Resume subscript_array_framed_memory_ptr[compile]:
  `ci_mono sa sm` by (drule (cj 1 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono sm st2` by (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono st2 sb` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     simp[] >> disch_then (SUBST1_TAC o SYM) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func` by
    (gvs[ci_mono_def] >> metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2` by
    metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `gas_admissible (eval_expr cx e1) expr_vv_res_ok es` by
    (simp[gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_array_subscript_base,
               expr_body_pre_vv_res_ok]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
      (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_ptr_at_marked])
      >- suspend "base_normal" >> suspend "base_exit") >>
  suspend "base_exempt"
QED

Resume subscript_array_framed_memory_ptr[base_normal]:
  qpat_x_assum `(\res ee G tn t. _) _ _ _ _ _`
    (strip_assume_tac o BETA_RULE) >> gvs[] >>
  `?p. bvv = LocatedValue (ArrayT ann (Fixed n)) p /\ p.ptr_location = LocMemory` by
    (Cases_on `bvv` >> gvs[vv_location_def] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
          compileEnvTheory.is_bytestring_type_def] >> metis_tac[]) >>
  qpat_x_assum `bvv = _` SUBST_ALL_TAC >>
  `expr_sim_ptr d ctx PG func cenv cx ty e2 (es_end with gas_obs := [])` by
    (irule array_subscript_index_sim_ptr >> metis_tac[]) >>
  `expr_body_pre cenv cx env e2 (es_end with gas_obs := [])` by
    (drule_all bodyPtrSubscriptSeamArrayMemoryAfterIndexTheory.marked_array_base_source_view >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok
     (es_end with gas_obs := [])` by
    (simp[gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_res_ok]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    gvs[loweringPostsTheory.vv_post_def] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_erase,
              fragGasPathTheory.gas_path_normal] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  pure_rewrite_tac[GSYM gas_outcome_ptr_def] >>
  irule fixed_array_after_base_ptr >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  suspend "callback"
QED

Resume subscript_array_framed_memory_ptr[callback]:
  qexists_tac `d` >> fs[] >> rpt gen_tac >> strip_tac >>
  `is_word_type (expr_type e2)` by
    (drule_all array_subscript_index_type >> strip_tac >>
     Cases_on `expr_type e2` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
     Cases_on `b` >> gvs[vyperTypeSystemTheory.is_int_type_def,
                         compileEnvTheory.is_word_type_def]) >>
  `post_value_type cenv e2 = expr_type e2` by simp[] >>
  `(!x. iop = Var x ==> not_fresh_at st2 x) /\ (!l. iop <> Label l)` by
    (drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac (CONJUNCT1 compiler_compile_var)) >> simp[vv_operand_def]) >>
  `expr_body_pre cenv cx env e1 es` by metis_tac[expr_body_pre_array_subscript_base] >>
  `!l. p.ptr_operand <> Label l` by
    (drule compile_array_pointer_not_label >> disch_then irule >> simp[] >>
     qexists_tac `env` >>
     gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x)` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `~q.vs_halted` by
    metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_erase, fragGasPathTheory.gas_path_normal] >>
  suspend "normal_summary"
QED

Resume subscript_array_framed_memory_ptr[normal_summary]:
  simp[mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule (bodyPtrSubscriptSeamArrayMemoryAfterIndexTheory.fixed_array_after_index_summary_ptr
    |> PURE_REWRITE_RULE [mk_ptr_def, vyperASTTheory.expr_type_def]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`G`,`marks`,`imarks`,`iop`,
    `compile_ptr_load F cenv.ce_imm_alloca LocMemory`,`es_end`,`p`,`sm`,`st2`,`tn`,`t`,
    `word_scale LocMemory`] >>
  fs[vv_operand_def]
QED
Resume subscript_array_framed_memory_ptr[base_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `INR exc` >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR exc`,`es_end`,`G`,`tn`,`r`] >> simp[] >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  gvs[gas_marked_exec_ptr_bind_exception]
QED
Resume subscript_array_framed_memory_ptr[base_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC
QED
Finalise subscript_array_framed_memory_ptr

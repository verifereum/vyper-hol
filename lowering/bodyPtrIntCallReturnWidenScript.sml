(*
 * internal_return_widened_ptr's body, up to the two facts it lacks, both
 * owed by whoever closes the held leaf (see the RESIDUAL comment on
 * internal_return_widened_ptr in bodyPtrIntCallFrameRet):
 *   - a widened compound return's source is disjoint from the caller's
 *     return buffer at the return point (from the return buffer's frame
 *     invariant once it carries the caller-buffer frontier);
 *   - a returned internal call's compiled return type agrees with its
 *     signature (at the body induction, from expr_body_pre's FST id = NONE
 *     plus body_inv).
 * The held leaf closes by irule internal_return_widened_ptr_of_disjoint
 * once both are derivable.
 *
 * TOP-LEVEL:
 *   internal_return_widened_ptr_of_disjoint
 *)
Theory bodyPtrIntCallReturnWiden
Ancestors
  bodyPtrIntCallFrameRet internalReturnWidenPtr
  bodyPtrDefs intCallReturnMem stmtSimReturn bodySim
  internalReturnStackPtr internalReturnStorePtr internalReturnCountedPtr
  internalReturnStackSuffixPtr internalReturnMemorySuffixPtr
  stmtSimReturnWiden compileEnv valueEncoding compileVyper loweringPosts
  ptrDiscipline fragGasPathPtr venomExecSemantics ctorReturnFrame
  returnValueTyped valueEncodingTyping typedMemoryCopy
  internalReturnUnlockPtr internalReturnUnlockSuffixPtr
  bodyPtrBytestringBuiltinsEval bodyPtrStructLitLayoutTransfer
  reasonCopySourcePtr loweringStateRelDefs valueEncodingDefs
  exprSimHyps exprSimHypsDefs exprSimIfExpCompat memoryLocalRhsProps
  bodyPtrIfExpEndpointTyping assignRelayoutCaller typedCopyPtr
  typedNormalizeWidening typedNormalizeStaticRigidity wideningZeroLayout
  aggregateEvaluatedLayout valueCopyBytes valueTypingMemoryProps
  representationCleanPtr valueEncodingProps exprOperandVar exprSimProps
  bodyExprPreFacts exprSimTypedAlloc exprSimAggregateChildren
  vyperTypeEvalSoundness vyperTypeSystem vyperTypeArgFits vyperTypeInvariants
  vyperTypeCallGraph vyperTyping exprLowering vyperAST typedTupleLeafContract
  vyperTypeExprSoundness venomState

(* ===== Static shape of a widened return ===== *)

Theorem tuple_like_stack_count_words[local]:
  tuple_like_stack_count ts <> 0 ==> EVERY is_word_type ts
Proof
  simp[tuple_like_stack_count_def] >> Cases_on `EVERY is_word_type ts` >> simp[]
QED

(* A type returned on the stack admits no proper widening into it. *)
Theorem widens_to_stack_return[local]:
  !tenv t u sft.
    type_widens_to tenv t u /\ returns_stack_count sft u <> 0 ==> t = u
Proof
  rpt strip_tac >>
  Cases_on `is_word_type u` >- metis_tac[compileEnvTheory.type_widens_to_word] >>
  Cases_on `u` >> gvs[returns_stack_count_def, is_word_type_def]
  >~ [`TupleT ts`]
  >- (drule tuple_like_stack_count_words >> strip_tac >>
      irule type_widens_to_static_identity >>
      conj_tac
      >- (qexists_tac `FEMPTY` >>
          fs[is_abi_dynamic_def, listTheory.EXISTS_MEM, listTheory.EVERY_MEM] >>
          metis_tac[word_type_abi_static]) >>
      metis_tac[]) >>
  metis_tac[typedNormalizeWideningTheory.type_widens_to_struct]
QED

Theorem stack_count_zero_not_word[local]:
  (!sft. returns_stack_count sft t = 0) ==> ~is_word_type t
Proof
  rpt strip_tac >> first_x_assum (qspec_then `ARB` mp_tac) >>
  Cases_on `t` >> fs[is_word_type_def, returns_stack_count_def]
QED

Theorem bytestring_stack_count[local]:
  is_bytestring_type t ==> returns_stack_count sft t = 0
Proof
  Cases_on `t` >> simp[is_bytestring_type_def, returns_stack_count_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[is_bytestring_type_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_bytestring_type_def, is_word_type_def]
QED

Theorem intcall_lowered_widens[local]:
  expr_sim_inv ce cx env es /\
  well_typed_expr env (Call ty (IntCall fid) args drv) ==>
  type_widens_to env.type_defs
    (lowered_value_type ce (Call ty (IntCall fid) args drv)) ty
Proof
  PairCases_on `fid` >>
  rw[expr_sim_inv_def, well_typed_expr_def, lowered_value_type_def] >>
  metis_tac[]
QED

(* The lowered type of an expression: its own type, a bytestring fitting
   its bytestring type, or an internal call's declared return type, which
   widens to the call's annotation. *)
Theorem return_lowered_cases[local]:
  expr_sim_inv ce cx env es /\ well_typed_expr env x ==>
  lowered_value_type ce x = expr_type x \/
  is_bytestring_type (expr_type x) /\
    is_bytestring_type (lowered_value_type ce x) \/
  (?ty fid args drv. x = Call ty (IntCall fid) args drv) /\
    type_widens_to (get_tenv cx) (lowered_value_type ce x) (expr_type x)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    (fs[expr_sim_inv_def, well_formed_type_def] >>
     metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates]) >>
  `!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
     ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty` by
    fs[expr_sim_inv_def] >>
  drule_all ifexp_lowered_type_classify >> rpt strip_tac >> gvs[] >>
  drule_all intcall_lowered_widens >> simp[expr_type_def]
QED

Theorem return_widened_count[local]:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME x))) /\
  ~(!e. SOME x = SOME e ==>
        lowered_value_type ce e = expr_type e /\
        (expr_type e = ret \/ is_word_type ret \/ is_bytestring_type ret)) ==>
  !sft. returns_stack_count sft ret = 0
Proof
  rpt strip_tac >> fs[] >>
  `well_typed_expr env x /\ type_widens_to env.type_defs (expr_type x) ret` by
    fs[type_stmt_return_some_iff] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  CCONTR_TAC >>
  `expr_type x = ret` by metis_tac[widens_to_stack_return] >>
  drule_all return_lowered_cases >> rpt strip_tac >> gvs[]
  >- metis_tac[bytestring_stack_count] >>
  metis_tac[widens_to_stack_return]
QED

Theorem return_widened_compound_shape[local]:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME x))) /\
  ~(!e. SOME x = SOME e ==>
        lowered_value_type ce e = expr_type e /\
        (expr_type e = ret \/ is_word_type ret \/ is_bytestring_type ret)) /\
  ~is_word_type ret ==>
  is_bytestring_type ret \/
  ~is_word_type (expr_type x) /\ ~is_bytestring_type (expr_type x) /\
  post_value_type ce x = lowered_value_type ce x /\
  lowered_value_type ce x <> ret /\
  type_widens_to (get_tenv cx) (lowered_value_type ce x) ret
Proof
  strip_tac >> Cases_on `is_bytestring_type ret` >> asm_rewrite_tac[] >>
  fs[] >>
  `well_typed_expr env x /\ type_widens_to env.type_defs (expr_type x) ret` by
    fs[type_stmt_return_some_iff] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `~is_word_type (expr_type x)` by
    (strip_tac >> fs[type_widens_to_def] >> metis_tac[arg_type_fits_word_type]) >>
  `~is_bytestring_type (expr_type x)` by
    (strip_tac >> fs[type_widens_to_def] >>
     metis_tac[arg_type_fits_bytestring_target]) >>
  `type_widens_to (get_tenv cx) (expr_type x) ret` by metis_tac[] >>
  drule_all return_lowered_cases >> strip_tac
  >- (drule post_value_type_lowered >> strip_tac >> gvs[]) >>
  `lowered_value_type ce x <> ret` by
    (strip_tac >> fs[] >> metis_tac[type_widens_to_antisym]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce x) ret` by
    metis_tac[type_widens_to_trans] >>
  qpat_x_assum `x = _` SUBST_ALL_TAC >>
  fs[expr_type_def]
QED

(* ===== The returned value's type at the lowered type ===== *)

Theorem return_intcall_lowered_typed[local]:
  expr_sim_inv ce cx env es /\
  well_typed_expr env (Call ann (IntCall id) args drv) /\
  call_evaluation_safe cx
    (int_calls_stmt (Return (SOME (Call ann (IntCall id) args drv)))) /\
  bind (eval_expr cx (Call ann (IntCall id) args drv)) (read_result cx)
    (es with gas_obs := g) = (INL v,es') ==>
  ?tv. evaluate_type (get_tenv cx)
         (lowered_value_type ce (Call ann (IntCall id) args drv)) = SOME tv /\
       value_has_type tv v
Proof
  rpt strip_tac >>
  `?sig. FLOOKUP env.fn_sigs id = SOME sig /\
         type_widens_to env.type_defs sig.ret_ty ann` by
    (PairCases_on `id` >> gvs[well_typed_expr_def] >> metis_tac[]) >>
  `lowered_value_type ce (Call ann (IntCall id) args drv) = sig.ret_ty` by
    (fs[expr_sim_inv_def, lowered_value_type_def] >> res_tac >> fs[]) >>
  `well_formed_type env.type_defs sig.ret_ty` by
    metis_tac[ifexp_frame_signature_return_well_formed] >>
  `well_typed_expr env (Call sig.ret_ty (IntCall id) args drv)` by
    (PairCases_on `id` >> gvs[well_typed_expr_def, type_widens_to_def]) >>
  `bind (eval_expr cx (Call sig.ret_ty (IntCall id) args drv)) (read_result cx)
     (es with gas_obs := g) = (INL v,es')` by
    (ONCE_REWRITE_TAC [Q.SPECL [`cx`, `sig.ret_ty`, `ann`]
       ifexp_internal_call_annotation_eval] >> first_assum ACCEPT_TAC) >>
  `call_evaluation_safe cx (int_calls_expr (Call sig.ret_ty (IntCall id) args drv))` by
    fs[int_calls_stmt_def, int_calls_expr_def] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  mp_tac (Q.INST [`e` |-> `Call sig.ret_ty (IntCall id) args drv`,
    `st` |-> `es with gas_obs := g`, `res` |-> `INL v`, `st'` |-> `es'`]
    eval_expr_read_type_sound) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  gvs[value_runtime_typed_def, env_consistent_def, env_context_consistent_def,
      expr_type_def]
QED

Theorem return_compound_lowered_typed[local]:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME x))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME x))) /\
  ~is_bytestring_type (expr_type x) /\
  bind (eval_expr cx x) (read_result cx) (es with gas_obs := g) = (INL v,es') ==>
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce x) = SOME tv /\
       value_has_type tv v
Proof
  rpt strip_tac >>
  `well_typed_expr env x` by fs[type_stmt_return_some_iff] >>
  Cases_on `?ann id args drv. x = Call ann (IntCall id) args drv`
  >- (gvs[] >> drule_all return_intcall_lowered_typed >> simp[]) >>
  `lowered_value_type ce x = expr_type x` by
    (drule_all return_lowered_cases >> rpt strip_tac >> gvs[]) >>
  drule_all return_value_typed >> simp[]
QED

(* ===== A bytestring return's live window ===== *)

Theorem bytestring_return_window[local]:
  is_bytestring_type ety /\ is_bytestring_type rty /\
  evaluate_type (get_tenv cx) ety = SOME etv /\
  evaluate_type (get_tenv cx) rty = SOME rtv /\
  value_has_type etv v /\ value_has_type rtv v /\
  ptr_val_ok cx ety v op G tn s /\ eval_operand op s = SOME a ==>
  ?src len. op = Var src /\ lookup_var src s = SOME a /\
    mload (w2n a) s = n2w len /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    val_footprint rtv v <= 32 + 32 * word_size len /\
    32 + 32 * word_size len <= type_memory_size rtv /\
    ptr_covers G tn src s (32 + 32 * word_size len) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory rtv v (w2n a) m)
Proof
  strip_tac >>
  `~is_word_type ety` by metis_tac[is_bytestring_word_type] >>
  `(?ne. etv = BaseTV (BytesT (Dynamic ne))) \/ (?ne. etv = BaseTV (StringT ne))` by
    metis_tac[bytestring_type_value] >>
  `(?nr. rtv = BaseTV (BytesT (Dynamic nr))) \/ (?nr. rtv = BaseTV (StringT nr))` by
    metis_tac[bytestring_type_value] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[ptr_val_ok_def, ptr_mem_ok_def, val_footprint_def, val_in_memory_def]
  >~ [`BytesV bs`]
  >- (`!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
           mem_word_at (w2n a) m = n2w (LENGTH bs)` by metis_tac[] >>
      `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
        (drule robust_mem_word_at_clean >> simp[]) >>
      `mload (w2n a) s = n2w (LENGTH bs)` by
        (rewrite_tac[GSYM mem_word_at_eq_mload] >>
         qpat_assum `!m. mem_agree_outside _ _ m ==> mem_word_at _ m = _` irule >>
         simp[mem_agree_outside_def]) >>
      `word_size (LENGTH bs) <= word_size nr` by
        (irule exprSimHypsTheory.word_size_monotone >> simp[]) >>
      `LENGTH bs <= 32 * word_size (LENGTH bs)` by simp[word_size_capacity] >>
      qexists_tac `LENGTH bs` >>
      gvs[eval_operand_def, val_store_size_def, type_memory_size_def,
          ptr_covers_def, GSYM vfmConstantsTheory.word_size_def]) >>
  rename1 `StringV str` >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       mem_word_at (w2n a) m = n2w (LENGTH str)` by metis_tac[] >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n a) s = n2w (LENGTH str)` by
    (rewrite_tac[GSYM mem_word_at_eq_mload] >>
     qpat_assum `!m. mem_agree_outside _ _ m ==> mem_word_at _ m = _` irule >>
     simp[mem_agree_outside_def]) >>
  `word_size (LENGTH str) <= word_size nr` by
    (irule exprSimHypsTheory.word_size_monotone >> simp[]) >>
  `LENGTH str <= 32 * word_size (LENGTH str)` by simp[word_size_capacity] >>
  qexists_tac `LENGTH str` >>
  gvs[eval_operand_def, val_store_size_def, type_memory_size_def,
      ptr_covers_def, GSYM vfmConstantsTheory.word_size_def]
QED

(* ===== Exiting with the return ===== *)

Theorem return_exit_glue[local]:
  gas_path_ptr D 0 ctx func PG G tn t 0 H tm (IntRet ir u) /\
  (!tail. RetQ v ((ee0 with gas_obs := tail) with scopes := []) (H,tm)
            (IntRet ir u)) ==>
  gas_outcome_ptr D tops (ctx,func) PG (raise (ReturnException v))
    (ee0 with gas_obs := [], t, G, tn) Q
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj1_tac >> simp[gas_summary_ptr_at_def, vyperStateTheory.raise_def] >>
  qexistsl_tac [`INR (ReturnException v)`, `ee0`, `H`, `tm`, `IntRet ir u`] >>
  gvs[fragExecTheory.exit_result_def, stmt_exit_ptr_def]
QED

Theorem intret_mem_ptr_post[local]:
  state_rel func cenv cx (ee0 with scopes := []) t /\
  typed_copy_state_frame sm off n t u /\
  cenv.ce_returns_count = 0 /\ ~cenv.ce_is_ctor /\
  cenv.ce_module = NONE /\ cenv.ce_imm_alloca = NONE /\
  stor_taint_ok cx tm (return_unlock_state cenv u with vs_inst_idx := i) /\
  (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
       val_in_memory ret_tv v (w2n bw) m) ==>
  intret_ptr_q func cenv cx ret_tv (SOME (bw,cap)) v
    ((ee0 with gas_obs := tail) with scopes := [])
    (H : string |-> num # num,tm)
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
       (return_unlock_state cenv u with vs_inst_idx := i))
Proof
  strip_tac >>
  asm_simp_tac (srw_ss()) [intret_ptr_q_def, intret_mem_q_def,
    return_unlock_state_memory] >>
  reverse conj_tac >- metis_tac[mem_agree_outside_def] >>
  irule intret_q_unlock_idx_intro >>
  simp[result_rel_def, intret_vals_match_def] >>
  qpat_x_assum `state_rel func cenv _ _ t` mp_tac >>
  qpat_x_assum `typed_copy_state_frame _ _ _ t u` mp_tac >>
  simp[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality] >>
  strip_tac >>
  simp[state_rel_gas_obs, state_rel_def, local_ptrs_rel_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
    vyperStateTheory.lookup_scopes_def, local_region_def,
    venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
  metis_tac[]
QED

(* A widened compound return: the typed copy into the caller's buffer. *)
Theorem return_widened_compound_exit[local]:
  compile_internal_return_from_env ce ty sty (Var src) (Var rpc) sa = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
  type_widens_to (get_tenv cx) sty ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type stv v /\
  expr_sim_inv ce cx env es /\ acyclic_struct_metadata ce.ce_struct_fields /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
  w2n a + type_memory_size stv < dimword (:256) /\
  w2n d + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size stv) (w2n d)
    (type_memory_size dtv) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) /\
  stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} /\
  return_unlock_state ce = return_unlock_state cenv /\
  state_rel func cenv cx (ee0 with scopes := []) s /\
  cenv.ce_returns_count = 0 /\ ~cenv.ce_is_ctor /\
  cenv.ce_module = NONE /\ cenv.ce_imm_alloca = NONE ==>
  !D tops PG Q dcap.
    gas_outcome_ptr D tops (ctx,func) PG (raise (ReturnException v))
      (ee0 with gas_obs := [], s, G, tn) Q
      (\res ee gt r. !tail. stmt_exit_ptr
         (intret_ptr_q func cenv cx dtv (SOME (d,dcap)))
         (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rpt gen_tac >>
  `value_has_type dtv v` by
    (drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `val_wf stv v /\ val_wf dtv v` by metis_tac[value_has_type_val_wf] >>
  `type_memory_bytes ce ty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  qpat_x_assum `expr_sim_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`]
    compile_internal_return_memory_widen_ptr) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `return_unlock_state ce = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule return_exit_glue >> disch_then irule >> gen_tac >>
  mp_tac (Q.INST [`t` |-> `s`, `u` |-> `t`, `sm` |-> `sa`, `off` |-> `w2n (d:256 word)`,
    `n` |-> `type_memory_size dtv`, `ret_tv` |-> `dtv`, `bw` |-> `(d:256 word)`,
    `cap` |-> `dcap`] intret_mem_ptr_post) >>
  impl_tac >- asm_rewrite_tac[] >> simp[]
QED

(* A widened bytestring return: the bytes copied into the caller's buffer
   are the live window, header plus payload. *)
Theorem return_widened_bytestring_exit[local]:
  compile_internal_return_from_env ce ty sty op (Var rpc) sa = ((),sb) /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  is_bytestring_type ty /\ is_bytestring_type ety /\
  evaluate_type (get_tenv cx) ety = SOME etv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type etv v /\ value_has_type tv v /\
  ptr_val_ok cx ety v op G tn s /\ eval_operand op s = SOME a /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  lookup_var dst s = SOME d /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  type_memory_size tv < dimword (:256) /\
  stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} /\
  return_unlock_state ce = return_unlock_state cenv /\
  state_rel func cenv cx (ee0 with scopes := []) s /\
  cenv.ce_returns_count = 0 /\ ~cenv.ce_is_ctor /\
  cenv.ce_module = NONE /\ cenv.ce_imm_alloca = NONE ==>
  !D tops PG Q dcap.
    gas_outcome_ptr D tops (ctx,func) PG (raise (ReturnException v))
      (ee0 with gas_obs := [], s, G, tn) Q
      (\res ee gt r. !tail. stmt_exit_ptr
         (intret_ptr_q func cenv cx tv (SOME (d,dcap)))
         (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rpt gen_tac >>
  mp_tac (Q.INST [`rty` |-> `ty`, `rtv` |-> `tv`] bytestring_return_window) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `op = Var _` SUBST_ALL_TAC >>
  `not_fresh_at sa src` by (first_x_assum irule >> simp[]) >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `ptr_covers G tn dst s (32 + 32 * word_size len)` by
    (irule ptr_covers_mono >> qexists_tac `type_memory_size tv` >> simp[]) >>
  `ptr_covers G tn src s 32` by
    (irule ptr_covers_mono >> qexists_tac `32 + 32 * word_size len` >> simp[]) >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`n` |-> `32 + 32 * word_size len`]
    internal_return_memory_unlock_path_ptr) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `return_unlock_state ce = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `return_unlock_state cenv t = return_unlock_state cenv t with
     vs_inst_idx := (return_unlock_state cenv t).vs_inst_idx` by
    simp[venomStateTheory.venom_state_component_equality] >>
  pop_assum (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  drule return_exit_glue >> disch_then irule >> gen_tac >>
  mp_tac (Q.INST [`t` |-> `s`, `u` |-> `t`, `sm` |-> `sa`, `off` |-> `w2n (d:256 word)`,
    `n` |-> `32 + 32 * word_size len`, `ret_tv` |-> `tv`, `bw` |-> `(d:256 word)`,
    `cap` |-> `dcap`, `i` |-> `(return_unlock_state cenv t).vs_inst_idx`]
    intret_mem_ptr_post) >>
  impl_tac >- asm_rewrite_tac[] >> simp[]
QED

(* The first two premises are the RESIDUAL (held) facts.
   1. Source/return-buffer disjointness; discharged once return_buf_frame
      carries the caller-buffer frontier.  It is asked only of a returned
      expression that has evaluated (its expr_sim_ptr post at the return
      type), and only when the store is the typed copy (source type differs
      from a compound, non-bytestring return type).
   2. A returned internal call's compiled return type is its signature's;
      discharged at the body induction from expr_body_pre (FST id = NONE)
      plus body_inv. *)
Theorem internal_return_widened_ptr_of_disjoint:
  !tops ctx PG func cx cenv ret_ty ret_tv d rpc rsz cenv' env lctx eo es.
    (!x sa sb op s0 G0 tn0 ee G tn t v sw bw cap stv.
       eo = SOME x /\ d = SOME (bw,cap) /\
       lowered_value_type cenv' x <> ret_ty /\
       ~is_word_type ret_ty /\ ~is_bytestring_type ret_ty /\
       evaluate_type (get_tenv cx) (lowered_value_type cenv' x) = SOME stv /\
       lower_value compile_expr cenv' ret_ty x sa = (op, sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv' sa /\ ~ctx_has_dalloca ctx /\
       ~cenv'.ce_is_ctor /\
       stmt_state_rel ctx func cenv' cx es s0 /\
       ghost_inv d cenv' cx es G0 tn0 s0 /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       expr_post ctx func cenv' cx x es sa sb s0 ee v op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv' cx ee G tn t /\
       ptr_val_ok cx (post_value_type cenv' x) v op G tn t /\
       ptr_buf_ok cenv' x op G t /\
       ghost_kept cenv' es sa G0 tn0 s0 G tn /\
       eval_operand op t = SOME sw ==>
       regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) cap) /\
    (!ann id args drv sig.
       eo = SOME (Call ann (IntCall id) args drv) /\
       FLOOKUP env.fn_sigs id = SOME sig ==>
       cenv'.ce_func_return_type (nsid_to_string id) = sig.ret_ty) /\
    body_inv tops ctx cenv cx /\
    cenv.ce_module = NONE /\
    cenv.ce_module_vars =
      add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
        tops 0 (add_module_var_locations tops FEMPTY) /\
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    (!off sz. cenv.ce_return_buf <> SOME (MemLoc off sz)) /\
    cenv.ce_imm_alloca = NONE /\
    (!nr nkey ut iv. cenv.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
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
  rpt gen_tac >> strip_tac >>
  Cases_on `eo` >- fs[] >>
  rename1 `Return (SOME x)` >>
  drule_all return_widened_count >> strip_tac >>
  `cenv.ce_returns_count = 0` by
    (qpat_x_assum `cenv.ce_returns_count = _` SUBST1_TAC >>
     first_assum MATCH_ACCEPT_TAC) >>
  `~is_word_type ret_ty` by
    (irule stack_count_zero_not_word >> first_assum ACCEPT_TAC) >>
  drule_all return_widened_compound_shape >> disch_tac >>
  `ret_ty <> NoneT` by fs[type_stmt_return_some_iff] >>
  `?bw cap. d = SOME (bw,cap)` by
    (Cases_on `d` >> fs[] >> metis_tac[pairTheory.pair_CASES]) >>
  `cap = type_memory_size ret_tv /\ w2n bw + cap < dimword (:256) /\
   cap + 64 < dimword (:256)` by
    (qpat_x_assum `!bw cap. d = SOME (bw,cap) ==> _`
       (qspecl_then [`bw`, `cap`] mp_tac) >> simp[]) >>
  qpat_x_assum `~!e. _` kall_tac >>
  qpat_x_assum `!ann id args drv sig. _` kall_tac >>
  pure_rewrite_tac[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `return_unlock_state cenv' = return_unlock_state cenv /\
   !nr nkey ut iv. cenv'.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut` by
    (`cenv'.ce_nonreentrant = cenv.ce_nonreentrant` by
       (fs[same_frame_def] >>
        qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
          ce_var_type := _ |> = _` (mp_tac o Q.AP_TERM `\c. c.ce_nonreentrant`) >>
        simp[]) >>
     metis_tac[return_unlock_state_cong]) >>
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
  Cases_on `compile_internal_return_from_env cenv' ret_ty
    (lowered_value_type cenv' x) val_op (Var rpc) sm` >>
  rename1 `_ = (ru,sf)` >> Cases_on `ru` >> simp[] >> strip_tac >>
  qpat_x_assum `cenv' = cenv''` SUBST_ALL_TAC >>
  qpat_x_assum `sf = sb` SUBST_ALL_TAC >>
  goalStack.print_tac "PROBE1" >>
  `cs_extends sa sm` by
    (drule bodyPtrCallCalldataTheory.lower_value_compile_expr_split >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `cs_extends sm sb` by
    (qspec_then `sm` mp_tac
      (Q.SPECL [`cenv''`, `ret_ty`, `lowered_value_type cenv'' x`, `val_op`,
        `Var rpc`] (cj 2 stmtLoweringMonoTheory.ci_mono_return_helpers)) >>
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
  goalStack.print_tac "PROBE2" >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (fn th => assume_tac th >>
              strip_assume_tac (REWRITE_RULE [expr_post_def] th)) >>
  `?a. eval_operand val_op t = SOME a` by metis_tac[expr_val_rel_def] >>
  `op_taint tn (Var rpc) = {} /\ stor_taint_ok cx tn t` by
    metis_tac[ghost_inv_def] >>
  `?pc. lookup_var rpc t = SOME pc` by
    metis_tac[ghost_inv_def, ret_pc_ok_def] >>
  `~t.vs_call_ctx.cc_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  `?dst slot. cenv''.ce_return_buf = SOME (PtrVar (Var dst) slot) /\
     lookup_var dst t = SOME bw /\ ptr_covers G tn dst t cap` by
    metis_tac[ghost_inv_def, return_buf_ptr_def] >>
  `not_fresh_at sm rpc /\ not_fresh_at sm dst` by
    (mp_tac (Q.SPECL [`cenv''`, `ret_ty`, `x`, `sa`]
       (cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >>
     asm_rewrite_tac[pairTheory.SND, exprLoweringPropsTheory.ci_mono_def] >>
     strip_tac >> conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> metis_tac[]) >>
  `!z. val_op = Var z ==> not_fresh_at sm z` by
    metis_tac[compile_lower_value_var] >>
  `state_rel func cenv cx (ee0 with scopes := []) t` by
    (irule constructor_exit_state_rel >> qexists_tac `cenv''` >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `~cenv.ce_is_ctor /\ ~cenv''.ce_is_ctor` by metis_tac[same_frame_is_ctor] >>
  `cenv''.ce_returns_count = 0` by
    (fs[same_frame_def] >>
     qpat_x_assum `_ with <| ce_vars := _; ce_dynarray_capacity := _;
       ce_var_type := _ |> = _`
       (mp_tac o Q.AP_TERM `\c. c.ce_returns_count`) >> simp[]) >>
  `?etv. evaluate_type (get_tenv cx) (expr_type x) = SOME etv /\
         value_has_type etv v` by
    (irule return_value_typed >> metis_tac[]) >>
  goalStack.print_tac "PROBE3" >>
  `type_widens_to (get_tenv cx) (expr_type x) ret_ty` by
    (fs[type_stmt_return_some_iff, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >> metis_tac[]) >>
  Cases_on `is_bytestring_type ret_ty`
  >- (`is_bytestring_type (expr_type x)` by
        metis_tac[typed_copy_bytestring_source] >>
      `value_has_type ret_tv v` by
        (mp_tac (Q.INST [`tenv` |-> `get_tenv cx`, `t` |-> `expr_type x`,
           `u` |-> `ret_ty`, `tv` |-> `etv`] type_widens_to_value_has_type) >>
         simp[]) >>
      `ptr_val_ok cx (expr_type x) v val_op G tn t` by gs[] >>
      irule return_widened_bytestring_exit >>
      goalStack.print_tac "PROBE4" >>
      cheat) >>
  goalStack.print_tac "PROBE5" >>
  qpat_x_assum `is_bytestring_type ret_ty \/ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv'' x) = SOME stv /\
         value_has_type stv v` by
    (irule return_compound_lowered_typed >> metis_tac[]) >>
  `type_memory_size stv <> 0` by
    (strip_tac >>
     mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,
       `sty` |-> `lowered_value_type cenv'' x`, `dty` |-> `ret_ty`,
       `dtv` |-> `ret_tv`] type_widens_to_zero_layout) >>
     asm_rewrite_tac[]) >>
  `type_memory_bytes cenv'' (lowered_value_type cenv'' x) =
     type_memory_size stv` by metis_tac[expr_sim_inv_memory_size] >>
  `?src. val_op = Var src /\ lookup_var src t = SOME a /\
     ptr_covers G tn src t (type_memory_size stv)` by
    (qpat_x_assum `ptr_buf_ok _ _ _ _ _` (mp_tac o SRULE [ptr_buf_ok_def]) >>
     disch_then (qspec_then `a` mp_tac) >> asm_simp_tac std_ss [] >>
     strip_tac >> rename1 `FLOOKUP G z = SOME (b,sz)` >> qexists_tac `z` >>
     gvs[ptr_covers_def, eval_operand_def]) >>
  `not_fresh_at sm src` by metis_tac[] >>
  `~is_word_type (lowered_value_type cenv'' x) /\
   ~is_bytestring_type (lowered_value_type cenv'' x)` by
    metis_tac[type_widens_to_def, arg_type_fits_word_type,
              arg_type_fits_bytestring_target] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  `w2n a + type_memory_size stv < dimword (:256)` by
    (qspecl_then [`func`, `cenv''`, `cx`, `lowered_value_type cenv'' x`, `sa`,
       `sm`, `ee0`, `v`, `val_op`, `t`, `stv`, `a`, `ctx`] mp_tac
       expr_val_at_bound >>
     impl_tac >- gs[] >> simp[]) >>
  `acyclic_struct_metadata cenv''.ce_struct_fields` by
    (drule_all body_inv_same_frame >> simp[body_inv_def]) >>
  goalStack.print_tac "PROBE6" >>
  cheat
QED

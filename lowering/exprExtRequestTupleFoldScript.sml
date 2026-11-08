(* Fixed-root positional tuple fold.  Captures stay before the tuple ALLOCA. *)
Theory exprExtRequestTupleFold
Ancestors
  exprExtRequestTupleCapturedHead exprExtRequestStrongCapture
  exprExtRequestHistoryCompose exprExtRequestHistory exprLoweringProps
  exprLowering compileEnv vyperInterpreter vyperState valueEncodingProps
  valueTypingMemoryProps gasSummary fragGasMode fragExec

(* The public compiler theory keeps its store-fold monotonicity fact local. *)
Theorem extrequest_store_values_mono:
  !cells off sa.
    ci_mono sa (SND (compile_extcall_store_values cenv cells buf off sa))
Proof
  Induct >> simp[compile_extcall_store_values_def, comp_return_def, ci_mono_refl] >>
  qx_gen_tac `cell` >> PairCases_on `cell` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `ci_mono sa cs'` by
    (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sa`] mp_tac
       ci_mono_emit_op >> simp[]) >>
  `ci_mono cs' cs''` by
    (qspecl_then [`cenv`, `cell0`, `cs'`] mp_tac
       ci_mono_unwrap_value >> simp[]) >>
  `ci_mono cs'' cs'³'` by
    (qpat_x_assum `(if is_word_type _ then _ else _) _ = _` mp_tac >>
     Cases_on `is_word_type cell1` >> simp[]
     >- (strip_tac >> qspecl_then [`MSTORE`, `[dst;v]`, `cs''`]
           mp_tac ci_mono_emit_void >> simp[]) >>
     Cases_on `is_bytestring_type cell1` >> simp[]
     >- (strip_tac >> qspecl_then [`v`, `dst`, `cs''`]
           mp_tac ci_mono_compile_store_bytestring >> simp[]) >>
     strip_tac >> qspecl_then
       [`MCOPY`, `[dst;v;Lit (n2w (type_memory_bytes cenv cell1))]`, `cs''`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  first_x_assum (qspecl_then [`off + type_memory_bytes cenv cell1`, `cs'³'`] mp_tac) >>
  strip_tac >> fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

(* Each aligned cell retains its capture at the fixed pre-allocation root. *)
Definition extrequest_tuple_cell_def:
  extrequest_tuple_cell ctx func cenv cx eb cb tb ee (e,r,vv,ty,tv,v) <=>
    extrequest_strong_capture ctx func cenv cx e r vv eb cb tb /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
    (!stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
       ~is_word_type (expr_type e) ==>
       type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
       type_memory_size stv < 2**64) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    (ty = expr_type e \/ is_bytestring_type ty /\ is_bytestring_type (expr_type e)) /\
    read_result cx r ee = (INL v,ee) /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256)
End

Theorem extrequest_tuple_store_fold:
  !cells off sm sb s.
    EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells /\
    compile_extcall_store_values cenv
      (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) buf off sm = ((),sb) /\
    stmt_state_rel ctx func cenv cx eb tb /\
    stmt_state_rel ctx func cenv cx ee s /\
    extrequest_history_frame cenv cx eb cb tb ee sm s /\
    cb.cs_next_id <= live /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ee.gas_obs = [] /\ safe_operand cb buf /\ eval_operand buf s = SOME w /\
    FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\ live < sm.cs_next_id /\
    tuple_base <= w2n w + off /\
    w2n w + off + SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) <=
      tuple_base + sz /\
    tuple_base + sz < dimword (:256) /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
       regions_disjoint tuple_base sz b len) /\
    (cenv.ce_is_ctor ==> !name itv iv io.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
       regions_disjoint io (type_memory_size itv) tuple_base sz) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel ctx func cenv cx ee q /\
      tuple_in_memory (MAP (\(e,r,vv,ty,tv,v). v) cells)
        (MAP (\(e,r,vv,ty,tv,v). tv) cells) (w2n w + off) q.vs_memory /\
      extrequest_history_frame cenv cx eb cb tb ee sb q /\
      FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
      (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
         regions_disjoint a k (w2n w + off)
           (SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells)) ==>
         mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct
  >- (simp[compile_extcall_store_values_def, comp_return_def] >>
      rpt strip_tac >> qexists_tac `s` >>
      simp[valueEncodingTheory.val_in_memory_def, gas_marked_path_def] >>
      irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  qx_gen_tac `cell` >> PairCases_on `cell` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  rename1 `extrequest_tuple_cell _ _ _ _ _ _ _ _ (e,r,vv,ty,tv,v)` >>
  qpat_x_assum `(\(dst,st). _) _ = _` mp_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  strip_tac >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  rename1 `unwrap_value cenv vv sn = (op,su)` >>
  rename1 `(if is_word_type ty then _ else _) su = ((),sh)` >>
  `ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sh /\ ci_mono sh sb` by
    (rpt conj_tac
     >- (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`]
           mp_tac ci_mono_emit_op >> simp[])
     >- (qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[])
     >- (qpat_x_assum `(if is_word_type ty then _ else _) su = _` mp_tac >>
         Cases_on `is_word_type ty` >> simp[]
         >- (strip_tac >> qspecl_then [`MSTORE`, `[dst;op]`, `su`]
               mp_tac ci_mono_emit_void >> simp[]) >>
         Cases_on `is_bytestring_type ty` >> simp[]
         >- (strip_tac >> qspecl_then [`op`, `dst`, `su`]
               mp_tac ci_mono_compile_store_bytestring >> simp[]) >>
         strip_tac >> qspecl_then
           [`MCOPY`, `[dst;op;Lit (n2w (type_memory_bytes cenv ty))]`, `su`]
           mp_tac ci_mono_emit_void >> simp[]) >>
     qspecl_then [`MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells`,
       `off + type_memory_bytes cenv ty`, `sh`] mp_tac
       extrequest_store_values_mono >> simp[]) >>
  `fn_has_code sm su func /\ fn_has_code su sh func /\ fn_has_code sh sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  qpat_x_assum `extrequest_tuple_cell _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[extrequest_tuple_cell_def, pairTheory.pair_case_thm] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `IS_SOME _`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `extrequest_strong_capture _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[extrequest_strong_capture_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ec tc` by fs[loweringPostsTheory.vv_post_def] >>
  `extrequest_history_frame cenv cx ec sc tc ee sm s` by
    metis_tac[extrequest_history_frame_trans] >>
  `sc.cs_next_id <= live` by fs[extrequest_history_frame_def] >>
  `tuple_base <= w2n (w + n2w off) /\
   w2n (w + n2w off) + type_memory_size tv <= tuple_base + sz` by decide_tac >>
  `cenv.ce_is_ctor ==> !name itv iv io.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv)
       (w2n (w + n2w off)) (type_memory_size tv)` by
    (rpt strip_tac >> fs[compileEnvTheory.regions_disjoint_def] >>
     first_x_assum (drule_all_then mp_tac) >> decide_tac) >>
  drule_all extrequest_tuple_captured_head >> strip_tac >>
  suspend "tail"
QED

Resume extrequest_tuple_store_fold[tail]:
  rename1 `gas_marked_exec _ _ _ _ _ _ _ (OK h)` >>
  `extrequest_history_frame cenv cx eb cb tb ee sh h` by metis_tac[] >>
  `eval_operand buf h = SOME w` by
    (Cases_on `buf` >> gvs[venomStateTheory.eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
     fs[extrequest_history_frame_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!name b len. local_region cenv ee.scopes h name b len ==>
       regions_disjoint tuple_base sz b len` by
    (rpt strip_tac >>
     `local_region cenv eb.scopes tb name b len` by
       metis_tac[extrequest_history_local_regions] >>
     metis_tac[extrequest_history_local_regions]) >>
  `live < sh.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  first_x_assum (qspecl_then [`off + type_memory_bytes cenv ty`, `sh`, `sb`, `h`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "finish"
QED

Resume extrequest_tuple_store_fold[finish]:
  rename1 `gas_marked_path F ctx func h 0 (OK q)` >>
  `mem_bytes_at (w2n w + off) (type_memory_size tv) q.vs_memory =
   mem_bytes_at (w2n w + off) (type_memory_size tv) h.vs_memory` by
    (first_assum irule >> simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `val_in_memory tv v (w2n w + off) q.vs_memory` by
    (metis_tac[val_in_memory_mem_agree, arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `q` >>
  conj_tac
  >- (`gas_marked_path F ctx func s 0 (OK h)` by fs[gas_marked_exec_def] >>
      drule_all gas_marked_path_then >> simp[]) >>
  simp[valueEncodingTheory.val_in_memory_def] >>
  conj_tac >- (metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  suspend "windows"
QED

Resume extrequest_tuple_store_fold[windows]:
  rpt strip_tac >>
  `mem_bytes_at a k q.vs_memory = mem_bytes_at a k h.vs_memory` by
    (first_assum irule >> simp[] >>
     fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at a k h.vs_memory = mem_bytes_at a k s.vs_memory` by
    (first_assum irule >> simp[] >>
     fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Finalise extrequest_tuple_store_fold

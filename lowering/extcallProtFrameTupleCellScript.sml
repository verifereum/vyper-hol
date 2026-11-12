Theory extcallProtFrameTupleCell
Ancestors
  extcallProtFrameTupleHead extcallProtFrameJointUnwrap
  exprExtRequestTupleFold exprExtRequestStrongCapture exprExtRequestHistoryCompose
  exprExtRequestHistory exprLoweringProps exprLowering compileEnv
  vyperInterpreter vyperState valueEncodingProps valueTypingMemoryProps
  gasSummary fragGasMode fragExec abiDecodeStaticProps loweringStateRelDefs valueEncodingDefs

Theorem extcall_tuple_cell_store_protected:
  extrequest_tuple_cell ctx func cenv cx eb cb tb ee (e,r,vv,ty,tv,v) /\
  compile_extcall_store_values cenv [(vv,ty)] buf off sm = ((),sb) /\
  stmt_state_rel ctx func cenv cx eb tb /\
  stmt_state_rel ctx func cenv cx ee s /\
  extrequest_history_frame cenv cx eb cb tb ee sm s /\
  cb.cs_next_id <= live /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ee.gas_obs = [] /\ safe_operand sm buf /\ eval_operand buf s = SOME w /\
  FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\ live < sm.cs_next_id /\
  tuple_base <= w2n w + off /\
  w2n w + off + type_memory_size tv <= tuple_base + sz /\
  tuple_base + sz < dimword (:256) /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    regions_disjoint tuple_base sz b len) /\
  (cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) tuple_base sz) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_state_rel ctx func cenv cx ee q /\
    val_in_memory tv v (w2n w + off) q.vs_memory /\
    extrequest_history_frame cenv cx eb cb tb ee sb q /\
    FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
    (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
      regions_disjoint a k (w2n w + off) (type_memory_size tv) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
      lookup_var x q = SOME z) /\
    (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
      FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
      mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >>
  qpat_x_assum `(\(dst,st). _) _ = _` mp_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  strip_tac >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  rename1 `unwrap_value cenv vv sn = (op,su)` >>
  `ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    (rpt conj_tac
     >- (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`]
           mp_tac ci_mono_emit_op >> simp[])
     >- (qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
     qpat_x_assum `(if is_word_type ty then _ else _) su = _` mp_tac >>
     Cases_on `is_word_type ty` >> simp[]
     >- (strip_tac >> qspecl_then [`MSTORE`, `[dst;op]`, `su`]
           mp_tac ci_mono_emit_void >> simp[]) >>
     Cases_on `is_bytestring_type ty` >> simp[]
     >- (strip_tac >> qspecl_then [`op`, `dst`, `su`]
           mp_tac ci_mono_compile_store_bytestring >> simp[]) >>
     strip_tac >> qspecl_then
       [`MCOPY`, `[dst;op;Lit (n2w (type_memory_bytes cenv ty))]`, `su`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sm su func /\ fn_has_code su sb func /\ fn_has_code sn su func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule w2n_add_n2w_lt >> decide_tac) >>
  suspend "capture"
QED

Resume extcall_tuple_cell_store_protected[capture]:
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
    (rpt strip_tac >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     first_x_assum (drule_all_then mp_tac) >> decide_tac) >>
  mp_tac (Q.INST [`stv` |-> `x`] extcall_tuple_captured_head_protected) >>
  (impl_tac >- (simp[] >>
    (conj_tac >- metis_tac[]) >>
    (conj_tac >- gvs[]) >>
    (conj_tac >- metis_tac[]) >>
    rpt strip_tac >>
    mp_tac (Q.INST [`sb` |-> `su`, `M` |-> `original`]
      extcall_joint_unwrap_read_protected) >> simp[] >>
    (impl_tac >- metis_tac[]) >> simp[])) >>
  strip_tac >>
  suspend "finish"
QED

Resume extcall_tuple_cell_store_protected[finish]:
  rename1 `gas_marked_exec _ _ _ _ _ _ _ (OK q)` >>
  qexists_tac `q` >> simp[] >>
  (conj_tac >-
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[gas_marked_path_def])) >>
  (conj_tac >- gvs[]) >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

Finalise extcall_tuple_cell_store_protected

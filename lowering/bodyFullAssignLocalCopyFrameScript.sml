(* Right-hand side and copy frames for local memory assignments. *)
Theory bodyFullAssignLocalCopyFrame
Ancestors
  arithmetic assignTuplePtrLocalFixedCopy blockPrefixEquiv[qualified,ignore_grammar]
  bodyCopyMemoryBase bodyFullAllocGeneric bodyFullHashKeccakFixed bodyFullUnwrap
  bodyPtrIfExpBytesPost bodyPtrIfExpCopyHeader bodySimFull bytesCopyCode compileEnv context
  emitHelperProps exprLowering exprLoweringProps exprOperandVar exprSimBufferStore
  exprSimDefs exprSimMemorySource[qualified,ignore_grammar] exprSimUnwrap finite_map
  fragExec fragGasCopyLoop fragGasMode fragGasOrigin fragGasOriginPtr fragGasSeqPtr
  fragGasCopySeqLiftProps
  fragGasSeqPtrContext gasExemptCert gasOutcomeFullCompose
  gasShadowCompile[qualified,ignore_grammar] gasShadowState haltExitProj list loweringPosts
  pair placeMemoryCopyEffect placeMemoryTypedPrimitive[qualified,ignore_grammar] pred_set
  ptrDiscipline reasonTupleCopyPtr rich_list stmtSimProps sum
  valueCopy[qualified,ignore_grammar] venomExecSemantics venomInst venomState
  vyperEvalExprPreservesScopesDom[qualified,ignore_grammar] vyperStorageFootprint
  vyperStorageTrace words
Libs
  monadsyntax

Theorem body_assign_local_memory_rhs_frontier:
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx (expr_type e) e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sV) /\
  unwrap_value cenv vv sV = (op,sB) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sB shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sB func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es, s0, G0, tn0)
    (\H res ee G tn u. (?v. res = INL v /\
       expr_post H ctx func cenv cx e es sa sB s0 ee v op u /\
       expr_store_bound cx (post_value_type cenv e) v op u /\
       u.vs_current_bb = sB.cs_current_bb /\
       u.vs_inst_idx = LENGTH sB.cs_current_insts /\
       alloca_history func u /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       s0.vs_alloca_next <= u.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
       ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
       (~is_word_type (post_value_type cenv e) ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
                 eval_operand op u = SOME w ==>
                 type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= u.vs_alloca_next))
    (\H res ee gt r.
       expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (vv',shadow_sV)` >>
  simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `vv' = vv /\ gas_shadow_state sV shadow_sV` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
       (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  gvs[] >>
  qpat_assum `compile_expr cenv _ e sa = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sV = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sV = _`
    (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.unwrap_value_extends) >>
  `fn_has_code sa sV func /\ fn_has_code sV sB func` by
    (qspecl_then [`sa`,`sV`,`sB`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sV shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sV`,`shadow_sb`,`shadow_func`] mp_tac
       fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sV` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sV x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule exprSimMemorySourceTheory.forced_expr_admissible_raw >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sV`,`shadow_sa`,`shadow_sV`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt gen_tac >> Cases_on `res` >>
      simp[expr_exit_def] >>
      ONCE_REWRITE_TAC [
        INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >>
      simp[]) >>
  suspend "read"
QED

Resume body_assign_local_memory_rhs_frontier[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sV s0 ee tv vv s /\
       ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  mp_tac (Q.INST [`sb` |-> `sV`, `sc` |-> `sB`, `G` |-> `G1`,
    `tn` |-> `tn1`, `Gi` |-> `G0`, `ti` |-> `tn0`, `sm` |-> `sV`,
    `ty` |-> `expr_type e`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL unwrap_value_origin_ptr)) >>
  (impl_tac >- simp[]) >>
  suspend "unwrap"
QED

Resume body_assign_local_memory_rhs_frontier[unwrap]:
  strip_tac >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[exprSimMemorySourceTheory.read_result_gas_obs] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee z` by fs[expr_post_def] >>
  drule stmt_state_rel_allocas_below_fmp >> simp[]
QED

Finalise body_assign_local_memory_rhs_frontier

Theorem body_assign_local_memory_bytes_copy_effect:
  compile_store_bytestring (Var xs) (Var xd) sa = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
     val_in_memory stv v (w2n sw) m) /\
  n = 32 + 32 * ((len+31) DIV 32) /\
  len+31 < dimword(:256) /\ n < dimword(:256) /\ n <= type_memory_size dtv /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs u = SOME sw /\ lookup_var xd u = SOME dw /\
  ptr_covers G tn xs u n /\ ptr_covers G tn xd u n /\
  w2n sw + n <= u.vs_alloca_next /\ w2n dw + n <= u.vs_alloca_next /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code sa sb func /\ ~u.vs_halted /\
  u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sa sb u t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all robust_bytestring_header >> strip_tac >>
  `eval_operand (Var xs) u = SOME sw /\ eval_operand (Var xd) u = SOME dw /\
   (!x. Var xs = Var x \/ Var xd = Var x ==> not_fresh_at sa x)` by
    (simp[eval_operand_def] >> rpt strip_tac >> gvs[]) >>
  `n = 32 + 32 * word_size len` by simp[vfmConstantsTheory.word_size_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) u` by suspend "safe" >>
  drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    suspend "prefix" >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `(sf with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u` by
    suspend "run_frame" >>
  drule_all bytestring_copy_effects >> strip_tac >>
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n dw) m` by
    (rpt strip_tac >> irule bytestring_copy_robust_destination >> metis_tac[]) >>
  qabbrev_tac `t = sf with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sa sb)` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,Gf,tnf)` by
    simp[Abbr `t`] >>
  `gas_marked_path F ctx func u 0 (OK t)` by suspend "marked" >>
  `typed_copy_effect ctx func sa sb u t (w2n dw) n` by suspend "effect" >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  simp[Abbr `t`,blockPrefixEquivTheory.lookup_var_set_inst_idx,
       IgnAsm `Abbrev (t = _)`] >>
  irule typed_copy_effect_enlarge >> qexistsl_tac [`w2n dw`,`n`] >> gvs[]
QED

Resume body_assign_local_memory_bytes_copy_effect[safe]:
  `32 + 32 * word_size len < dimword(:256) /\
   w2n sw + (32 + 32 * word_size len) <= u.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= u.vs_alloca_next` by metis_tac[] >>
  drule_all compile_store_bytestring_body_mem_ok >> simp[]
QED

Resume body_assign_local_memory_bytes_copy_effect[prefix]:
  qpat_x_assum `fn_has_code sa sb func` mp_tac >> simp[fn_has_code_def] >>
  strip_tac >> goal_assum drule >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]
QED

Resume body_assign_local_memory_bytes_copy_effect[run_frame]:
  `32 + 32 * word_size len < dimword(:256)` by metis_tac[] >>
  drule_all buffer_store_bytestring_run >> strip_tac >> gvs[]
QED

Resume body_assign_local_memory_bytes_copy_effect[marked]:
  irule gas_marked_path_from_mem >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK t,_,_)` (qspec_then `ARB` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def]
QED

Resume body_assign_local_memory_bytes_copy_effect[effect]:
  simp[typed_copy_effect_def] >>
  qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _|>) = u` mp_tac >>
  simp[Abbr `t`,venom_state_component_equality,
       blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> simp[]) >>
  simp[placeMemoryTypedPrimitiveTheory.mcopy_memory_length]
QED

Finalise body_assign_local_memory_bytes_copy_effect

Theorem body_assign_local_memory_flat_copy_effect:
  compile_copy_memory (Var xd) (Var xs) n sa = ((),sb) /\
  0 < n /\ n = type_memory_size dtv /\
  val_wf dtv v /\ val_footprint dtv v <= n /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
       val_in_memory dtv v (w2n sw) m) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs u = SOME sw /\ lookup_var xd u = SOME dw /\
  ptr_covers G tn xs u n /\ ptr_covers G tn xd u n /\
  w2n sw + n < dimword(:256) /\ w2n dw + n < dimword(:256) /\
  w2n sw + n <= u.vs_alloca_next /\ w2n dw + n <= u.vs_alloca_next /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~u.vs_halted /\
  u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,Gf,tf)) /\
    typed_copy_effect ctx func sa sb u t (w2n dw) (type_memory_size dtv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
       val_in_memory dtv v (w2n dw) m) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < dimword(:256)` by decide_tac >>
  `w2n (n2w n : 256 word) = n` by simp[] >>
  `eval_operand (Var xs) u = SOME sw /\ eval_operand (Var xd) u = SOME dw /\
   eval_operand (Lit (n2w n)) u = SOME (n2w n)` by simp[eval_operand_def] >>
  `emit_void MCOPY [Var xd; Var xs; Lit (n2w n)] sa = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) u` by
    (drule_all compile_copy_memory_body_mem_ok >> simp[]) >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP u.vs_inst_idx bb.bb_instructions)` by
    suspend "prefix" >>
  qabbrev_tac `sf = mcopy (w2n dw) (w2n sw) n u` >>
  qabbrev_tac `tnf = step_taint (mk_inst sa.cs_next_id MCOPY
    [Var xd; Var xs; Lit (n2w n)] []) u sf tn` >>
  qabbrev_tac `t = sf with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sa sb)` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tn) [] (OK t,G,tnf)` by
    suspend "path" >>
  `gas_marked_path F ctx func u 0 (OK t)` by suspend "marked" >>
  `typed_copy_effect ctx func sa sb u t (w2n dw) (type_memory_size dtv)` by
    suspend "effect" >>
  qexistsl_tac [`t`,`G`,`tnf`] >> simp[] >>
  conj_tac >- suspend "robust" >>
  suspend "ghost"
QED

Resume body_assign_local_memory_flat_copy_effect[prefix]:
  qpat_x_assum `fn_has_code sa sb func` mp_tac >> simp[fn_has_code_def] >>
  strip_tac >> goal_assum drule >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]
QED

Resume body_assign_local_memory_flat_copy_effect[path]:
  gen_tac >>
  `~ctx_has_dalloca (ctx with ctx_functions := [])` by simp[ctx_has_dalloca_def] >>
  `op_taint tn (Lit (n2w n)) = {}` by simp[op_taint_def] >>
  `inst_seq_ptr D 0 (ctx with ctx_functions := []) func PG G tn
     (emitted_insts sa sb) u G tnf /\ run_inst_seq (emitted_insts sa sb) u = OK sf` by
    (mp_tac (Q.SPECL [`D`,`ctx with ctx_functions := []`,`func`,`PG`,`G`,`tn`,`u`,
                       `sa.cs_next_id`,`xd`,`xs`,`Lit (n2w n)`,`sw`,`dw`,`n2w n`]
       assignTuplePtrLocalFixedCopyTheory.mcopy_operand_seq_ptr) >>
     simp[Abbr `tnf`, Abbr `sf`] >> gvs[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) u G tnf` by
    (irule fragGasSeqPtrContextTheory.inst_seq_ptr_restore_ctx >>
     simp[mk_inst_def,is_terminator_def,is_alloca_op_def]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) u G tnf` by
    ((irule fragGasCopySeqLiftPropsTheory.inst_seq_ptr_lower_bound_transport >>
     simp[mk_inst_def] >> qexists_tac `0` >> simp[] >> (gvs[mk_inst_def, fragGasCopySeqLiftPropsTheory.inst_seq_ptr_lower_bound_transport]))) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def,is_terminator_def] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post z. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre u = OK z ==> unitTransformDefs$dalloca_no_wrap i z)` by
    simp[APPEND_EQ_CONS, mk_inst_def, memSafeRunTheory.dalloca_no_wrap_non_dalloca] >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[Abbr `t`,mk_inst_def]
QED

Resume body_assign_local_memory_flat_copy_effect[marked]:
  irule gas_marked_path_from_mem >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def]
QED

Resume body_assign_local_memory_flat_copy_effect[effect]:
  simp[typed_copy_effect_def] >>
  simp[Abbr `t`,IgnAsm `Abbrev (t = _)`,
       blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  `!a len. a + len <= w2n dw \/ w2n dw + n <= a ==>
      mem_bytes_at a len sf.vs_memory = mem_bytes_at a len u.vs_memory` by
    (rpt strip_tac >> (metis_tac[valueCopyTheory.mem_bytes_at_mcopy_disjoint])) >>
  `LENGTH u.vs_memory <= LENGTH sf.vs_memory` by
    simp[Abbr `sf`,placeMemoryTypedPrimitiveTheory.mcopy_memory_length] >>
  qpat_x_assum `n = type_memory_size dtv` SUBST_ALL_TAC >>
  gvs[] >>
  qpat_assum `!a len. a + len <= w2n dw \/ type_memory_size dtv + w2n dw <= a ==>
        mem_bytes_at a len sf.vs_memory = mem_bytes_at a len u.vs_memory`
    (SUBST1_TAC o EQT_INTRO) >>
  simp[Abbr `sf`,IgnAsm `Abbrev (sf = _)`,mcopy_def,write_memory_with_expansion_def,
       lookup_var_def,venom_state_component_equality]
QED

Resume body_assign_local_memory_flat_copy_effect[robust]:
  simp[Abbr `t`,IgnAsm `Abbrev (t = _)`] >>
  qx_gen_tac `m` >> strip_tac >>
  irule reasonTupleCopyPtrTheory.reason_mcopy_robust_representation >>
  (metis_tac[])
QED

Resume body_assign_local_memory_flat_copy_effect[ghost]:
  `tnf = step_taint (mk_inst sa.cs_next_id MCOPY [Var xd; Var xs; Lit (n2w n)] [])
     u (mcopy (w2n dw) (w2n sw) n u) tn` by simp[Abbr `tnf`,Abbr `sf`] >>
  drule_all assignTuplePtrLocalFixedCopyTheory.mcopy_operand_taint_frames_ptr >>
  strip_tac >>
  simp[Abbr `t`,IgnAsm `Abbrev (t = _)`,Abbr `sf`,op_taint_def,
       mcopy_def,write_memory_with_expansion_def,lookup_var_def]
QED

Finalise body_assign_local_memory_flat_copy_effect

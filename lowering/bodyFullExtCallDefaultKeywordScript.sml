(* Join the nonword default's store to the child VV endpoint. *)
Theory bodyFullExtCallDefaultKeyword
Ancestors
  bodyFullShadowBodyInv
  bodyFullExtCallDefaultPrefix bodyFullExtCallDefaultBytesStore
  bodyFullExtCallDefaultCopy bodyFullPreds bodySimFull gasOutcomeFullCompose
  stateRelProj bodyFullStructLitFrames bodyFullPathHistory
  abiEncodeArgsCase abiEncodeMaterialize aggregateEvaluatedLayout
  gasShadowCompile stmtLoweringMono exprOperandVar exprSimSource exprSimHyps
  exprSimMemorySource exprSimIfExpWidenedPhysicalType exprSimPtrLiteralBuffer
  targetPureSourceFrame placeStoreDynPrepare stmtSimProps valueCopyBytes
  vyperEvalExprPreservesScopesDom gasExemptCert typedMemoryCopy words venomState
  compileEnv exprLowering exprLoweringProps fragExec loweringPosts exprSimHypsDefs
  loweringShapeDefs bodyPtrDefs
  bodyPtrIfExpBytesCounted bodyCopyMemory bodyDeclMemoryCounted abiTupleProps
(* A robust value over a covering window has the memory pointer post. *)
Theorem default_memory_post[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ val_wf tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n w) m) /\
  (type_memory_size tv <> 0 ==>
     ?x. op = Var x /\ ptr_covers G tn x s (type_memory_size tv)) ==>
  ptr_mem_ok cx ty v op G tn s
Proof
  strip_tac >> simp[bodyPtrDefsTheory.ptr_mem_ok_def] >> strip_tac >>
  `type_memory_size tv <> 0` by
    (drule exprSimPropsTheory.val_footprint_le >> decide_tac) >>
  first_x_assum drule >> strip_tac >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, eval_operand_def] >>
  drule exprSimPropsTheory.val_store_size_le >> decide_tac
QED

(* Both stores write within the allocated destination capacity. *)
val default_store_inputs = ``
  compile_store_memory ce src (Var dst) ty ty a = ((),b) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at a x) /\ not_fresh_at a dst /\
  eval_operand src s = SOME sw /\ lookup_var dst s = SOME dw /\
  ptr_mem_ok cx ty v src G tn s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n sw) m) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\
  (type_memory_size tv <> 0 ==>
     (?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
     w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts``;

val default_store_post = ``
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tm)) /\
    (!mem. mem_agree_outside tm.t_mem u.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem) /\
    lookup_var dst u = SOME (dw:256 word) /\
    typed_copy_state_frame a (w2n dw) (type_memory_size tv) s u /\
    (!x. not_fresh_at a x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    u.vs_current_bb = b.cs_current_bb /\ u.vs_current_bb = s.vs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted``;

Theorem copied_head_store_observed:
  ^default_store_inputs /\
  (!u. same_blocks a b /\
       b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
       EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                   ~is_terminator i.inst_opcode) (emitted_insts a b) /\
       run_inst_seq (emitted_insts a b) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
       u.vs_inst_idx = LENGTH b.cs_current_insts ==> R s u) ==>
  ?u Gf tm. R s u /\ ^default_store_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `same_blocks a b /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) (emitted_insts a b)` by
    (Cases_on `is_bytestring_type ty`
     >- (`compile_store_bytestring src (Var dst) a = ((),b)` by
           fs[contextTheory.compile_store_memory_def] >>
         drule exprSimBufferStoreTheory.buffer_store_bytestring_shape >> strip_tac >>
         drule compile_store_bytestring_code >> simp[listTheory.EVERY_CONJ]) >>
     `compile_copy_memory (Var dst) src (type_memory_bytes ce ty) a = ((),b)` by
       fs[contextTheory.compile_store_memory_def] >>
     drule compile_copy_memory_extends >> strip_tac >>
     drule copy_memory_body_code >>
     drule compile_copy_memory_no_gas >> simp[listTheory.EVERY_CONJ]) >>
  Cases_on `is_bytestring_type ty`
  >- (`type_memory_size tv <> 0` by
        (drule_all bytestring_type_value >> strip_tac >>
         gvs[valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def]) >>
      qpat_x_assum `type_memory_size tv <> 0 ==> _` (strip_assume_tac o UNDISCH) >>
      gvs[eval_operand_def] >>
      `w2n sw + type_memory_size tv <= s.vs_alloca_next /\
       w2n dw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
      drule_all extcall_default_bytes_store_capacity_joint_exact >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      `R s u` by (first_x_assum irule >> simp[]) >>
      qexistsl_tac [`u`,`Gf`,`tm`] >> simp[] >>
      conj_tac
      >- (simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
          conj_tac >- gvs[venom_state_component_equality] >>
          rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      gvs[venom_state_component_equality]) >>
  `type_memory_size tv <> 0 ==>
     (?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
     ptr_covers G tn dst s (type_memory_size tv) /\
     w2n sw + type_memory_size tv <= s.vs_alloca_next /\
     w2n dw + type_memory_size tv <= s.vs_alloca_next /\
     s.vs_alloca_next < dimword (:256)` by simp[] >>
  drule_all extcall_default_copy_capacity_joint_exact >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `R s u` by (first_x_assum irule >> simp[]) >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> asm_rewrite_tac[] >>
  fs[same_blocks_def]
QED

Theorem default_store_dispatch[local]:
  ^default_store_inputs ==> ?u Gf tm. ^default_store_post
Proof
  disch_tac >>
  mp_tac (BETA_RULE (Q.INST [`R` |-> `\(s:venom_state) (u:venom_state). T`]
                    copied_head_store_observed)) >>
  simp[]
QED

val extcall_materialized_post = ``
    \(H : (bool # bytes32 # type_value) list # num list) (res : value + exception) ee G tn t.
      ?v. res = INL v /\ dt = lowered_value_type cenv e /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ptr_val_ok cx dt v op G tn t /\ ptr_mem_ok cx dt v op G tn t /\
      ptr_buf_ok cenv e op G t /\
      (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
        w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (~expr_has_effect e ==>
        (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
        (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)) /\
      (?x. op = Var x) /\
      (?w aid tv. eval_operand op t = SOME w /\
         evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
         val_wf tv v /\
         FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
         aid = sm.cs_next_id /\ aid < sb.cs_next_id /\
         (!n b sz. local_region cenv ee.scopes t n b sz ==>
            regions_disjoint (w2n w) (type_memory_size tv) b sz))``;

(* Administrative suffix on a fixed, successful VV evaluation. *)
Theorem extcall_operand_materialized_read:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  ~is_word_type (expr_type e) /\ dt = lowered_value_type cenv e /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_materialize_vv cenv dt vv sm = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
           (INL tv,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G1 tn1 s /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
         eval_operand (vv_operand vv) s = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
           val_in_memory rt val (w2n w) mem)) /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G1 s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G1 s) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 ==>
  ?v u Gf tm.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G1,tn1) [] (OK u,Gf,tm) /\
      (^extcall_materialized_post) H (INL v) ee Gf tm u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> BETA_TAC >> gvs[] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv (lowered_value_type cenv e)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  Cases_on `unwrap_value cenv vv mid` >>
  rename1 `unwrap_value cenv vv mid = (src,sc)` >>
  Cases_on `compile_store_memory cenv src buf.buf_operand
    (lowered_value_type cenv e) (lowered_value_type cenv e) sc` >>
  qpat_x_assum `compile_materialize_vv _ _ _ sm = _` mp_tac >>
  simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  strip_tac >> gvs[] >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  rename1 `compile_store_memory _ _ _ _ _ sc = ((),sb)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`]
      (cj 1 ci_mono_compile_expr_sa)) >> simp[]) >>
  `ci_mono sm mid` by
    (mp_tac (Q.SPECL [`type_memory_bytes cenv (lowered_value_type cenv e)`,`sm`]
      ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono mid sc` by
    (mp_tac (Q.SPECL [`cenv`,`vv`,`mid`] ci_mono_unwrap_value) >> simp[]) >>
  `ci_mono sc sb` by
    (mp_tac (Q.SPECL [`cenv`,`src`,`buf.buf_operand`,
       `lowered_value_type cenv e`,`lowered_value_type cenv e`,`sc`]
       ci_mono_compile_store_memory) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code mid sc func /\ fn_has_code sc sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  Cases_on `read_result cx tv ee` >>
  rename1 `read_result cx tv ee = (read_res,read_state)` >>
  drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
  Cases_on `read_res`
  >- (rename1 `read_result cx tv ee = (INL v,ee)` >> suspend "typing") >>
  metis_tac[exprSimUnwrapTheory.vv_post_failed_read]
QED

Resume extcall_operand_materialized_read[typing]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all (REWRITE_RULE [ETA_AX] memory_rhs_read_post_typed) >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  disch_then (qx_choose_then `ptv` strip_assume_tac) >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  `type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ptv /\
   type_memory_size ptv < 2 ** 64` by
    (drule body_post_type_allocation_bound >> disch_then (qspec_then `ptv` mp_tac) >> simp[]) >>
  suspend "prefix"
QED

Resume extcall_operand_materialized_read[prefix]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `type_memory_size ltv < dimword (:256)` by decide_tac >>
  Q_TAC (C SUBGOAL_THEN ASSUME_TAC)
    `post_value_type cenv e = lowered_value_type cenv e \/
     is_bytestring_type (post_value_type cenv e) /\
     is_bytestring_type (lowered_value_type cenv e)`
  >- (irule materialize_post_lowered_classify >> simp[]) >>
  `!v'. read_result cx tv ee = (INL v',ee) ==>
    value_has_type ptv v' /\ value_has_type ltv v'` by simp[] >>
  `?obs. ee.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `eval_expr _ _ _ = (INL tv,ee)`
      (mp_then Any mp_tac vyperStorageTraceTheory.storage_trace_frame_prefix) >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_prefix] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `!H. _ ==> vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qhdtm_assum `ghost_inv_at` (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  let
    fun feed pat next rule = qpat_assum pat (mp_then Any next rule)
  in
    feed `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0`
    (feed `compile_expr _ _ e sa = _`
    (feed `compile_alloc_buffer _ sm = (buf,mid)`
    (feed `unwrap_value cenv vv mid = (src,sc)`
    (feed `!H. _ ==> vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\ _`
    (feed `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
    (feed `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv`
    (feed `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv`
      mp_tac))))))) extcall_default_prefix_store_entry
  end >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]) >>
     rpt strip_tac >>
     TRY (qpat_assum `!t x. vv = StackValue t x /\ _ ==> _`
            irule >> simp[] >> NO_TAC) >>
     qpat_assum `_ /\ vv_location vv = SOME LocCode ==> _` drule >> simp[] >>
     (gvs[]))) >>
  disch_then (foldr (uncurry qx_choose_then) (map_every assume_tac o CONJUNCTS)
    [`dst`,`dw`,`v'`,`z`,`G'`,`tn'`,`sw`]) >>
  suspend "store"
QED

Resume extcall_operand_materialized_read[store]:
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[arg_type_fits_word_type] >>
  `compile_store_memory cenv src (Var dst) (lowered_value_type cenv e)
     (lowered_value_type cenv e) sc = ((),sb)` by fs[] >>
  `v' = v` by fs[] >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `ptr_mem_ok cx (lowered_value_type cenv e) v src G' tn' z` by
    (irule default_memory_post >> qexistsl_tac [`ltv`,`sw`] >> simp[]) >>
  drule_at (Pat `compile_store_memory _ _ (Var dst) _ _ _ = _`) default_store_dispatch >>
  disch_then (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand src z = _`)) >>
  disch_then (drule_at (Pat `lookup_var dst z = _`)) >>
  disch_then (drule_at (Pat `allocas_from lo z`)) >>
  disch_then (drule_at (Pat `fn_has_code sc sb func`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (foldr (uncurry qx_choose_then) (map_every assume_tac o CONJUNCTS)
    [`u`,`Gf`,`tm`]) >>
  qexistsl_tac [`u`,`Gf`,`tm`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    drule >> strip_tac >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') [] _`
        (qspec_then `DF H` assume_tac) >>
      qpat_assum `gas_origin_ptr_path _ (s,G1,tn1) [] _`
        (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
      simp[]) >>
  simp[] >> suspend "post"
QED

Resume extcall_operand_materialized_read[post]:
  qpat_assum `expr_post H ctx func cenv cx e es sa sc s0 ee v src z`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `typed_copy_state_frame sc _ _ z u`
    (mp_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  simp[venom_state_component_equality,typed_copy_frame_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
   sc.cs_next_var <= sb.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `not_fresh_at sb dst` by metis_tac[not_fresh_at_mono] >>
  `ptr_covers Gf tm dst u (type_memory_size ltv)` by
    (qpat_assum `ptr_covers G' tn' dst z _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_assum `!x. not_fresh_at sc x ==> _ /\ _ /\ _` (qspec_then `dst` mp_tac) >>
     simp[ptr_covers_def]) >>
  `ptr_mem_ok cx (lowered_value_type cenv e) v (Var dst) Gf tm u` by
    (irule default_memory_post >> qexistsl_tac [`ltv`,`dw`] >> simp[eval_operand_def] >>
     strip_tac >> qexists_tac `dst` >> simp[]) >>
  `ptr_val_ok cx (lowered_value_type cenv e) v (Var dst) Gf tm u` by
    ((qpat_assum `ptr_covers Gf tm dst u _` mp_tac >> simp[ptr_covers_def,ptr_val_ok_def] >> (gvs[ptr_covers_def, ptr_val_ok_def]))) >>
  `ptr_buf_ok cenv e (Var dst) Gf u` by
    (qpat_assum `ptr_covers Gf tm dst u _` mp_tac >>
     simp[ptr_covers_def,ptr_buf_ok_def,eval_operand_def]) >>
  `sm.cs_next_id < mid.cs_next_id` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >>
     simp[loweringShapeRulesTheory.emit_op_eq] >> strip_tac >>
     qpat_assum `_ = mid` (SUBST1_TAC o SYM) >>
     SIMP_TAC (srw_ss()) []) >>
  `sm.cs_next_id < sb.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `!n b sz. local_region cenv ee.scopes u n b sz ==>
      regions_disjoint (w2n dw) (type_memory_size ltv) b sz` by
    (rpt strip_tac >>
     `local_ptrs_rel func cenv ee.scopes z` by
       (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     `local_region cenv ee.scopes z n b sz` by
       (irule exprSimPropsTheory.local_region_frame >>
        qpat_assum `local_ptrs_rel func cenv ee.scopes z` (irule_at Any) >>
        qpat_assum `local_region cenv ee.scopes u n b sz` (irule_at Any) >>
        qpat_assum `local_ptrs_reserved cenv sc` (irule_at Any) >>
        simp[] >> rpt strip_tac >>
        qpat_assum `!x. not_fresh_at sc x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[]) >>
     qpat_assum `!n b sz. local_region cenv ee.scopes z n b sz ==> _`
       drule >> simp[]) >>
  Q_TAC (C SUBGOAL_THEN ASSUME_TAC)
    `?aid. FLOOKUP z.vs_allocas aid = SOME (w2n dw,type_memory_size ltv) /\
       aid = sm.cs_next_id /\ aid < sb.cs_next_id /\
       (!n b sz. local_region cenv ee.scopes u n b sz ==>
          regions_disjoint (w2n dw) (type_memory_size ltv) b sz)`
  >- (qexists_tac `sm.cs_next_id` >> simp[] >> first_assum ACCEPT_TAC) >>
  simp[eval_operand_def,arithmeticTheory.ADD_COMM,
       typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp] >>
  suspend "frames"
QED

Resume extcall_operand_materialized_read[frames]:
  conj_tac
  >- (irule place_typed_copy_alloca_state_frame >>
      qpat_assum `typed_copy_state_frame sc _ _ z u` (irule_at Any) >>
      qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
      qexists_tac `type_memory_size ltv` >>
      simp[venomInstTheory.mk_inst_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_inv z` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee z`
      (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') [] (OK u,Gf,tm)`
       (qspec_then `DF H` (irule_at Any)) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `typed_copy_state_frame sc _ _ z u`
       (mp_then Any mp_tac typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp) >> simp[]) >>
  simp[] >> suspend "exterior"
QED

Resume extcall_operand_materialized_read[exterior]:
  conj_tac >- fs[] >>
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo z` (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n dw`,`type_memory_size ltv`] mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by metis_tac[not_fresh_at_mono] >>
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
     regions_disjoint (w2n dw) (type_memory_size ltv) b sz` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes z name b sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qpat_assum `local_region cenv es.scopes s0 name b sz` (irule_at Any) >>
        qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >> simp[]) >>
     qpat_assum `!name b len. local_region cenv ee.scopes z name b len ==> _`
       (qspecl_then [`name`,`b`,`sz`] mp_tac) >> simp[]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n dw \/ w2n dw + type_memory_size ltv <= off` by
    (rpt strip_tac >>
     `FLOOKUP z.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     `aid <> sm.cs_next_id` by decide_tac >>
     qpat_assum `alloca_inv z`
       (mp_tac o cj 1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     pure_rewrite_tac [venomMemDefsTheory.allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`aid`,`sm.cs_next_id`,`off`,`sz`,
                                `w2n dw`,`type_memory_size ltv`] mp_tac) >> simp[]) >>
  `!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
     lookup_var p z = SOME w ==>
     val_wf entry.type entry.value /\
     (w2n w + val_footprint entry.type entry.value <= w2n dw \/
      w2n dw + type_memory_size ltv <= w2n w)` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv ee.scopes z name (w2n w) sz` by
       (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
     `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
       (qpat_assum `stmt_state_rel H ctx func cenv cx ee z`
         (mp_tac o cj 1 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
        simp[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
        disch_then (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac o cj 1) >> simp[]) >>
     simp[] >>
     `val_footprint entry.type entry.value <= sz` by
       (qpat_assum `val_wf entry.type entry.value`
         (mp_then Any mp_tac exprSimPropsTheory.val_footprint_le) >> decide_tac) >>
     qpat_assum `!name b len. local_region cenv ee.scopes z name b len ==> _`
       (qspecl_then [`name`,`w2n w`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "ghost"
QED

Resume extcall_operand_materialized_read[ghost]:
  `!name b sz. local_region cenv es.scopes s0 name b sz ==>
     b+sz <= w2n dw \/ w2n dw + type_memory_size ltv <= b` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!name b sz. local_region cenv es.scopes s0 name b sz ==> _`
       (qspecl_then [`name`,`b`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    metis_tac[] >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sc x` by
    (qpat_assum `local_ptrs_reserved cenv sc` (mp_tac o REWRITE_RULE
       [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >> metis_tac[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gf tm u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm` by
    (irule structlit_store_ghost_frame >>
     qpat_assum `typed_copy_state_frame sc _ _ z u` (irule_at Any) >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee G' tn' z` (irule_at Any) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w` by
    (rpt strip_tac >> `not_fresh_at sc x` by simp[] >> metis_tac[]) >>
  `return_buf_frame d cenv sb u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >> simp[]) >>
  simp[] >> suspend "purity"
QED

Resume extcall_operand_materialized_read[purity]:
  `wb_frame cenv es ee sa s0 z` by
    (qpat_assum `expr_post H ctx func cenv cx e es sa sc s0 ee v src z`
       (ACCEPT_TAC o MATCH_MP exprSimWordArgsTheory.expr_post_frame)) >>
  `allocas_non_overlapping z` by
    (qpat_assum `alloca_inv z`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def])) >>
  conj_tac
  >- (irule materialize_fresh_store_frame >>
      qpat_assum `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (_,type_memory_size ltv)`
        (irule_at Any) >>
      simp[] >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name b sz. local_region cenv es.scopes s0 name b sz ==> _`
            (drule_then mp_tac) >> simp[DISJ_COMM, arithmeticTheory.ADD_COMM])
      >- (rpt strip_tac >>
          qpat_assum `!x. not_fresh_at sc x ==> _ /\ _ /\ _`
            (qspec_then `x` mp_tac) >> simp[]) >>
      rpt strip_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
        (qspecl_then [`off`,`len`] mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (strip_tac >>
      MATCH_MP_TAC (Q.SPECL [`cenv`,`func`,`es`,`sa`,`s0`,`z`,`u`,
        `mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size ltv))] [dst]`,
        `w2n (dw:bytes32)`,`type_memory_size ltv`] exprSimPropsTheory.pure_frame_buffer_tail) >>
      qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _`
        (assume_tac o REWRITE_RULE [venomInstTheory.mk_inst_def]) >>
      simp[venomInstTheory.mk_inst_def] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
        (qspecl_then [`off`,`len`] mp_tac) >>
      qpat_assum `regions_disjoint off len _ _`
        (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
      simp[arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `eval_expr cx e (es with gas_obs := _) = (INL tv,ee)`
        (mp_then Any mp_tac effect_free_source_projection) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Finalise extcall_operand_materialized_read

Theorem extcall_operand_materialized_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  ~is_word_type (expr_type e) /\ dt = lowered_value_type cenv e /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  compile_materialize_vv cenv dt vv sm = (op,sb) /\
  compile_materialize_vv cenv dt vv shadow_sm = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
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
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    ^extcall_materialized_post
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac
           (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
     qspecl_then [`cenv`,`lowered_value_type cenv e`,`vv`,`sm`] mp_tac
       ci_mono_compile_materialize_vv >> simp[]) >>
  `fn_has_code sa sm func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]) >>
  suspend "child"
QED

Resume extcall_operand_materialized_full[child]:
  `gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o
        REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[]) >>
  `ci_mono shadow_sa shadow_sm` by
    (qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`shadow_sa`]
       mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono shadow_sm shadow_sb` by
    (mp_tac (Q.SPECL [`cenv`,`lowered_value_type cenv e`,`vv`,`shadow_sm`]
       ci_mono_compile_materialize_vv) >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac
       fn_has_code_split >> fs[ci_mono_def]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  drule expr_body_pre_vv_gas_admissible >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  suspend "bind"
QED

Resume extcall_operand_materialized_full[bind]:
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
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
      simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
      simp[]) >>
  suspend "read"
QED

Resume extcall_operand_materialized_full[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ post _` >>
  `?v u Gf tm. read_result cx tv ee = (INL v,ee) /\
     !H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G1,tn1) [] (OK u,Gf,tm) /\ post H (INL v) ee Gf tm u` by
    (unabbrev_all_tac >> simp_tac (srw_ss()) [] >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`dt` |-> `lowered_value_type cenv e`] extcall_operand_materialized_read)) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (HINT_EXISTS_TAC >> simp[]))) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL v`,`u`,`tm`] >>
  conj_tac >- (drule read_result_gas_obs >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Finalise extcall_operand_materialized_full

Theorem extcall_kwarg_default_owned_lookup_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  ~is_word_type rt /\ ~is_word_type (expr_type e) /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt EKDefault (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
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
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ dt = lowered_value_type cenv e /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ptr_val_ok cx dt v op G tn t /\ ptr_mem_ok cx dt v op G tn t /\
      ptr_buf_ok cenv e op G t /\
      (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
        w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (~expr_has_effect e ==>
        (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
        (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)) /\
      (?w aid tv. eval_operand op t = SOME w /\
         evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
         val_wf tv v /\
         FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
         aid < sb.cs_next_id /\
         (!n b sz. local_region cenv ee.scopes t n b sz ==>
            regions_disjoint (w2n w) (type_memory_size tv) b sz)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (sv,shadow_sm)` >>
  `sv = vv` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o
        REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[]) >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv sm` >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv shadow_sm` >>
  gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at Any (Q.INST [`sa` |-> `sa`, `sm` |-> `sm`,
      `shadow_sa` |-> `shadow_sa`, `shadow_sm` |-> `shadow_sm`]
    extcall_operand_materialized_full) >>
  qpat_assum `compile_materialize_vv _ _ _ sm = _` (irule_at Any) >>
  qpat_assum `compile_materialize_vv _ _ _ shadow_sm = _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ sa s0` (irule_at Any) >>
  simp[] >> qexists_tac `shadow_sa` >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> qexists_tac `v` >> simp[] >>
  qexists_tac `sm.cs_next_id` >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* Project away allocation ownership for callers that only save the operand. *)
Theorem extcall_kwarg_default_lookup_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ~is_word_type rt /\ ~is_word_type (expr_type e) /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt EKDefault (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
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
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ dt = lowered_value_type cenv e /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ptr_val_ok cx dt v op G tn t /\ ptr_mem_ok cx dt v op G tn t /\
      ptr_buf_ok cenv e op G t /\
      (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
        w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      return_buf_frame d cenv sb t /\ pure_frame cenv func es sa s0 t /\
      (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >> drule_all extcall_kwarg_default_owned_lookup_full >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  pop_assum (irule_at Any) >> BETA_TAC >>
  conj_tac >- (rpt gen_tac >> strip_tac >> qexists `v` >> simp[]) >> simp[]
QED

(* Keep the outcome interface for callers that do not save operands. *)
Theorem extcall_kwarg_default_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  ~is_word_type rt /\ ~is_word_type (expr_type e) /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt EKDefault (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
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
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ dt = lowered_value_type cenv e /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ptr_val_ok cx dt v op G tn t /\ ptr_mem_ok cx dt v op G tn t /\
      ptr_buf_ok cenv e op G t /\
      (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
        w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\ pure_frame cenv func es sa s0 t /\
      (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (assume_tac o MATCH_MP extcall_kwarg_default_lookup_full) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  pop_assum (irule_at Any) >> BETA_TAC >>
  conj_tac >- (rpt gen_tac >> strip_tac >> qexists `v` >> simp[]) >> simp[]
QED

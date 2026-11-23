(* Joint ordinary-memory and empty AnnAssign execution. *)
Theory bodyFullAnnAssignMemory
Ancestors
  bodyFullPreds bodySimFull bodySim gasShadow
  bodySimDeclCases bodyExprPreFacts exprSimHyps exprSimHypsDefs exprSimSource
  memoryLocalRhsProps supportedStmts supportedStmtTraverse
  stmtSimDeclEmpty stmtSimDeclSource bodyDeclCopyMemory
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  bodyFullAllocaFresh bodyFullMemoryStore bodyFullUnwrap aggregateEvaluatedLayout
  gasShadowCompile exprOperandVar exprSimUnwrap freshWrites
  logStoreDataOriginPtr stmtSimDeclMem exprSimProps
  context emitHelper venomState bodyPtrDefs typedMemoryCopy
  valueEncodingDefs valueEncodingProps valueEncoding vyperTyping ptrDiscipline
  gasOutcomeFullCompose exprSimMemorySource bodyFullStructLitInputs
  immutableDeployPhysicalSource valueCopyBytes gasOutcomeInitialObsPtr
  bodyFullShared bodyFullAnnAssignMemoryPost contextRawReachable unitTransformDefs
  exprLoweringProps assignTuplePtrCopyLen stmtSimDefs stateRelProj
  exprOpenMain exprOpenTerminals stmtSimDeclTypedCode stmtLoweringMono
  valueTypingMemoryProps stmtSimDeclSourceSeparation annassignRelayoutSource
  vyperEvalExprPreservesScopesDom vyperTypeEnvPreservation
  stmtSimDeclCopyFrame stmtSimDeclCompose bodyMemoryDefs
  loweringStateRelDefs bodyBinopFragMemory emitHelperProps fragExec allocaHistory
  compileEnv exprLowering stmtLowering loweringPosts
  vyperTypeSystem vyperTypeArgFits vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

(* The physical source footprint is positive and fits in the destination;
   its runtime type is not identified with the destination runtime type. *)
Theorem annassign_memory_full_source_layout[local]:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) typ /\
  (expr_type e = typ \/ is_bytestring_type typ) /\
  0 < type_memory_bytes ce typ /\ type_memory_bytes ce typ < 2 ** 64 /\
  (lowered_value_type ce e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    0 < type_memory_size stv /\
    type_memory_size stv <= type_memory_bytes ce typ
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `0 < type_memory_bytes ce (lowered_value_type ce e) /\
   type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce typ` by
    metis_tac[memory_rhs_destination_bound] >>
  `type_memory_bytes ce (lowered_value_type ce e) < 2 ** 64` by decide_tac >>
  drule_all memory_rhs_lowered_runtime_layout >> strip_tac >>
  qexists_tac `ltv` >> gvs[]
QED

(* The physical bytestring type can have a smaller capacity than its
   expression post. Both layouts assign the same footprint to this value. *)
Theorem annassign_memory_full_bytes_source_origin[local]:
  is_bytestring_type pty /\ is_bytestring_type sty /\
  evaluate_type (get_tenv cx) pty = SOME ptv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type ptv v /\ value_has_type stv v /\
  expr_val_at ce cx pty sa sb mid v op s ==>
  expr_val_at ce cx sty sa sb mid v op s
Proof
  strip_tac >>
  `?bt1 bt2. ptv = BaseTV bt1 /\ stv = BaseTV bt2` by
    metis_tac[bytestring_type_value] >>
  `val_footprint stv v = val_footprint ptv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_wf stv v` by metis_tac[value_has_type_memory_wf] >>
  gvs[expr_val_at_def, is_bytestring_word_type] >>
  metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]
QED

(* The empty-value branch writes only its zero length word, not the full
   destination capacity.  Reuse the joint scalar store for that write. *)
Theorem annassign_memory_full_empty_store_path[local]:
  has_length_word typ /\ evaluate_type tenv typ = SOME tyv /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
  lookup_var p s = SOME w /\ w2n w + 32 < dimword (:256) /\
  w2n w + 32 <= s.vs_alloca_next /\ ptr_covers G tn p s 32 /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code b sf func /\ ~s.vs_halted /\
  s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory tyv (default_value tyv) (w2n w) t.vs_memory /\
    val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv (default_value tyv) (w2n w) mem) /\
    typed_copy_state_frame b (w2n w) 32 s t /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!i. ~(w2n w <= i /\ i < w2n w + 32) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!q. FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tf (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `compile_store_memory ARB (Lit 0w) (Var p)
    (BaseT BoolT) (BaseT BoolT) b = ((),sf)` by
    simp[compile_store_memory_def, is_word_type_def] >>
  `is_word_type (BaseT BoolT) /\
   evaluate_type tenv (BaseT BoolT) = SOME (BaseTV BoolT) /\
   value_has_type (BaseTV BoolT) (BoolV F) /\
   eval_operand (Lit 0w) s = SOME (typed_val_to_w256 (BaseTV BoolT) (BoolV F)) /\
   op_taint tn (Lit 0w) = {}` by
    simp[is_word_type_def, evaluate_type_def, value_has_type_def,
         eval_operand_def, typed_val_to_w256_def, val_to_w256_def, op_taint_def] >>
  drule_all compile_store_memory_word_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  gvs[val_in_memory_def, val_to_w256_def] >>
  metis_tac[memory_length_word_layout]
QED

(* The raw RHS is still executed in the empty branch.  Its full exceptional
   post is forwarded, rather than replaced by expr_exit alone. *)
Theorem annassign_memory_full_empty_rhs_bind[local]:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
    tv = Value (default_value tyv)) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_expr cx e) (es,s,G,tn) P
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!H res ee G1 tn1 u. P H res ee G1 tn1 u ==> ?tv. res = INL tv) /\
  (!marks tv mid G1 tn1 u.
    (!tail. eval_expr cx e
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (INL tv,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL tv) mid G1 tn1 u) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (new_variable id tyv (default_value tyv)) (mid,u,G1,tn1) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (eval_stmt cx (AnnAssign id typ e)) (es,s,G,tn) Q R
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  once_rewrite_tac[bind_assoc] >> irule gas_outcome_full_bind_all >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (bind (read_result _ v) _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.storage_trace_frame_new_variable]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[]) >>
  rpt strip_tac >>
  `?tv. res = INL tv` by
    (fs[vyperStorageFootprintTheory.storage_trace_domain_def] >> metis_tac[]) >>
  gvs[] >>
  `tv = Value (default_value tyv)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[] >> metis_tac[]) >>
  gvs[read_result_def, bind_return] >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`marks`, `Value (default_value tyv)`] >> simp[]
QED

(* Empty declarations write the 32-byte length word. *)
Theorem annassign_memory_full_empty_post[local]:
  has_length_word typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  new_variable id tyv (default_value tyv) mid = (INL (),out) /\
  mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
  out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv;
               value := default_value tyv; popped := []|>))::rest /\
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  (!H. valid_horizon cx st0 H out.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid G tn s) /\
  fn_inst_ids_distinct func /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
  local_ptrs_reserved ce b /\ not_fresh_at b p /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
  type_memory_size tyv <= sz /\
  alloca_frame old es sa s0 ce mid s /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name a cap. local_region old es.scopes s0 name a cap ==>
      off+len <= a \/ a+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
  w2n w + 32 < dimword (:256) /\ w2n w + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code b sf func /\ ~s.vs_halted /\ ~block_is_terminated sf /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  return_buf_frame d ce b s /\ alloca_history func s ==>
  ?t Gf tf.
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    (!DF. gas_origin_ptr_path (DF,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    !H. valid_horizon cx st0 H out.storage_trace ==>
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce out.scopes /\
      stmt_state_rel H ctx func ce cx out t /\
      storage_well_formed_on cx out (FST H) /\
      return_buf_frame d ce sf t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx out Gf tf t /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame old es sa s0 ce out t /\
      (!aid off len i.
        FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region old es.scopes s0 name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `32 <= type_memory_size tyv` by
    (qspecl_then [`get_tenv cx`, `typ`, `tyv`, `0`, `(mstore 0 0w s).vs_memory`]
       mp_tac memory_length_word_layout >> simp[mstore_mem_word_at_same]) >>
  `ptr_covers G tn p s 32` by
    (qpat_x_assum `ptr_covers G tn p s sz`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  drule_all annassign_memory_full_empty_store_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tf`] >>
  conj_tac >- fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  conj_tac >- fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp] >>
  `return_buf_frame d ce sf t` by suspend "return_frame" >>
  `alloca_history func t` by suspend "history" >>
  qx_gen_tac `H` >> disch_tac >>
  match_mp_tac
    (let
       val theorem = annassign_memory_full_installation_post
       val (vars, _) = strip_forall (concl theorem)
       val body = UNDISCH (SPECL vars theorem)
     in
       GENL vars (DISCH_ALL (CONJUNCT2 (CONJUNCT2 body)))
     end) >>
  qexistsl_tac [`mid`, `b`, `s`, `G`, `tn`, `id`, `p`, `sz`, `w`,
                 `inst`, `32`, `tyv`, `default_value tyv`, `sc`, `rest`] >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[default_value_well_typed, arithmeticTheory.ADD_COMM] >> gvs[]
QED

Resume annassign_memory_full_empty_post[return_frame]:
  drule emitted_insts_emit_void >> strip_tac >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`ce`, `s`, `b`] >>
  fs[typed_copy_state_frame_def]
QED

Resume annassign_memory_full_empty_post[history]:
  drule emitted_insts_emit_void >> strip_tac >>
  `sf.cs_current_bb = b.cs_current_bb` by
    (qpat_x_assum `emit_void MSTORE _ b = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `fn_has_code b sf func` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  rename1 `lookup_block b.cs_current_bb func.fn_blocks = SOME bb` >>
  `?restcode. bb.bb_instructions = sf.cs_current_insts ++ restcode` by
    metis_tac[rich_listTheory.IS_PREFIX_APPEND] >>
  `t with vs_inst_idx := s.vs_inst_idx + 1 = t` by
    simp[venom_state_component_equality] >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + 1)` suffices_by
    asm_rewrite_tac[] >>
  drule alloca_history_no_alloca_slice >>
  disch_then (qspecl_then [`t`, `bb`,
    `[mk_inst b.cs_next_id MSTORE [Var p; Lit 0w] []]`, `restcode`] mp_tac) >>
  simp[venomInstTheory.mk_inst_def, DROP_APPEND, arithmeticTheory.SUB_EQ_0] >>
  `t with vs_inst_idx := LENGTH b.cs_current_insts + 1 = t` by
    simp[venom_state_component_equality] >>
  `LENGTH b.cs_current_insts - (LENGTH b.cs_current_insts + 1) = 0` by decide_tac >>
  asm_rewrite_tac[DROP_0]
QED

Finalise annassign_memory_full_empty_post

(* Empty declarations run compile_expr itself.  This boundary enriches that
   run with the reserved destination and the original allocation frame. *)
Theorem annassign_memory_full_raw_rhs_from_entry[local]:
  compile_expr ce ty e a = (vv,b) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) shadow_a = (vv,shadow_b) /\
  gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code a b func /\ fn_has_code shadow_a shadow_b shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  return_buf_frame d ce a entry /\ alloca_history func entry /\
  (!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es entry /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es Ga tna entry) /\
  ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
  entry.vs_inst_idx = LENGTH a.cs_current_insts /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = NONE /\ not_fresh_at a p /\
  lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
  FLOOKUP entry.vs_allocas aid = SOME (w2n w,sz) /\
  w2n w+sz < dimword (:256) /\ w2n w+sz <= entry.vs_alloca_next /\
  sa.cs_next_id <= a.cs_next_id /\
  (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
    lookup_var x entry = SOME z) /\
  (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==>
    FLOOKUP entry.vs_allocas ad = SOME ent) /\
  alloca_frame old es sa s0 ce es entry /\
  ghost_kept_at lo old es sa G0 tn0 s0 Ga tna ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_expr cx e) (es,entry,Ga,tna)
    (\H res mid G tn u. ?tv. res = INL tv /\
      vv_post H ctx func ce cx e es a b entry mid tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) mid tv vv u /\
      ptr_vv_ok cx (post_value_type ce e) tv vv mid G tn u /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
           ~is_bytestring_type (post_value_type ce e) ==>
        vv_own ce cx (post_value_type ce e) a b mid tv vv u /\
        (!ann q. vv = LocatedValue ann q ==> q.ptr_location = LocMemory)) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv mid = (INL val,mid) /\
          !rt sw. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            eval_operand (vv_operand vv) u = SOME sw ==>
            w2n sw + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
              val_in_memory rt val (w2n sw) mem)) /\
      (!ann op. vv = StackValue ann op /\ ~is_word_type (post_value_type ce e) ==>
        ptr_buf_ok ce e op G u) /\
      (!ann q. vv = LocatedValue ann q /\ q.ptr_location = LocMemory ==>
        ptr_buf_ok ce e q.ptr_operand G u) /\
      ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
      u.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func u /\
      entry.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx mid G tn u /\
      ghost_kept_at lo ce es a Ga tna entry G tn /\
      return_buf_frame d ce b u /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
      lookup_scopes id mid.scopes = NONE /\ not_local_ptr ce mid.scopes p /\
      lookup_var p u = SOME w /\ ptr_covers G tn p u sz /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      w2n w+sz < dimword (:256) /\ w2n w+sz <= u.vs_alloca_next /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
        lookup_var x u = SOME z) /\
      (!ad ent. FLOOKUP s0.vs_allocas ad = SOME ent ==>
        FLOOKUP u.vs_allocas ad = SOME ent) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      alloca_frame old es sa s0 ce mid u /\
      (!ad off len i.
        FLOOKUP s0.vs_allocas ad = SOME (off,len) /\ ad < sa.cs_next_id /\
        (!name x cap. local_region old es.scopes s0 name x cap ==>
          off+len <= x \/ x+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem))
    (\H res mid gt rr. expr_exit res rr /\ halt_exit H cx mid res rr /\
      (ctx_has_dalloca ctx ==> !s. rr = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (`stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es entry` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `stmt_state_rel _ ctx func ce cx es entry`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,
    `vv`,`entry`,`Ga`,`tna`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "success"
QED

Resume annassign_memory_full_raw_rhs_from_entry[success]:
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP
       vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by suspend "horizon" >>
  `stmt_state_rel H ctx func ce cx es entry` by metis_tac[] >>
  `lookup_scopes id ee.scopes = NONE` by
    (Cases_on `lookup_scopes id ee.scopes` >> simp[] >>
     drule_all lookup_scopes_same_fdoms_some >> simp[]) >>
  `not_local_ptr ce ee.scopes p` by
    (irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`,`sz`] >> simp[]) >> qexists_tac `a` >> simp[]) >>
  `cs_extends a b /\ a.cs_next_var <= b.cs_next_var /\
   a.cs_next_id <= b.cs_next_id` by metis_tac[compile_expr_grows] >>
  `return_buf_frame d ce b t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`entry`,`a`] >>
     fs[vv_post_def]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas aid = SOME (w2n w,sz)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `ptr_covers G' tn' p t sz` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
     fs[ghost_kept_at_def]) >>
  `alloca_frame ce es a entry ce ee t` by
    (drule vv_post_alloca_frame >> disch_then irule >> simp[]) >>
  `alloca_frame old es sa s0 ce ee t` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`es`,`entry`,`a`] >> simp[]) >>
  `!ad off len i.
    FLOOKUP s0.vs_allocas ad = SOME (off,len) /\ ad < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
      off+len <= x \/ x+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tn'.t_mem ==> i IN tn0.t_mem` by
    suspend "taint" >>
  fs[vv_post_def,ghost_kept_at_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,metis_tac[]]
QED

Resume annassign_memory_full_raw_rhs_from_entry[horizon]:
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> strip_tac >>
  drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  disch_then drule >> simp[]
QED

Resume annassign_memory_full_raw_rhs_from_entry[taint]:
  fs[ghost_kept_at_def] >>
  qpat_assum `alloca_frame old es sa s0 ce es entry`
    (mp_then Any mp_tac alloca_taint_kept_trans) >>
  disch_then (qspecl_then [`tn'`,`tna`,`tn0`,`a`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`ad`,`off`,`len`,`i`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise annassign_memory_full_raw_rhs_from_entry

(* Keep the physical frontier and unwrap origin at the very endpoint used by
   the successful source read.  The value-only judgment forgets these fields. *)
Theorem annassign_memory_full_physical_rhs_from_entry[local]:
  !DF lo d PG ctx shadow_ctx func shadow_func old ce cx es id typ e
   sa r a b shadow_a shadow_b p sz op s0 G0 tn0 lctx st0 w entry Ga tna env.
    declare_local old id typ sa = (ce,r) /\ old.ce_alloca_locals /\
    FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
    sz = type_memory_bytes old typ /\ sz < dimword (:256) /\
    compile_alloc_buffer sz sa =
      (<|buf_operand := Var p; buf_size := sz|>,a) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) shadow_a = (op,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa a func /\ fn_has_code a b func /\
    fn_has_code shadow_a shadow_b shadow_func /\ fn_inst_ids_distinct func /\
    cs_extends sa a /\ cs_extends a b /\
    local_ptrs_reserved old sa /\ local_ptrs_reserved ce a /\
    (!H. dead_lo_ok H (DF H) lo old cx) /\ ret_pc_ok old sa s0 /\
    (!x cap. old.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
      not_fresh_at sa x) /\
    return_buf_frame d old sa s0 /\ alloca_history func s0 /\
    (!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z) /\
    storage_trace_domain cx st0 es.storage_trace /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    expr_body_pre ce cx env e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
      ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_fresh_at a p /\
    ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
    entry.vs_inst_idx = LENGTH a.cs_current_insts /\
    entry with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
      vs_alloca_next := s0.vs_alloca_next; vs_inst_idx := s0.vs_inst_idx|> = s0 /\
    alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
    lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
    FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    FLOOKUP Ga p = SOME (w2n w,sz) /\
    w2n w+sz < dimword (:256) /\ w2n w+sz <= entry.vs_alloca_next /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP entry.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x entry = lookup_var x s0 /\ FLOOKUP Ga x = FLOOKUP G0 x /\
      op_taint tna (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce es entry /\
    ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es entry /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d ce cx es Ga tna entry) ==>
    not_fresh_at b p /\ local_ptrs_reserved ce b /\
    (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x) /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,entry,Ga,tna)
      (\H res mid G tn u. ?v vv sm tv.
        res = INL v /\
        compile_expr ce (expr_type e) e a = (vv,sm) /\
        unwrap_value ce vv sm = (op,b) /\ read_result cx tv mid = (INL v,mid) /\
        (!ann q. vv = LocatedValue ann q /\ ~is_word_type ann /\
          (q.ptr_location = LocStorage \/ q.ptr_location = LocTransient \/
           q.ptr_location = LocCode) ==>
          vv_own ce cx (post_value_type ce e) sm b mid (Value v)
            (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) u) /\
        (~is_word_type (post_value_type ce e) ==>
          vv_at ce cx (post_value_type ce e) a b mid tv
            (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) u) /\
        (~is_word_type (post_value_type ce e) ==>
          vv_at ce cx (post_value_type ce e) a sm mid tv
            (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) u \/
          vv_at ce cx (post_value_type ce e) sm b mid tv
            (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) u) /\
        (~is_word_type (post_value_type ce e) ==>
          !rt sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
            eval_operand op u = SOME sw ==>
            type_memory_size rt = 0 \/ w2n sw + type_memory_size rt <= u.vs_alloca_next) /\
        expr_post H ctx func ce cx e es a b entry mid v op u /\
        expr_store_bound cx (post_value_type ce e) v op u /\
        ~u.vs_halted /\ mid.gas_obs = [] /\
        u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
        alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        entry.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d ce cx mid G tn u /\
        ptr_val_ok cx (post_value_type ce e) v op G tn u /\
        (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
        ghost_kept_at lo ce es a Ga tna entry G tn /\
        return_buf_frame d ce b u /\
        MAP FDOM mid.scopes = MAP FDOM es.scopes /\
        lookup_scopes id mid.scopes = NONE /\ not_local_ptr ce mid.scopes p /\
        lookup_var p u = SOME w /\ ptr_covers G tn p u sz /\
        FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
        w2n w+sz < dimword (:256) /\ w2n w+sz <= u.vs_alloca_next /\
        (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
          lookup_var x u = SOME z) /\
        (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
          FLOOKUP u.vs_allocas aid = SOME ent) /\
        (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        s0.vs_alloca_next <= u.vs_alloca_next /\
        alloca_frame ce es a entry ce mid u /\
        alloca_frame old es sa s0 ce mid u /\
        (!aid off len i.
          FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
          (!name x cap. local_region old es.scopes s0 name x cap ==>
            off+len <= x \/ x+cap <= off) /\
          off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem))
      (\H res mid gt rr. expr_exit res rr /\ halt_exit H cx mid res rr /\
        (ctx_has_dalloca ctx ==> !s. rr = Halt s ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa a /\ ci_mono a b` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_lower_value_compile_expr,
              pairTheory.SND] >>
  `sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
   sa.cs_next_id <= a.cs_next_id` by fs[ci_mono_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x` by
    (rpt strip_tac >> metis_tac[not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at b p /\ local_ptrs_reserved ce b` by
    (conj_tac >- metis_tac[not_fresh_at_mono] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `ce.ce_is_ctor = old.ce_is_ctor /\
   ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc` by
    (qpat_assum `ce with <|ce_vars := _; ce_var_type := _;
                         ce_dynarray_capacity := _|> = old` mp_tac >>
     simp[compile_env_component_equality]) >>
  `(!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
   (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x)` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  simp[] >> suspend "split"
QED

Resume annassign_memory_full_physical_rhs_from_entry[split]:
  qpat_x_assum `lower_value compile_expr ce (expr_type e) e a = _` mp_tac >>
  simp[lower_value_def,comp_bind_def] >>
  Cases_on `compile_expr ce (expr_type e) e a` >> rename1 `_ = (vv,sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr _ (expr_type e) (gas_shadow_expr e) _ = _` mp_tac >>
  simp[lower_value_def,comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a` >>
  rename1 `_ = (vv',shadow_sm)` >> simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `FST (compile_expr ce (expr_type e) e a) =
     FST (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a) /\
   gas_shadow_state (SND (compile_expr ce (expr_type e) e a))
     (SND (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a))` by
    (irule (REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]
      gas_shadow_stmt_compile_expr_env) >> first_assum ACCEPT_TAC) >>
  gvs[] >>
  `cs_extends a sm /\ a.cs_next_var <= sm.cs_next_var /\
   a.cs_next_id <= sm.cs_next_id` by metis_tac[compile_expr_grows] >>
  `cs_extends sm b` by metis_tac[unwrap_value_extends] >>
  `cs_extends shadow_a shadow_sm /\ cs_extends shadow_sm shadow_b` by
    metis_tac[compile_expr_extends,unwrap_value_extends] >>
  `fn_has_code a sm func /\ fn_has_code sm b func` by
    (qspecl_then [`a`,`sm`,`b`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_a shadow_sm shadow_func` by
    (qspecl_then [`shadow_a`,`shadow_sm`,`shadow_b`,`shadow_func`] mp_tac
      fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
   (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x)` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  `return_buf_frame d ce a entry` by
    (irule return_buf_frame_frame >> qexistsl_tac [`old`,`s0`,`sa`] >>
     simp[] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule expr_body_pre_vv_gas_admissible >> goal_assum (drule_at Any)) >>
  qpat_assum `expr_vv_sim_full _ ce cx _ e es`
    (mp_then (Pat `expr_vv_sim_full _ _ _ _ _ _`) mp_tac
      annassign_memory_full_raw_rhs_from_entry) >>
  disch_then (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ (gas_shadow_expr _) _ = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (qspecl_then [`type_memory_bytes old typ`,`st0`,`id`,`sa.cs_next_id`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, fs[dead_lo_ok_def,arithmeticTheory.ADD_COMM] >> NO_TAC])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[]) >>
  qexists_tac `\H res mid G tn u. childQ H res mid G tn u /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type] >>
      simp[]) >> suspend "read"
QED

Resume annassign_memory_full_physical_rhs_from_entry[read]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s`] >>
  disch_then (strip_assume_tac o BETA_RULE) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (drule_then mp_tac) >>
  simp[Abbr `childQ`,NoAsms] >> strip_tac >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `mid.gas_obs = []` by metis_tac[] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks entry.vs_gas_readings) =
    (INL tv,mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >> asm_rewrite_tac[]) >>
  drule_all post_type_evaluates >> strip_tac >>
  drule body_post_type_allocation_bound >> disch_tac >>
  `!v. read_result cx tv mid = (INL v,mid) ==> value_has_type tv' v` by
    (rpt strip_tac >>
     `expr_body_pre ce cx env e
       (es with gas_obs := gas_explicit marks entry.vs_gas_readings)` by simp[] >>
     `value_runtime_typed env (post_value_type ce e) v` by
       (irule memory_rhs_read_post_typed >>
        qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks entry.vs_gas_readings`,`mid`] >>
        simp[bind_def]) >>
     `env.type_defs = get_tenv cx` by
       (qpat_assum `expr_body_pre ce cx env e es` mp_tac >>
        pure_rewrite_tac[expr_body_pre_def,expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >>
        rpt disch_tac >> metis_tac[]) >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!H. dead_lo_ok H (DF H) lo ce cx` by
    (rewrite_tac[dead_lo_ok_def] >>
     qpat_assum `ce.ce_is_ctor = old.ce_is_ctor` (fn ctor =>
       qpat_assum `!H. dead_lo_ok H (DF H) lo old cx`
         (ACCEPT_TAC o REWRITE_RULE [dead_lo_ok_def, GSYM ctor]))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post H ctx func ce cx e es a sm entry mid tv vv s /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (drule_then mp_tac) >> simp[NoAsms] >>
     rpt strip_tac >> gvs[]) >>
  qpat_assum `compile_expr ce (expr_type e) e a = (vv,sm)`
    (mp_then Any mp_tac unwrap_value_origin_ptr) >>
  disch_then (fn th => qpat_assum `unwrap_value ce vv sm = (op,b)`
    (mp_then (Pat `unwrap_value _ _ _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _` (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (post_value_type ce e) = SOME _`)) >>
  disch_then (qspecl_then [`tv'`,`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  strip_tac >> suspend "unwrap"
QED

Resume annassign_memory_full_physical_rhs_from_entry[unwrap]:
  simp[] >> irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `eval_expr cx e _ = (INL tv,mid)`
       (mp_then (Pat `f st = _`) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func ce cx es entry` by metis_tac[] >>
  `alloca_frame ce es a entry ce mid z` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ z`
       (mp_then Any mp_tac expr_post_alloca_frame) >> simp[]) >>
  `alloca_frame old es sa s0 ce mid z` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`es`,`entry`,`a`] >> simp[]) >>
  `return_buf_frame d ce b z` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`entry`,`a`] >>
     fs[expr_post_def]) >>
  `lookup_var p z = SOME w` by metis_tac[not_fresh_at_mono] >>
  `ptr_covers G' tn' p z (type_memory_bytes old typ)` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
     `lookup_var p z = lookup_var p entry` by asm_rewrite_tac[] >>
     qpat_assum `ghost_kept_at lo ce es a Ga tna entry G' tn'`
       (qspec_then `p` (drule_then strip_assume_tac) o cj 1 o
        REWRITE_RULE [ghost_kept_at_def]) >>
     asm_rewrite_tac[]) >>
  `~z.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[exit_result_def] >> metis_tac[]) >>
  suspend "physical_post"
QED

Resume annassign_memory_full_physical_rhs_from_entry[physical_post]:
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
      off+len <= x \/ x+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tn'.t_mem ==> i IN tn0.t_mem` by
    suspend "physical_taint" >>
  qexistsl_tac [`v`,`tv`] >> asm_rewrite_tac[] >>
  qpat_assum `expr_post H ctx func ce cx e es a b entry mid v op z`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `ghost_kept_at lo ce es a Ga tna entry G' tn'`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid z`
      (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  `w2n w + type_memory_bytes old typ <= z.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `entry.vs_alloca_next` >> asm_rewrite_tac[]) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists_tac `entry.vs_alloca_next` >> asm_rewrite_tac[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP z.vs_allocas aid = SOME ent` by
    (rpt strip_tac >>
     qpat_assum `!aid ent. FLOOKUP entry.vs_allocas aid = SOME ent ==> _` irule >>
     qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> _`
       (drule_then ACCEPT_TAC)) >>
  `FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_bytes old typ)` by
    (qpat_assum `!aid ent. FLOOKUP entry.vs_allocas aid = SOME ent ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x z = SOME w` by
    (rpt strip_tac >>
     qpat_assum `!x w. not_fresh_at a x /\ lookup_var x entry = SOME w ==> _` irule >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at a x /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0 /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G0 x /\
      op_taint tn' (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at a x /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     qpat_assum `!x. not_fresh_at a x ==> FLOOKUP G' x = FLOOKUP Ga x /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0 /\ _`
       (drule_then strip_assume_tac) >>
     asm_rewrite_tac[]) >>
  `!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
      len+off <= x \/ cap+x <= off) /\
    off <= i /\ i < len+off /\ i IN tn'.t_mem ==> i IN tn0.t_mem` by
    (qpat_assum `!aid off len i.
       FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
       (!name x cap. local_region old es.scopes s0 name x cap ==>
         off+len <= x \/ x+cap <= off) /\
       off <= i /\ i < off+len /\ i IN tn'.t_mem ==> i IN tn0.t_mem` mp_tac >>
     simp[NoAsms,arithmeticTheory.ADD_COMM]) >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    qpat_assum `~is_word_type (post_value_type ce e) ==> !rt sw.
       _ ==> _ \/ _ <= z.vs_alloca_next`
      (fn th => mp_tac th >> simp[NoAsms,arithmeticTheory.ADD_COMM])]
QED

Resume annassign_memory_full_physical_rhs_from_entry[physical_taint]:
  qpat_assum `ghost_kept_at lo old es sa G0 tn0 s0 Ga tna`
    (assume_tac o cj 2 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `ghost_kept_at lo ce es a Ga tna entry G' tn'`
    (assume_tac o cj 2 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `alloca_frame old es sa s0 ce es entry`
    (mp_then Any mp_tac alloca_taint_kept_trans) >>
  disch_then (qspecl_then [`tn'`,`tna`,`tn0`,`a`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise annassign_memory_full_physical_rhs_from_entry

(* Complete consumer boundary.  Dispatch and installation are the two literal
   universal contracts; RHS induction is supplied for the declared environment. *)
Theorem annassign_memory_full_execution:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  type_widens_to env.type_defs (expr_type e) typ /\
  assignable_type env.type_defs typ /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
  (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
    has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cenv.ce_alloca_locals` by
    (qpat_x_assum `body_inv tops ctx cenv cx` mp_tac >> simp[body_inv_def]) >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    (qpat_x_assum `stmt_exprs_ok cenv (AnnAssign id typ e)` mp_tac >>
     simp[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
    qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
      irule (MATCH_MP gas_outcome_full_use_return_buf_allocas
        (CONJ frame sep)))) >>
  drule annassign_admissible_type >> strip_tac >>
  `type_memory_bytes cenv typ = type_memory_size tyv` by
    (irule expr_sim_inv_memory_size >> qexistsl_tac [`cx`, `env`, `es`] >> simp[]) >>
  `type_memory_size tyv + 64 < dimword (:256)` by
    (irule allocation_limit_word_room >> fs[]) >>
  drule_all annassign_full_prefix_parts >>
  disch_then (qx_choosel_then
    [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
    strip_assume_tac) >>
  qpat_assum `!sa ce r ty. declare_local _ _ _ _ = _ ==> _`
    (drule_then (qspec_then `expr_type e` strip_assume_tac)) >>
  irule gas_outcome_full_initial_domain >> simp[] >>
  (conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  strip_tac >>
  `sz < dimword (:256)` by decide_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (strip_tac >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     conj_tac >- metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
     drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  drule_all annassign_full_alloc_entry >>
  disch_then (qspecl_then [`PG`, `gas_explicit_sites ctx shadow_ctx`]
    (qx_choosel_then [`w`, `entry`, `Ga`, `tna`] strip_assume_tac)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`
       (qspec_then `ARB` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
       qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _` (fn safe =>
       ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
         (LIST_CONJ [path,phi,safe]))))))) >>
  Cases_on `has_length_word typ /\ is_empty_value_expr e`
  >- suspend "empty" >>
  suspend "ordinary"
QED

Resume annassign_memory_full_execution[empty]:
  qpat_x_assum `if has_length_word typ /\ is_empty_value_expr e then _ else _`
    mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `b = sv` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_b = shadow_sv` SUBST_ALL_TAC >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule expr_body_pre_vv_gas_admissible >> goal_assum (drule_at Any)) >>
  `!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) ==>
    tv = Value (default_value tyv)` by
    (rpt strip_tac >> irule memory_rhs_empty_eval_destination >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     qexistsl_tac [`env`, `typ`] >>
     `env.type_defs = get_tenv cx` by
       (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
        pure_rewrite_tac[expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def] >>
        rpt disch_tac >> metis_tac[]) >>
     simp[] >> qpat_assum `expr_body_pre cenv cx env e es` mp_tac >>
     pure_rewrite_tac[expr_body_pre_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Ga`, `entry`, `tna`] >> simp[] >>
  drule_at (Pat `expr_vv_sim_full _ _ _ _ _ _`)
    annassign_memory_full_raw_rhs_from_entry >>
  disch_then (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ (gas_shadow_expr _) _ = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (qspecl_then [`sz`, `st0`, `id`, `sa.cs_next_id`] mp_tac) >>
  (impl_tac >-
    (`cenv'.ce_is_ctor = cenv.ce_is_ctor` by
       (qpat_assum `cenv' with <|ce_vars := _; ce_var_type := _;
         ce_dynarray_capacity := _|> = cenv`
         (mp_tac o Q.AP_TERM `\ce. ce.ce_is_ctor`) >> simp[]) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, fs[dead_lo_ok_def,arithmeticTheory.ADD_COMM] >> NO_TAC])) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule annassign_memory_full_empty_rhs_bind >>
  qexistsl_tac [`childQ`, `tyv`] >> simp[] >>
  (conj_tac >- suspend "empty_continuation") >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (simp[Abbr `childQ`] >> rpt strip_tac >> goal_assum (drule_at Any))) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
  qpat_x_assum `ctx_has_dalloca ctx ==> !s. r' = Halt s ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def] >>
  Cases_on `y` >> Cases_on `r'` >>
  simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
  TRY (Cases_on `e`) >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume annassign_memory_full_execution[empty_continuation]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> childQ _ _ _ _ _ _`
    (drule_then mp_tac) >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >>
  `tv = Value (default_value tyv)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_assum `!gs tv ee. eval_expr _ _ _ = _ ==> _`
       (drule_then assume_tac) >> simp[]) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
    (INL (default_value tyv),mid with gas_obs := tail)` by
    (simp[Once bind_def, read_result_def, return_def]) >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  qabbrev_tac `out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv;
      value := default_value tyv; popped := []|>))::rest` >>
  `new_variable id tyv (default_value tyv) mid = (INL (),out)` by
    (qpat_assum `!tail. new_variable _ _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >> simp[Abbr `out`, NoAsms]) >>
  `!H. valid_horizon cx st0 H out.storage_trace ==>
    stmt_state_rel H ctx func cenv' cx mid u /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv' cx mid G1 tn1 u` by
    (gen_tac >> simp[Abbr `out`, NoAsms] >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
       (drule_then mp_tac) >>
     simp[loweringPostsTheory.vv_post_def, NoAsms] >> rpt strip_tac >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) out.storage_trace` by
       simp[Abbr `out`] >>
     qpat_assum `!H. valid_horizon _ _ H out.storage_trace ==> _`
       (drule_then (mp_tac o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)) >>
     simp[]) >>
  drule_at (Pat `new_variable _ _ _ _ = _`) annassign_memory_full_empty_post >>
  disch_then (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
  disch_then (fn th => qpat_assum `emit_void MSTORE _ sv = ((),sb)`
    (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (fn th => qpat_assum `!H. valid_horizon _ _ H out.storage_trace ==> _`
    (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `mid.scopes = _`)) >>
  disch_then (fn th => qpat_assum `lookup_var p u = SOME w`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `!x. not_fresh_at sa x ==>
    FLOOKUP G1 x = FLOOKUP G0 x /\ _` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`lctx`, `gas_explicit_sites ctx shadow_ctx`, `PG`] mp_tac) >>
  (impl_tac >- (`32 <= type_memory_size tyv` by
      (qspecl_then [`get_tenv cx`, `typ`, `tyv`, `0`, `(mstore 0 0w u).vs_memory`]
        mp_tac memory_length_word_layout >> simp[mstore_mem_word_at_same]) >>
    `~block_is_terminated sb` by
      (irule emit_void_nonterminator_open >> goal_assum (drule_at Any) >>
       simp[venomInstTheory.is_terminator_def]) >>
    `allocas_from lo u /\ lo <= u.vs_alloca_next` by
      (qpat_assum `ghost_inv_at _ lo d cenv' cx mid G1 tn1 u` mp_tac >>
       pure_rewrite_tac[ghost_inv_at_def] >>
       disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
    `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sv x` by
      (rpt strip_tac >> qpat_assum `ret_pc_ok cenv sa s0` mp_tac >>
       pure_rewrite_tac[ret_pc_ok_def] >>
       disch_then (qspecl_then [`x`, `cap`] mp_tac) >>
       simp[] >> strip_tac >>
       qpat_assum `!x. not_fresh_at sa x ==> _ /\ not_fresh_at sv x`
         (drule_then strip_assume_tac) >> simp[]) >>
    simp[Abbr `out`, venomInstTheory.mk_inst_def, arithmeticTheory.ADD_COMM] >>
    qpat_assum `!ad off len i. _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM])) >>
  strip_tac >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `out`, `INL ()`, `t`, `tf`] >>
  (conj_tac >-
    (qpat_assum `!tail. new_variable _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac[] >> simp[Abbr `out`, NoAsms])) >>
  gen_tac >> disch_tac >> (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H out.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  BETA_TAC >> strip_tac >> qexists_tac `cenv'` >>
  `return_buf_sep d cenv' out t` by
    (`MAP FDOM (sc::rest) = MAP FDOM es.scopes` by
       (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
          (qspec_then `[]` (mp_tac o SRULE [])) >>
        strip_tac >> drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
     irule annassign_memory_return_buf_sep >>
     qpat_assum `FLOOKUP cenv'.ce_vars id = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (w2n w,_)` (irule_at Any) >>
     qexistsl_tac [`st0`,`sc`,`sa`,`s0`,`rest`,`cenv`,`func`,`es`,`<|assignable := T; type := tyv; value := default_value tyv; popped := []|>`,`cx`,`ctx`] >>
     simp[Abbr `out`] >> metis_tac[]) >>
  `ghost_inv_at (DF H) lo d cenv' cx (out with gas_obs := []) Gf tf t <=>
   ghost_inv_at (DF H) lo d cenv' cx out Gf tf t` by
    simp_tac (srw_ss()) [ghost_inv_at_def] >>
  `alloca_frame cenv es sa s0 cenv' (out with gas_obs := []) t <=>
   alloca_frame cenv es sa s0 cenv' out t` by
    simp_tac (srw_ss()) [alloca_frame_def] >>
  `storage_well_formed_on cx (out with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx out (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  simp[exprLoweringPropsTheory.stmt_state_rel_start_gas_obs, return_buf_sep_gas_obs] >>
  qpat_assum `!aid off len i. _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume annassign_memory_full_execution[ordinary]:
  qpat_x_assum `if has_length_word typ /\ is_empty_value_expr e then _ else _`
    mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  qpat_assum `declare_local cenv id typ sa = (cenv',r)`
    (mp_then Any mp_tac annassign_memory_full_physical_rhs_from_entry) >>
  disch_then (fn th => qpat_assum `lower_value _ _ _ e _ = _`
    (mp_then (Pat `lower_value _ _ _ e _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lower_value _ _ _ (gas_shadow_expr e) _ = _`
    (mp_then (Pat `lower_value _ _ _ (gas_shadow_expr e) _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `alloca_frame cenv es sa s0 cenv' es entry`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Ga tna`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `expr_body_pre cenv' cx env e es`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`p`, `sz`, `lctx`, `st0`, `w`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rhs_post _` >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >> (conj_tac >- simp[]) >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
    (mp_then Any (qspecl_then [`id`,`e`] SUBST1_TAC) eval_annassign_action) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `rhs_post` >> reverse conj_tac
  >- (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ rhs_post _` (irule_at Any) >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
      qpat_x_assum `ctx_has_dalloca ctx ==> !s. r' = Halt s ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def, stmt_exit_ptr_def] >>
      Cases_on `y` >> Cases_on `r'` >>
      simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      TRY (Cases_on `e`) >> simp[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (drule_then mp_tac) >>
  simp[Abbr `rhs_post`, NoAsms] >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp_tac (srw_ss()) [] >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  qabbrev_tac `out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest` >>
  `new_variable id tyv v mid = (INL (),out)` by
    (qpat_assum `!tail. new_variable _ _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >> simp[Abbr `out`, NoAsms]) >>
  qpat_assum `declare_local cenv id typ sa = (cenv',r)`
    (mp_then Any mp_tac declare_local_memory_types_mem) >>
  asm_rewrite_tac[] >> strip_tac >>
  `expr_type e = typ \/ is_bytestring_type typ` by
    (qpat_assum `lowered_value_type cenv e = typ \/ _` mp_tac >>
     qpat_assum `lowered_value_type cenv e = expr_type e \/ _` mp_tac >>
     qpat_assum `~(has_length_word typ /\ is_empty_value_expr e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv' e) typ` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >> simp[]) >>
  `~is_word_type (lowered_value_type cenv' e)` by
    (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv' e) typ` mp_tac >>
     qpat_assum `!e. lowered_value_type cenv' e = _` (qspec_then `e` mp_tac) >>
     qpat_assum `lowered_value_type cenv e = typ \/ _` mp_tac >>
     qpat_assum `~(has_length_word typ /\ is_empty_value_expr e)` mp_tac >>
     qpat_assum `~is_word_type typ` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source,
       valueCopyBytesTheory.is_bytestring_word_type]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv' cx e
    (es with gas_obs := gas_explicit marks entry.vs_gas_readings) a b entry mid v op t` by
    simp[gasOutcomeInitialObsPtrTheory.expr_post_initial_obs] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (fn th => simp[NoAsms, GSYM th])) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks entry.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
       qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL, eq])))) >>
  qpat_assum `expr_post _ _ _ _ _ _ (es with gas_obs := _) _ _ _ _ _ _ _`
    (mp_then Any mp_tac structlit_unwrapped_physical_inputs) >>
  disch_then (fn th => qpat_assum `ptr_val_ok _ _ _ _ G1 tn1 t`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`env`] mp_tac) >>
  (impl_tac >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
    asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM])) >>
  disch_then (qx_choosel_then [`stv`,`sw`] strip_assume_tac) >>
  `0 < type_memory_size stv` by
    (qpat_assum `expr_body_pre cenv cx env e es`
        (mp_then Any mp_tac annassign_memory_full_source_layout) >>
      disch_then (qspec_then `typ` mp_tac) >>
      (impl_tac >- (asm_simp_tac bool_ss [] >>
        qpat_assum `lowered_value_type cenv e = expr_type e \/ _` mp_tac >>
        tautLib.TAUT_TAC)) >>
      disch_then (qx_choose_then `source_ty` (fn layout =>
        qpat_assum `!e. lowered_value_type cenv' e = _` (fn ty_eq =>
          qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv' e) = SOME stv`
            (fn ev => ACCEPT_TAC (REWRITE_RULE
              [REWRITE_RULE [Q.SPEC `e` ty_eq, cj 1 layout, optionTheory.SOME_11] ev]
              (cj 3 layout))))))) >>
  TRY (qpat_assum `type_memory_size stv = 0` (fn eq =>
    qpat_assum `0 < type_memory_size stv` mp_tac >> simp_tac std_ss [eq]) >> NO_TAC) >>
  qpat_assum `0 < type_memory_size stv ==> _` drule >> strip_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ lo d cenv' cx mid G1 tn1 t` mp_tac >>
     simp[ghost_inv_at_def, NoAsms] >> strip_tac >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv' cx mid t` by
    qpat_assum `expr_post _ _ _ _ _ _ es a b entry mid v op t`
      (ACCEPT_TAC o cj 1 o REWRITE_RULE [expr_post_def]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> MATCH_ACCEPT_TAC alloca_room_next_lt) >>
  `lookup_var src t = SOME sw /\ not_fresh_at b src` by
    (conj_tac
     >- (qpat_assum `op = Var src` (fn op_eq =>
           qpat_assum `eval_operand op t = SOME sw`
             (ACCEPT_TAC o REWRITE_RULE [op_eq,venomStateTheory.eval_operand_def]))) >>
     qpat_assum `lower_value compile_expr cenv' (expr_type e) e a = (op,b)`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  qabbrev_tac `exp_obs = es with gas_obs := gas_explicit marks entry.vs_gas_readings` >>
  `bind (eval_expr cx e) (read_result cx) exp_obs = (INL v,mid)` by
    (simp_tac std_ss [Abbr `exp_obs`] >> first_assum ACCEPT_TAC) >>
  `expr_body_pre cenv' cx env e exp_obs` by simp[Abbr `exp_obs`] >>
  `value_runtime_typed env typ v` by
    (qspecl_then [`cenv'`,`cx`,`env`,`e`,`exp_obs`,`v`,`mid`,`typ`]
       mp_tac memory_rhs_read_destination_typed >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `value_has_type tyv v /\ val_wf tyv v` by
    (qspecl_then [`cenv`,`cx`,`env`,`es`,`typ`,`v`] mp_tac
       memory_rhs_runtime_layout >>
     simp[value_has_type_memory_wf]) >>
  `acyclic_struct_metadata cenv'.ce_struct_fields` by
    (qpat_assum `body_inv tops ctx cenv' cx`
       (strip_assume_tac o PURE_REWRITE_RULE [body_inv_def]) >>
     first_assum ACCEPT_TAC) >>
  `storage_vars_rel cenv' cx /\ transient_vars_rel cenv' cx` by
    (drule stmt_state_rel_vars_rels >> simp[]) >>
  `~block_is_terminated a` by
    (irule emit_inst_nonterminator_open >>
     qpat_assum `emit_inst ALLOCA _ _ _ = _` (irule_at Any) >>
     simp[venomInstTheory.is_terminator_def]) >>
  `?tv es1. eval_expr cx e exp_obs = (INL tv,es1)` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) exp_obs = (INL v,mid)`
       (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `~block_is_terminated sv` by
    (irule compile_expr_open_general >>
     qpat_assum `compile_expr cenv' (expr_type e) e a = (vv,sv)` (irule_at Any) >>
     qpat_assum `eval_expr cx e exp_obs = (INL _,_)` (irule_at Any) >>
     qexistsl_tac [`tops`,`env`,`ctx`] >> simp[]) >>
  `~block_is_terminated b` by
    (irule unwrap_value_open >>
     qpat_assum `unwrap_value cenv' vv sv = (op,b)` (irule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `~block_is_terminated sb` by
    (irule compile_assign_value_typed_open >>
     qpat_assum `compile_assign_value cenv' _ _ op _ _ _ _ _ b = ((),sb)`
       (irule_at Any) >> simp[]) >>
  `a.cs_next_id <= b.cs_next_id` by
    (qpat_assum `lower_value compile_expr cenv' (expr_type e) e a = (op,b)`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `b.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `compile_assign_value cenv' _ _ op _ _ _ _ _ b = ((),sb)`
       (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
     metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND]) >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [p] /\
   inst.inst_opcode = ALLOCA` by
    simp[Abbr `inst`, venomInstTheory.mk_inst_def, NoAsms] >>
  `inst.inst_id < b.cs_next_id` by
    (qpat_assum `inst.inst_id = sa.cs_next_id` SUBST1_TAC >>
     qpat_assum `a.cs_next_id <= b.cs_next_id` mp_tac >>
     qpat_assum `sa.cs_next_id < a.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!H. valid_horizon cx st0 H out.storage_trace ==>
    stmt_state_rel H ctx func cenv' cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv' cx mid G1 tn1 t` by
    (gen_tac >> simp[Abbr `out`, NoAsms] >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
       (drule_then mp_tac) >>
     simp[NoAsms, expr_post_def] >>
     rpt strip_tac >> simp[]) >>
  `?u Gf tf.
    lookup_var p u = SOME w /\
    FLOOKUP u.vs_allocas (inst.inst_id) = SOME (w2n w,sz) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gf,tf)) /\
    !H. valid_horizon cx st0 H out.storage_trace ==>
      stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext cenv cenv' out.scopes /\ stmt_state_rel H ctx func cenv' cx out u /\
      storage_well_formed_on cx out (FST H) /\ return_buf_frame d cenv' sb u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv' cx out Gf tf u /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x u = SOME z) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv' out u /\
      (!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region cenv es.scopes s0 name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)` by
    suspend "ordinary_suffix" >>
  suspend "ordinary_pure"
QED

Resume annassign_memory_full_execution[ordinary_suffix]:
  markerLib.RESUME_TAC >>
  `expr_val_at cenv' cx (lowered_value_type cenv' e) a b mid v op t` by
    (`expr_val_at cenv' cx (post_value_type cenv' e) a b mid v op t` by
       (qpat_assum `expr_post _ _ _ _ _ _ es a b entry mid v op t` mp_tac >>
        simp[NoAsms,expr_post_def]) >>
     qpat_assum `expr_body_pre cenv' cx env e exp_obs`
       (mp_then Any mp_tac immutable_rhs_post_physical_classify) >>
     strip_tac
     >- (qpat_assum `post_value_type cenv' e = lowered_value_type cenv' e`
           (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) immutable_rhs_physical_memory) >>
     disch_then (qx_choosel_then [`ptv`,`pw`] strip_assume_tac) >>
     mp_tac (Q.INST
       [`pty` |-> `post_value_type cenv' e`, `sty` |-> `lowered_value_type cenv' e`,
        `ptv` |-> `ptv`, `stv` |-> `stv`, `ce` |-> `cenv'`, `sa` |-> `a`,
        `sb` |-> `b`, `s` |-> `t`] annassign_memory_full_bytes_source_origin) >>
     asm_rewrite_tac[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (qpat_assum `w2n sw + type_memory_size stv <= t.vs_alloca_next` mp_tac >>
     qpat_assum `t.vs_alloca_next < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz)` by simp[] >>
  `sa.cs_next_id <= b.cs_next_id` by
    (qpat_assum `a.cs_next_id <= b.cs_next_id` mp_tac >>
     qpat_assum `sa.cs_next_id < a.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `compile_assign_value cenv' (Var p) LocMemory (Var src) F (vv_location vv)
    typ (lowered_value_type cenv' e) (type_memory_bytes cenv' typ) b = ((),sb)` by
    (qpat_assum `op = Var src` (fn eq =>
       qpat_assum `compile_assign_value cenv' _ _ op _ _ _ _ _ b = ((),sb)`
         (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  `~is_bytestring_type typ /\ vv_location vv <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size tyv <= w2n sw` by
    (strip_tac >>
     `~is_bytestring_type (lowered_value_type cenv' e)` by
       (qpat_assum `type_widens_to _ (lowered_value_type cenv' e) typ` mp_tac >>
        qpat_assum `~is_bytestring_type typ` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[type_widens_from_bytestring]) >>
     `val_footprint stv v = type_memory_size stv` by
       (qpat_assum `evaluate_type _ (lowered_value_type cenv' e) = SOME stv`
         (mp_then Any mp_tac nonbytes_evaluated_val_footprint) >> simp[]) >>
     `w2n sw + val_footprint stv v <= w2n w \/ w2n w + sz <= w2n sw` by
       (`inst.inst_id < a.cs_next_id` by simp[] >>
        `0 < val_footprint stv v` by simp[] >>
        map_every (fn pat => qpat_assum pat mp_tac)
          [`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv' cx mid t`,
           `fn_inst_ids_distinct func`,
           `expr_val_at cenv' cx (lowered_value_type cenv' e) a b mid v op t`,
           `evaluate_type (get_tenv cx) (lowered_value_type cenv' e) = SOME stv`,
           `~is_word_type (lowered_value_type cenv' e)`,
           `0 < val_footprint stv v`, `eval_operand op t = SOME sw`,
           `MEM inst (fn_insts func)`, `inst.inst_outputs = [p]`,
           `not_local_ptr cenv' mid.scopes p`, `inst.inst_id < a.cs_next_id`,
           `FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz)`] >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[expr_val_at_alloca_outside_interval_separate]) >>
     simp[]) >>
  (Cases_on `is_bytestring_type typ /\ vv_location vv <> SOME LocMemory` >|
    [irule annassign_memory_full_bytes_suffix_post,
     irule annassign_memory_full_suffix_post]) >>
  suspend "ordinary_suffix_premises"
QED

Resume annassign_memory_full_execution[ordinary_suffix_premises]:
  markerLib.RESUME_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `expr_body_pre cenv' cx env e es`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_body_pre_def, expr_sim_inv_def]) >>
    first_assum ACCEPT_TAC)
  >> TRY (qpat_assum `!aid off len i. _ ==> i IN tn0.t_mem`
    (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
    disch_tac >> rpt gen_tac >> strip_tac >>
    first_x_assum (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
    simp[arithmeticTheory.ADD_SYM] >> disch_then irule >>
    rpt strip_tac >> first_x_assum drule >>
    simp[arithmeticTheory.ADD_SYM] >> NO_TAC) >>
  TRY (qpat_assum `inst.inst_id = sa.cs_next_id`
    (fn th => PURE_REWRITE_TAC [th, arithmeticTheory.LESS_EQ_REFL])) >>
  qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`b`,`tyv`,`typ`] >>
  qexistsl_tac [`id`,`mid`,`type_memory_size stv`,`rest`,`sc`] >>
  qexistsl_tac [`vv_location vv`,`a`,`stv`,`lowered_value_type cenv' e`,
    `sw`,`v`,`src`] >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
  TRY (qpat_assum `expr_body_pre cenv' cx env e es`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_body_pre_def, expr_sim_inv_def]) >>
    first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `type_widens_to _ (lowered_value_type cenv' e) typ`
    (mp_then Any mp_tac typed_copy_bytestring_source) >> simp[] >> NO_TAC) >>
  TRY (simp[Abbr `out`, arithmeticTheory.ADD_COMM] >> NO_TAC) >>
  TRY (disch_tac >> qpat_assum `op = Var src` (fn eq =>
    qpat_assum
      `expr_val_at cenv' cx (lowered_value_type cenv' e) a b mid v op t`
      (ACCEPT_TAC o PURE_REWRITE_RULE [eq])) >> NO_TAC) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`~(is_bytestring_type typ /\ vv_location vv <> SOME LocMemory)`,
     `~is_bytestring_type typ /\ vv_location vv <> SOME LocMemory ==> _`] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume annassign_memory_full_execution[ordinary_pure]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_pure >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gf`,`out`,`INL ()`,`u`,`tf`] >>
  (conj_tac >- (drule new_variable_success_gas_obs >> simp[NoAsms])) >>
  gen_tac >> disch_tac >>
  (conj_tac >- first_assum MATCH_ACCEPT_TAC) >>
  BETA_TAC >> strip_tac >> qexists_tac `cenv'` >>
  `out with gas_obs := [] = out` by
    (qpat_assum `mid.gas_obs = []`
       (fn th => simp[NoAsms,Abbr `out`,GSYM th])) >>
  qpat_assum `out with gas_obs := [] = out`
    (fn eq => pure_rewrite_tac [eq]) >>
  qpat_assum `!H. valid_horizon cx st0 H out.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `return_buf_sep d cenv' out u` by
    (`MAP FDOM (sc::rest) = MAP FDOM es.scopes` by
       (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
          (qspec_then `[]` (mp_tac o SRULE [])) >>
        strip_tac >> drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
     irule annassign_memory_return_buf_sep >>
     qpat_assum `FLOOKUP cenv'.ce_vars id = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (w2n w,_)` (irule_at Any) >>
     qexistsl_tac [`st0`,`sc`,`sa`,`s0`,`rest`,`cenv`,`func`,`es`,`<|assignable := T; type := tyv; value := v; popped := []|>`,`cx`,`ctx`] >>
     simp[Abbr `out`] >> metis_tac[]) >>
  asm_simp_tac bool_ss [] >>
  qpat_assum `!aid off len i. _ ==> i IN tn0.t_mem`
    (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
  simp[arithmeticTheory.ADD_SYM] >> disch_then irule >>
  rpt strip_tac >> first_x_assum drule >> simp[arithmeticTheory.ADD_SYM]
QED

Finalise annassign_memory_full_execution

(* Joint ordinary-memory and empty AnnAssign execution. *)
Theory bodyFullAnnAssignMemory
Ancestors
  bodyFullPreds bodySimFull bodyInvNoDalloca gasShadow
  bodySimDeclCases bodyExprPreFacts exprSimHyps exprSimHypsDefs exprSimSource
  memoryLocalRhsProps supportedStmts supportedStmtTraverse
  stmtSimDeclEmpty stmtSimDeclSource bodyDeclCopyMemory
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  bodyFullAllocaFresh bodyFullMemoryStore
  logStoreDataOriginPtr stmtSimDeclMem exprSimProps
  context emitHelper venomState bodyPtrDefs typedMemoryCopy
  valueEncodingDefs valueEncodingProps valueEncoding vyperTyping ptrDiscipline
  gasOutcomeFullCompose
  stmtSimDeclCopyFrame stmtSimDeclCompose bodyMemoryDefs bodyPtrDefs
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

(* The empty-value branch writes only its zero length word, not the full
   destination capacity.  Reuse the joint scalar store for that write. *)
Theorem annassign_memory_full_empty_store_path[local]:
  has_length_word typ /\ evaluate_type tenv typ = SOME tyv /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
  lookup_var p s = SOME w /\ w2n w + 32 < dimword (:256) /\
  w2n w + 32 <= s.vs_alloca_next /\ ptr_covers G tn p s 32 /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
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

(* Package the actual empty suffix against a horizon-indexed installation
   continuation.  The machine endpoint is chosen before that quantifier. *)
Theorem annassign_memory_full_empty_continuation[local]:
  has_length_word typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
  lookup_var p s = SOME w /\ w2n w + 32 < dimword (:256) /\
  w2n w + 32 <= s.vs_alloca_next /\ ptr_covers G tn p s 32 /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code b sf func /\ ~s.vs_halted /\
  s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!tail. new_variable id tyv (default_value tyv) (mid with gas_obs := tail) =
    (INL (),out with gas_obs := tail)) /\
  (!H Gf tf t.
    valid_horizon cx st0 H out.storage_trace /\
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
      op_taint tf (Var q) = op_taint tn (Var q)) ==>
    Q H (INL ()) (out with gas_obs := []) Gf tf t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (new_variable id tyv (default_value tyv)) (mid,s,G,tn) Q R
Proof
  strip_tac >> drule_all annassign_memory_full_empty_store_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`, `out`, `INL ()`, `t`, `tf`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
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

(* Empty declarations use a 32-byte write, although the declared runtime
   type and the destination capacity may both be larger.  The installation
   implication below is the common, capacity-parametric contract verbatim. *)
Theorem annassign_memory_full_empty_post:
  (!(H : (bool # 256 word # type_value) list # num list) D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf
   id p sz w inst n tyv v sc rest lctx.
    new_variable id tyv v mid = (INL (),out) /\
    mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    FLOOKUP old.ce_vars id = NONE /\
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at D lo d ce cx mid G tn s /\ fn_inst_ids_distinct func /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
    local_ptrs_reserved ce b /\ not_fresh_at b p /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
    n <= type_memory_size tyv /\ type_memory_size tyv <= sz /\
    val_wf tyv v /\ value_has_type tyv v /\
    typed_copy_state_frame b (w2n w) n s t /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n w <= i /\ i < w2n w+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at b x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
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
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
    cenv_top_ext old ce out.scopes /\
    stmt_state_rel H ctx func ce cx out t /\
    storage_well_formed_on cx out (FST H) /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d ce cx out Gf tf t /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce out t /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)) /\
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
    ghost_inv_at D lo d ce cx mid G tn s) /\
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
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code b sf func /\ ~s.vs_halted /\ ~block_is_terminated sf /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  return_buf_frame d ce b s /\ alloca_history func s ==>
  ?t Gf tf.
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
      ghost_inv_at D lo d ce cx out Gf tf t /\
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
  qpat_x_assum `!H D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf id p sz w inst n tyv v sc rest lctx. _`
    (mk_asm "install") >>
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
  (conj_tac >- first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `return_buf_frame d ce sf t` by suspend "return_frame" >>
  `alloca_history func t` by suspend "history" >>
  qx_gen_tac `H` >> disch_tac >>
  asm_x "install" match_mp_tac >>
  qexistsl_tac [`mid`, `b`, `s`, `G`, `tn`, `id`, `p`, `sz`, `w`,
                 `inst`, `32`, `tyv`, `default_value tyv`, `sc`, `rest`] >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[default_value_well_typed, arithmeticTheory.ADD_COMM] >> gvs[]
QED

Resume annassign_memory_full_empty_post[return_frame]:
  qpat_x_assum `install :- _` kall_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`ce`, `s`, `b`] >>
  fs[typed_copy_state_frame_def]
QED

Resume annassign_memory_full_empty_post[history]:
  qpat_x_assum `install :- _` kall_tac >>
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

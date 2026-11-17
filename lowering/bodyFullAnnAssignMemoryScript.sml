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
  gvs[read_result_def, bind_return] >> first_x_assum irule >>
  qexistsl_tac [`marks`, `Value (default_value tyv)`] >> simp[]
QED

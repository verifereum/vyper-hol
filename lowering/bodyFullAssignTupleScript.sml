(*
 * Tuple assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAssignTuple
Ancestors placeMemoryCopyEffect[qualified,ignore_grammar] immSectionDead compileVyper bodyStorageMetadata ctorDeployDeadSectionFrame ctorDeployDeadSection pred_set immutableCopyExecution immutableDeployOperandTransfer fragGasSeqPtr stmtReasonLitFragMemory immutableWordExecution fragExecMem memSafeRun venomExecSemantics exprSimCopy venomInst unitTransformDefs codegenRel contextCodegenRel bodyPtrBopInRepresentation immutableAssignCompose immutableDeployAssignBytes immutableDeployAssignAdmissible valueEncodingProps venomMemProps vyperTypeValues typedCopyOriginPtr placeStoreDynPrepare bodyMemBopRestWordPath allocaSiteResource exprSimPtrLiteralBuffer exprSimAlloc exprOperandVar fragGasMode fragGasOrigin[qualified,ignore_grammar]
  words[qualified,ignore_grammar] bodyFullPreds bodySimFull bodyFullShared gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  bodyFullLocalCopy robustCopyTransportPtr exprSimProps typedMemoryCopy
  bodyFullMemoryCopy bodyFullMemoryFrames context loweringPosts loweringStateRelDefs
  venomState typedCopyOriginPtrBase decoderSetupStepPtr exprPtrCtorImmStore
  stateFrame ghostPcTransportPtr emitHelperProps arithmetic bodyPtrDefs ptrDiscipline
  tupleLoadProps fragExec fragGasOriginPtrLoop
  assignTuplePtrLoadStep tupleTypedLoad bodyFullGhostFrame valueEncodingProofs
  augAssignFullStore assignTuplePtrStorage stmtSimAssignStorage vfmState exprLoweringProps
  tupleTargetStoreRun bodyFullMemoryStore stateRelProj wordLoadStorePtr memoryPlaceStorePost
  haltExitProj immutableRepSensitivity immutableBytestringRuntime[qualified,ignore_grammar] assignTuplePtrStoreWord stmtSimDeclStore vyperTypeArgFits instMemFrontier
  tupleTargetStoreProps vyperLookup stmtSimAssignStorageFacts stmtSimDefs exprSimDefs fragGasOriginPtr loweringSlice
  bodyExprPreFacts supportedNameRoot exprSimBufferStore[qualified,ignore_grammar] immutableDeployAssignFacts[qualified,ignore_grammar] bodyImmutableAugAssignStore[qualified,ignore_grammar] immutableDeployAssignStateFrame[qualified,ignore_grammar] exprSimLiteralBuffer[qualified,ignore_grammar] exprSimAbiEncodeStateTransport[qualified,ignore_grammar] exprSimAggregateLoops[qualified,ignore_grammar] vyperTypeContract[qualified,ignore_grammar] supportedProgram[qualified,ignore_grammar] exprSimHyps structFieldsProps immutableRelation gasContext allocLimitsProps supportedStmtTraverse
  vyperTypeCallGraph vyperTypeCallStackSoundness gasShadowCompileStmtHelpers
  gasShadowState exprSimUnwrap stmtLoweringMono exprSimSource
  bodyPtrBopTypedSource[qualified,ignore_grammar]
  vyperStorageFootprint[qualified,ignore_grammar] stmtSimAppendStorageCompose[qualified,ignore_grammar] bodyFullMemoryStage[qualified,ignore_grammar]
  immutableAssignOpen[qualified,ignore_grammar] bodyFullPathHistory[qualified,ignore_grammar]
  bodyFullAssignTopCopyTail[qualified,ignore_grammar] tuplePlaceValueStorageFrame[qualified,ignore_grammar]

val _ = Parse.hide "body";

Theorem type_stmt_assigntuple:
  type_stmt env ret_ty (Assign (TupleTarget gs) e) =
    (if atarget_accepts env (TupleTarget gs) (expr_type e) /\
        well_typed_expr env e /\ assignable_type env.type_defs (expr_type e)
     then SOME env else NONE)
Proof
  simp_tac bool_ss [Once type_stmt_def]
QED

Theorem supported_stmt_assigntuple:
  supported_stmt tops bindings (Assign (TupleTarget gs) e) =
    supported_assignment tops bindings (TupleTarget gs) e
Proof
  simp_tac bool_ss [Once supported_stmt_def]
QED

(* A local copy preserves the disjoint snapshot used by later tuple targets. *)
Theorem body_assign_tuple_local_copy_snapshot_post:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf) /\
  typed_copy_state_frame sa (w2n dst) (type_memory_size entry.type) s t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME dst /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s id (w2n dst) cap /\
  type_memory_size entry.type <= cap /\ lo <= w2n dst /\
  val_wf entry.type v /\ value_has_type entry.type v /\
  val_in_memory entry.type v (w2n dst) t.vs_memory /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory entry.type v (w2n dst) mem) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. ~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type) ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  (b + type_memory_size (TupleTV tvs) <= w2n dst \/
   w2n dst + type_memory_size entry.type <= b) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) ==>
  stmt_state_rel H ctx func cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
  ghost_inv_at D lo d cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
    Gf tf t /\
  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) /\
  (!aid off sz i.
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n a len. local_region cenv es.scopes s n a len ==>
      off + sz <= a \/ a + len <= off) /\
    off <= i /\ i < off + sz /\ i IN tf.t_mem ==>
    i IN tn.t_mem)
Proof
  strip_tac >> (drule_all body_full_local_copy_post >> strip_tac >> simp[] >>
  conj_tac
  >- (drule val_footprint_le >> strip_tac >>
      `!i. b <= i /\ i < b + val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) ==>
        ~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type)` by
        (rpt strip_tac >> decide_tac) >>
      `!i. ~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
        (rpt strip_tac >>
         qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
         simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
         rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      drule_at (Pos (el 5)) robust_val_in_memory_exterior_frame >>
      disch_then (qspecl_then [`tf.t_mem`, `t.vs_memory`,
        `{i | w2n dst <= i /\ i < w2n dst + type_memory_size entry.type}`] mp_tac) >>
      simp[]) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`id`, `w2n dst`, `cap`] mp_tac) >>
  simp[] >> strip_tac >>
  `~(w2n dst <= i /\ i < w2n dst + type_memory_size entry.type)` by decide_tac >>
  metis_tac[])
QED

(* The positive MCOPY emitted by tuple staging selects one joint endpoint. *)
Theorem body_assign_tuple_stage_mcopy_path:
  emit_void MCOPY [Var xd; Var xs; Lit (n2w n)] sa = ((),sb) /\
  0 < n /\ type_memory_size (TupleTV tvs) = n /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) mem) /\
  ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
  w2n sw + n < dimword (:256) /\ w2n dw + n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `compile_copy_memory (Var xd) (Var xs) n sa = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  Q.SUBGOAL_THEN `n = 0 \/ w2n sw + n <= s.vs_alloca_next` assume_tac
  >- simp[] >>
  Q.SUBGOAL_THEN `n = 0 \/ w2n dw + n <= s.vs_alloca_next` assume_tac
  >- simp[] >>
  drule_all body_full_memory_copy_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

(* Allocation retains robust source contents at its own joint endpoint. *)
Theorem body_assign_tuple_alloc_snapshot:
  stmt_state_rel H ctx func cenv cx es s /\
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  n < dimword (:256) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  expr_val_at cenv cx (TupleT tys) start sa es (ArrayV (TupleV vs)) (Var xs) s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) mem) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u root b G1 tn1.
    buf.buf_operand = Var root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
      stmt_state_rel H' ctx func cenv cx es u) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es G1 tn1 u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\
    lo <= b /\ b+n < dimword (:256) /\ lookup_var root u = SOME (n2w b) /\
    ptr_covers G1 tn1 root u n /\
    (!name a len. local_region cenv es.scopes u name a len ==> regions_disjoint b n a len) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==> regions_disjoint b n a len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==> ptr_covers G1 tn1 x u cap) /\
    not_fresh_at sb root /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    u.vs_accounts = s.vs_accounts /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    (!i. ~(b <= i /\ i < b+n) ==> (i IN tn1.t_mem <=> i IN tn.t_mem)) /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) mem)
Proof
  strip_tac >>
  drule_all body_full_alloc_buffer_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`u`,`root`,`b`,`G1`,`tn1`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!name a len. local_region cenv es.scopes u name a len <=>
    local_region cenv es.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
   (!i. w2n sw <= i /\
        i < w2n sw + val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) ==>
        ~(b <= i /\ i < b+n))` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_val_at_def] >>
     disch_then (qspec_then `TupleTV tvs` mp_tac) >>
     simp[is_word_type_def,eval_operand_def] >> strip_tac >>
     gvs[regions_disjoint_def] >> res_tac >> decide_tac) >>
  drule_at (Pos (el 5)) robust_val_in_memory_exterior_frame >>
  disch_then (qspecl_then [`tn1.t_mem`, `s.vs_memory`,
    `{i | b <= i /\ i < b+n}`] mp_tac) >> simp[]
QED

(* Tuple element addresses are joint origin/pointer steps at every horizon. *)
Theorem body_assign_tuple_offset_add_path:
  emit_op ADD [Var root; Lit (n2w off)] sa = (op,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME w /\
  ptr_covers G tn root s capacity /\ off+n <= capacity /\
  w2n w + capacity < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t Gf tf.
    op = Var out /\ not_fresh_at sb out /\
    t = (update_var out (w+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out])
      (update_var out (w+n2w off) s) /\
    tf = step_taint (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out]) s
      (update_var out (w+n2w off) s) tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    lookup_var out t = SOME (w+n2w off) /\ ptr_covers Gf tf out t n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    op_taint tf (Var out) = {} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `op = Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[not_fresh_at_def,Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  `eval_operand (Var root) s = SOME w /\
   eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def,op_taint_def] >>
  `!D. ?t Gf tf.
     t = (update_var out (w+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
     Gf = step_prov PG G (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out])
       (update_var out (w+n2w off) s) /\
     tf = step_taint (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [out]) s
       (update_var out (w+n2w off) s) tn /\
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (gen_tac >>
     drule_all (typed_copy_origin_ptr_binop_path |> Q.INST
       [`opc` |-> `ADD`, `w` |-> `x+y`] |> SRULE []) >>
     simp[eval_operand_def,op_taint_def] >>
     disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`D`] mp_tac) >>
     gvs[] >> metis_tac[]) >>
  gnvs[] >>
  conj_tac >- metis_tac[typed_copy_emit_op_fresh] >>
  conj_tac >- simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  conj_tac >-
    (simp[] >> irule typed_copy_origin_ptr_offset_covers >>
     simp[eval_operand_def] >> metis_tac[]) >>
  simp[typed_copy_origin_ptr_binop_ghost_frame] >>
  simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE,state_frame_def] >>
  rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame,GSYM update_var_def]
QED

(* Storage-field slots are word sums of literals, never memory pointers. *)
Theorem body_assign_tuple_field_add_path:
  emit_op ADD [Lit slot; Lit (n2w off)] sa = (dst,sb) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t Gf tf.
    dst = Var out /\ not_fresh_at sb out /\
    t = (update_var out (slot+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst sa.cs_next_id ADD [Lit slot;Lit (n2w off)] [out])
      (update_var out (slot+n2w off) s) /\
    tf = step_taint (mk_inst sa.cs_next_id ADD [Lit slot;Lit (n2w off)] [out]) s
      (update_var out (slot+n2w off) s) tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    lookup_var out t = SOME (slot+n2w off) /\
    op_taint tf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==>
      ptr_covers Gf tf x t cap)
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `dst = Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[not_fresh_at_def,Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `!D. ?t Gf tf.
     t = (update_var out (slot+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
     Gf = step_prov PG G (mk_inst sa.cs_next_id ADD [Lit slot;Lit (n2w off)] [out])
       (update_var out (slot+n2w off) s) /\
     tf = step_taint (mk_inst sa.cs_next_id ADD [Lit slot;Lit (n2w off)] [out]) s
       (update_var out (slot+n2w off) s) tn /\
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (gen_tac >>
     `eval_operand (Lit slot) s = SOME slot /\
      eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
      op_taint tn (Lit slot) = {} /\ op_taint tn (Lit (n2w off)) = {}` by
       simp[eval_operand_def,op_taint_def] >>
     drule_all (typed_copy_origin_ptr_binop_path |> Q.INST
       [`opc` |-> `ADD`, `w` |-> `x+y`] |> SRULE []) >>
     disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`,`G`,`D`] mp_tac) >>
     gvs[] >> metis_tac[]) >>
  gnvs[] >>
  conj_tac >- metis_tac[typed_copy_emit_op_fresh] >>
  conj_tac >- simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  simp[typed_copy_origin_ptr_binop_ghost_frame] >>
  conj_tac >-
    simp[op_prov_def,step_prov_def,out_prov_def,first_prov_def,set_prov_def,
         venomInstTheory.mk_inst_def,FLOOKUP_DRESTRICT] >>
  conj_tac >- simp[state_frame_def,update_var_def] >>
  simp[update_var_def] >>
  conj_asm1_tac >-
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[lookup_var_def,FLOOKUP_UPDATE,GSYM update_var_def,
          typed_copy_origin_ptr_binop_ghost_frame]) >>
  conj_tac >- (rpt strip_tac >>
    irule stmt_state_rel_old_vars_frame_ptr >>
    goal_assum (drule_at Any) >> qexists `sa` >>
    simp[state_frame_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule ghost_inv_at_exterior_frame >>
    goal_assum (drule_at Any) >> qexists `sa` >>
    simp[GSYM update_var_def,typed_copy_origin_ptr_binop_ghost_frame] >>
    metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _`
    (qspec_then `x` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  irule decoderGhostFramePtrTheory.ptr_covers_frame >>
  qexistsl_tac [`G`,`s`,`tn`] >> simp[lookup_var_def]
QED

(* Clean tuple words use the same deterministic MLOAD endpoint for all D. *)
Theorem body_assign_tuple_mload_path:
  emit_op MLOAD [Var root] sa = (op,sb) /\
  lookup_var root s = SOME w /\ ptr_covers G tn root s 32 /\
  w2n w+32 <= s.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t Gf tf.
    op = Var out /\ not_fresh_at sb out /\
    t = (update_var out (mload (w2n w) s) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var root] [out])
      (update_var out (mload (w2n w) s) s) /\
    tf = step_taint (mk_inst sa.cs_next_id MLOAD [Var root] [out]) s
      (update_var out (mload (w2n w) s) s) tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    lookup_var out t = SOME (mload (w2n w) s) /\
    op_taint tf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `op = Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[not_fresh_at_def,Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [Var root] [out]) s =
     OK (update_var out (mload (w2n w) s) s)` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_read1_def,eval_operand_def] >>
  `!out. inst_mem_below_frontier (mk_inst sa.cs_next_id MLOAD [Var root] [out]) s /\
     inst_dload_in_section (mk_inst sa.cs_next_id MLOAD [Var root] [out]) s` by
    simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      memSafeRunTheory.inst_dload_in_section_def,venomInstTheory.mk_inst_def,eval_operand_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out (mload (w2n w) s) s with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var root] [out])
       (update_var out (mload (w2n w) s) s),
     step_taint (mk_inst sa.cs_next_id MLOAD [Var root] [out]) s
       (update_var out (mload (w2n w) s) s) tn) /\
     sa.cs_current_bb = sb.cs_current_bb` by
    (gen_tac >>
     `!out. ptr_inst_ok D lo 0 ctx func G tn
       (mk_inst sa.cs_next_id MLOAD [Var root] [out]) s` by
       (gen_tac >> irule ptr_inst_ok_mload_lo >> simp[]) >>
     `MLOAD <> INVOKE /\ MLOAD <> GAS /\ ~is_terminator MLOAD` by
       simp[venomInstTheory.is_terminator_def] >>
     drule_all typed_copy_origin_ptr_emit_op_path >>
     disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`] mp_tac) >>
     gvs[] >> metis_tac[update_var_def]) >>
  gnvs[] >>
  conj_tac >- metis_tac[typed_copy_emit_op_fresh] >>
  simp[setup_mload_ghost |> SRULE []] >>
  simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE,state_frame_def] >>
  conj_tac >-
    simp[op_prov_def,step_prov_def,out_prov_def,set_prov_def,
      venomInstTheory.mk_inst_def,FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[decoderGhostFramePtrTheory.step_prov_other_output,
    decoderGhostFramePtrTheory.step_taint_other_output,venomInstTheory.mk_inst_def]
QED

(* Joint load recursion; semantic value recovery is done at this endpoint. *)
Theorem body_assign_tuple_load_all_core:
  !tys cenv root off sa elems sb s w G tn capacity lo ctx func explicit PG.
    compile_tuple_load_all cenv (Var root) tys off sa = (elems,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME w /\
    ptr_covers G tn root s capacity /\
    off + SUM (MAP (type_memory_bytes cenv) tys) <= capacity /\
    w2n w + capacity < dimword (:256) /\
    w2n w + capacity <= s.vs_alloca_next /\
    EVERY (\ty. is_word_type ty ==> type_memory_bytes cenv ty = 32) tys /\
    (!i j. i < LENGTH tys /\ is_word_type (EL i tys) /\
      w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) <= j /\
      j < w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32 ==>
      j NOTIN tn.t_mem) /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    LENGTH elems = LENGTH tys /\ sa.cs_next_var <= sb.cs_next_var /\
    ?t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. i < LENGTH tys ==>
        ?x. EL i elems = Var x /\ not_fresh_at sb x /\ op_taint tf (Var x) = {} /\
          (if is_word_type (EL i tys) then op_prov Gf (Var x) = NONE
           else ptr_covers Gf tf x t (type_memory_bytes cenv (EL i tys))))
Proof
  Induct
  >- (rpt gen_tac >> simp[compile_tuple_load_all_def,comp_return_def] >>
      strip_tac >> gvs[] >> qexistsl_tac [`s`,`G`,`tn`] >>
      simp[exprLoweringPropsTheory.emitted_insts_def,exprLoweringPropsTheory.run_inst_seq_def] >>
      conj_tac >- metis_tac[cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
      simp[venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_tuple_load_all_def,comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `compile_load_memory _ _ sm = (v,sh)` >>
  rename1 `compile_tuple_load_all _ _ _ _ sh = (rest,sb)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `cs_extends sm sh /\ sm.cs_next_var <= sh.cs_next_var` by
    (Cases_on `is_word_type h` >>
     gvs[compile_load_memory_def,comp_return_def] >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,cs_extends_refl]) >>
  `cs_extends sh sb /\ sh.cs_next_var <= sb.cs_next_var` by
    metis_tac[stmtSimReturnTheory.compile_tuple_load_all_grows] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sh func /\ fn_has_code sh sb func` by
    metis_tac[fn_has_code_split] >>
  `off + type_memory_bytes cenv h <= capacity` by decide_tac >>
  `w2n w + capacity < dimword (:256)` by decide_tac >>
  drule_all body_assign_tuple_offset_add_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sm) s =
     OK (t with vs_inst_idx := s.vs_inst_idx)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     `out = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
     simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomInstTheory.mk_inst_def,eval_operand_def] >>
     simp[venom_state_component_equality,update_var_def]) >>
  `?x u GH th.
     v = Var x /\ not_fresh_at sh x /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,GH,th)) /\
     run_inst_seq (emitted_insts sa sh) s =
       OK (u with vs_inst_idx := s.vs_inst_idx) /\
     ~u.vs_halted /\ u.vs_current_bb = sh.cs_current_bb /\
     u.vs_inst_idx = LENGTH sh.cs_current_insts /\
     state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
     u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
     u.vs_alloca_next = s.vs_alloca_next /\
     th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
     th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
     (!y. not_fresh_at sa y ==>
       lookup_var y u = lookup_var y s /\ FLOOKUP GH y = FLOOKUP G y /\
       op_taint th (Var y) = op_taint tn (Var y)) /\
     op_taint th (Var x) = {} /\
     (if is_word_type h then op_prov GH (Var x) = NONE
      else ptr_covers GH th x u (type_memory_bytes cenv h))` by
    (Cases_on `is_word_type h`
     >- (qpat_x_assum `compile_load_memory _ _ _ = _` mp_tac >>
         simp[compile_load_memory_def] >> strip_tac >>
         `type_memory_bytes cenv h = 32` by metis_tac[] >>
         `ptr_covers Gf tf out t 32` by metis_tac[] >>
         `off < dimword (:256) /\ w2n w + off < dimword (:256)` by decide_tac >>
         `w2n (w+n2w off) = w2n w+off` by
           simp[wordsTheory.word_add_def,wordsTheory.w2n_n2w] >>
         `w2n (w+n2w off)+32 <= t.vs_alloca_next` by decide_tac >>
         `!j. w2n (w+n2w off) <= j /\ j < w2n (w+n2w off)+32 ==>
           j NOTIN tf.t_mem` by
           (rpt strip_tac >>
            qpat_x_assum `!i j. _ ==> j NOTIN tn.t_mem`
              (qspecl_then [`0`,`j`] mp_tac) >> simp[] >> metis_tac[]) >>
         `allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
           (simp[allocas_from_def,allocas_below_fmp_def,update_var_def] >>
            fs[allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
         drule_all body_assign_tuple_mload_path >>
         disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
         `run_inst_seq (emitted_insts sm sh) (t with vs_inst_idx := s.vs_inst_idx) =
            OK (t' with vs_inst_idx := s.vs_inst_idx)` by
           (qpat_assum `emit_op MLOAD _ _ = _`
              (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
            `out' = STRING #"%" (toString sm.cs_next_var)` by metis_tac[operand_11] >>
            simp[exprLoweringPropsTheory.run_inst_seq_def,
              venomExecSemanticsTheory.step_inst_base_opcode_eqs,
              venomExecSemanticsTheory.exec_read1_def,
              venomInstTheory.mk_inst_def,eval_operand_def,lookup_var_def,mload_def,FLOOKUP_UPDATE] >>
            simp[venom_state_component_equality,update_var_def]) >>
         map_every (fn q => qpat_x_assum q kall_tac)
           [`t = _`,`t' = _`,`Gf = _`,`Gf' = _`,`tf = _`,`tf' = _`] >>
         qexistsl_tac [`out'`,`t'`,`Gf'`,`tf'`] >>
         simp[] >>
         conj_tac >- (gen_tac >>
           qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK t,Gf,tf)`
             (qspec_then `D` (mp_then Any (irule o SRULE [])
               fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >> simp[]) >>
         conj_tac >- (irule emitHelperPropsTheory.run_inst_seq_compose_ok >>
           qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx`,`sm`] >>
           simp[] >> metis_tac[emitHelperPropsTheory.inst_extends_emit_op]) >>
         conj_tac >- (fs[state_frame_def] >> metis_tac[]) >>
         metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     qpat_x_assum `compile_load_memory _ _ _ = _` mp_tac >>
     simp[compile_load_memory_def,comp_return_def] >> strip_tac >>
     map_every (fn q => qpat_x_assum q kall_tac) [`t = _`,`Gf = _`,`tf = _`] >>
     gvs[] >> qexistsl_tac [`t`,`Gf`,`tf`] >>
     simp[] >> fs[state_frame_def]) >>
  `not_fresh_at sh root` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var root u = SOME w` by metis_tac[] >>
  `ptr_covers GH th root u capacity` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `off + type_memory_bytes cenv h + SUM (MAP (type_memory_bytes cenv) tys) <= capacity` by
    decide_tac >>
  `allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    ((fs[allocas_from_def,allocas_below_fmp_def,state_frame_def]) >> (metis_tac[allocas_from_def, allocas_below_fmp_def, state_frame_def])) >>
  `!i j. i < LENGTH tys /\ is_word_type (EL i tys) /\
    off + type_memory_bytes cenv h +
      (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + w2n w) <= j /\
    j < off + type_memory_bytes cenv h +
      (SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + (w2n w+32)) ==>
    j NOTIN th.t_mem` by
    (rpt strip_tac >>
     qpat_x_assum `!i j. _ ==> j NOTIN tn.t_mem`
       (qspecl_then [`SUC i`,`j`] mp_tac) >> simp[] >> metis_tac[]) >>
  `capacity + w2n w <= u.vs_alloca_next` by simp[] >>
  qpat_x_assum `!cenv' root' off' sa' elems' sb' s'' w' G' tn' capacity' lo' ctx' func' explicit PG. _`
    (fn thm => drule_all thm) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  map_every (fn q => qpat_x_assum q kall_tac) [`t = _`,`Gf = _`,`tf = _`] >>
  rename1 `run_inst_seq (emitted_insts sh sb) u = OK (z with vs_inst_idx := _)` >>
  `(!x. Var root = Var x ==> not_fresh_at sh x) /\
   eval_operand (Var root) u = SOME w` by simp[eval_operand_def] >>
  `inst_extends sh sb` by
    (drule_all (cj 1 tupleLoadPropsTheory.compile_tuple_load_all_values) >>
     simp[emitHelperPropsTheory.inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sb)` by
    (drule_all (cj 4 tupleLoadPropsTheory.compile_tuple_load_all_values) >>
     simp[EVERY_MEM]) >>
  `run_inst_seq (emitted_insts sh sb) (u with vs_inst_idx := s.vs_inst_idx) =
     OK (z with vs_inst_idx := s.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx,instIdxIndepTheory.exec_result_map_def] >>
  `inst_extends sa sh` by
    (Cases_on `is_word_type h` >>
     gvs[compile_load_memory_def,comp_return_def] >>
     metis_tac[emitHelperPropsTheory.inst_extends_emit_op,
       emitHelperPropsTheory.inst_extends_trans,emitHelperPropsTheory.inst_extends_refl]) >>
  conj_tac >- simp[] >>
  conj_tac >- decide_tac >>
  qexistsl_tac [`z`,`Gf'`,`tf'`] >> simp[] >>
  conj_tac >- (gen_tac >>
    qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK u,GH,th)`
      (qspec_then `D` (mp_then Any (irule o SRULE [])
        fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >> simp[]) >>
  conj_tac >- (irule emitHelperPropsTheory.run_inst_seq_compose_ok >>
    qexistsl_tac [`u with vs_inst_idx := s.vs_inst_idx`,`sh`] >> simp[]) >>
  fs[state_frame_def] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qx_gen_tac `i` >> strip_tac >> Cases_on `i`
  >- (simp[] >>
      conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      `op_taint tf' (Var x) = op_taint th (Var x) /\
       FLOOKUP Gf' x = FLOOKUP GH x /\
       lookup_var x z = lookup_var x u` by metis_tac[] >>
      Cases_on `is_word_type h` >> gvs[op_prov_def] >>
      irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

(* Typed and relational postconditions at the joint load endpoint. *)
Theorem body_assign_tuple_load_all_path:
  compile_tuple_load_all cenv (Var root) tys off sa = (elems,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME w /\
  ptr_covers G tn root s capacity /\ off + type_memory_size_list tvs <= capacity /\
  w2n w + capacity < dimword (:256) /\ w2n w + capacity <= s.vs_alloca_next /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n w + off) mem) /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  LENGTH elems = LENGTH tys /\ local_ptrs_reserved cenv sb /\
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es Gf tf t) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==>
      ptr_covers Gf tf x t cap) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      tuple_in_memory vs tvs (w2n w + off) mem) /\
    (!i. i < LENGTH tys ==>
      ?x. EL i elems = Var x /\ not_fresh_at sb x /\ op_taint tf (Var x) = {} /\
        (if is_word_type (EL i tys) then
           lookup_var x t = SOME (typed_val_to_w256 (EL i tvs) (EL i vs)) /\
           op_prov Gf (Var x) = NONE
         else lookup_var x t = SOME (n2w (w2n w + off +
                SUM (MAP type_memory_size (TAKE i tvs)))) /\
           ptr_covers Gf tf x t (type_memory_size (EL i tvs))))
Proof
  strip_tac >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `!i. SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
       SUM (MAP type_memory_size (TAKE i tvs))` by
    metis_tac[tuple_prefix_sizes] >>
  `SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs` by
    (first_x_assum (qspec_then `LENGTH tys` mp_tac) >>
     simp[valueEncodingProofsTheory.type_memory_size_list_sum]) >>
  `EVERY (\ty. is_word_type ty ==> type_memory_bytes cenv ty = 32) tys` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     fs[LIST_REL_EL_EQN] >> metis_tac[stmtSimReturnTheory.word_type_sizes]) >>
  `w2n w + off + type_memory_size_list tvs < dimword (:256)` by decide_tac >>
  `!i j. i < LENGTH tys /\ is_word_type (EL i tys) /\
    w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) <= j /\
    j < w2n w + off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) + 32 ==>
    j NOTIN tn.t_mem` by
    (rpt strip_tac >> metis_tac[tuple_word_member_clean]) >>
  `off + SUM (MAP (type_memory_bytes cenv) tys) <= capacity` by simp[] >>
  drule_all body_assign_tuple_load_all_core >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule compile_tuple_load_all_values >>
  disch_then (qspecl_then [`s`,`w`] mp_tac) >>
  (impl_tac >- simp[eval_operand_def]) >> strip_tac >>
  `t' = t with vs_inst_idx := s.vs_inst_idx` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t' = s with vs_vars := _` kall_tac >>
  qpat_x_assum `t' = t with vs_inst_idx := _` SUBST_ALL_TAC >>
  qpat_x_assum `eval_operands _ _ = _` mp_tac >>
  rewrite_tac[instIdxIndepTheory.eval_ops_inst_idx] >> disch_tac >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >>
    irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule ghost_inv_at_exterior_frame >>
    goal_assum (drule_at Any) >> fs[state_frame_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  qx_gen_tac `i` >> strip_tac >>
  `i < LENGTH tys` by simp[] >>
  qpat_x_assum `!i. i < LENGTH tys ==> ?x. _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  qexists `x` >> asm_rewrite_tac[] >>
  `type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs)` by
    (qpat_assum `LIST_REL (\ty tv. type_memory_bytes cenv ty = _) _ _`
       (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[]) >>
  `eval_operand (EL i elems) t = SOME
    (if is_word_type (EL i tys) then
       mem_word_at (w2n (w + n2w (off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys)))) ) s.vs_memory
     else w + n2w (off + SUM (MAP (type_memory_bytes cenv) (TAKE i tys))))` by
    (drule eval_operands_index >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  drule tuple_typed_load_value >>
  disch_then (drule_at (Pat `values_have_types _ _`)) >>
  disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
  disch_then (qspecl_then [`n2w (w2n w + off)`,`s.vs_memory`,`i`] mp_tac) >>
  `w2n w + off < dimword (:256)` by decide_tac >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w] >>
    qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _`
      (qspec_then `s.vs_memory` mp_tac) >>
    simp_tac bool_ss [mem_agree_outside_def] >> metis_tac[ADD_COMM])) >>
  simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `eval_operand (EL i elems) t = _` mp_tac >>
  qpat_x_assum `if is_word_type _ then _ else _` mp_tac >>
  qpat_x_assum `EL i elems = _` mp_tac >>
  qpat_x_assum `type_memory_bytes cenv (EL i tys) = _` mp_tac >>
  qpat_x_assum `!i. SUM _ = _` (qspec_then `i` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `is_word_type (EL i tys)` >>
  Cases_on `w` >>
  asm_simp_tac std_ss [wordsTheory.word_add_n2w,wordsTheory.w2n_n2w,
    LESS_MOD,eval_operand_def,AC ADD_ASSOC ADD_COMM]
QED

(* A normal storage head changes neither the staged tuple nor loaded operands. *)
Theorem body_assign_tuple_storage_head_path:
  compile_store_at_loc cenv.ce_imm_alloca dst value
    (SOME (if tr then LocTransient else LocStorage)) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME slot /\ eval_operand value s = SOME w /\
  op_taint tn dst = {} /\ op_taint tn value = {} /\
  write_storage_slot cx tr slot tv v es = (INL (),es') /\
  encode_value tv v = SOME [(0,w)] /\ es'.scopes = es.scopes ==>
  ?t tf.
    t = ((if tr then tstore slot w s else sstore slot w s)
      with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tf = step_taint (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE)
      [dst;value] []) s (if tr then tstore slot w s else sstore slot w s) tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tf)) /\
    (!H. stmt_state_rel H ctx func cenv cx es s /\
      (!u mem. storage_dead H tr (update_storage slot u mem) = storage_dead H tr mem) ==>
      stmt_state_rel H ctx func cenv cx es' t) /\
    (!H D d. dead_lo_ok H D lo cenv cx /\
      ghost_inv_at D lo d cenv cx es G tn s /\
      (!u mem. storage_dead H tr (update_storage slot u mem) = storage_dead H tr mem) ==>
      ghost_inv_at D lo d cenv cx es' G tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    t.vs_immutables = s.vs_immutables /\ t.vs_call_ctx = s.vs_call_ctx /\
    tf.t_mem = tn.t_mem /\ tf.t_var = tn.t_var /\ tf.t_imm = tn.t_imm /\
    (!x. lookup_var x t = lookup_var x s /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x cap. ptr_covers G tn x s cap ==> ptr_covers G tf x t cap)
Proof
  strip_tac >>
  `emit_void (if tr then TSTORE else SSTORE) [dst;value] sa = ((),sb)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `u = if tr then tstore slot w s else sstore slot w s` >>
  qabbrev_tac `un = step_taint
    (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;value] []) s u tn` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    (Cases_on `tr` >> simp[Abbr `u`,tstore_def,sstore_def]) >>
  `un.t_mem = tn.t_mem /\ un.t_var = tn.t_var /\ un.t_imm = tn.t_imm /\
   un.t_stor = (if tr then tn.t_stor else {(k,b) | (k,b) IN tn.t_stor /\ k <> slot}) /\
   un.t_trans = (if tr then {(k,b) | (k,b) IN tn.t_trans /\ k <> slot} else tn.t_trans)` by
    (simp[Abbr `un`] >> irule clean_storage_step_taint_ptr >> simp[]) >>
  `un = (if tr then tn with t_trans := key_update tn.t_trans slot {}
         else tn with t_stor := key_update tn.t_stor slot {})` by
    (Cases_on `tr` >> simp[taint_component_equality,key_update_def]) >>
  qexistsl [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`un`] >>
  simp[] >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `u`] >>
      drule_all storage_word_store_origin_ptr >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx,Abbr `u`] >>
      drule_all stmt_state_rel_write_storage_word >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ghost_inv_at_inst_idx] >>
      qpat_x_assum `un = _` kall_tac >>
      `stor_taint_ok_at D un u` by
        (fs[ghost_inv_at_def,dead_lo_ok_def,stor_taint_ok_at_def] >>
         Cases_on `tr` >>
         gvs[Abbr `u`,sourceUnitExecutionTheory.cx_dead_def,sstore_def,tstore_def,lookup_account_def,
             combinTheory.APPLY_UPDATE_THM] >>
         simp[pred_setTheory.SUBSET_DEF] >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
      qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[ghost_inv_at_def] >> strip_tac >>
      Cases_on `tr` >>
      gvs[Abbr `u`,tstore_def,sstore_def,allocas_from_def,op_taint_def,
          lookup_var_def,ptr_covers_def,key_update_def,stor_taint_ok_at_def] >>
      (Cases_on `d` >-
        (gvs[return_buf_ptr_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
       rename1 `return_buf_ptr (SOME rb) cenv G tn s` >>
       PairCases_on `rb` >>
       gvs[return_buf_ptr_def,ptr_covers_def,op_taint_def,lookup_var_def] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  Cases_on `tr` >>
  simp[Abbr `u`,tstore_def,sstore_def,lookup_var_def,op_taint_def,ptr_covers_def]
QED

(* Source observations supply the dead-slot frame for a nonlocal tuple head. *)
Theorem body_assign_tuple_nonlocal_write_ready:
  tuple_target_aligned cenv cx g ty tv /\
  (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
  assign_tuple_targets cx g v es = (INL (),es') ==>
  ?bt tr slot obs ee.
    g = BaseTarget bt /\ ee = es with storage_trace := obs /\
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),ee) /\
    write_storage_slot cx tr slot tv v ee = (INL (),es') /\
    encode_value tv v = SOME [(0,typed_val_to_w256 tv v)] /\
    ~cx.txn.is_static /\ es'.scopes = es.scopes /\
    (!st0 H. valid_horizon cx st0 H es'.storage_trace ==>
      !u mem. storage_dead H tr (update_storage slot u mem) = storage_dead H tr mem)
Proof
  simp[tupleTargetStorePropsTheory.tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- suspend "scalar" >>
  suspend "field"
QED

Resume body_assign_tuple_nonlocal_write_ready[scalar]:
  drule_all tupleTargetStorePropsTheory.tuple_target_toplevel_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tupleTargetStorePropsTheory.tuple_target_storage_assignment >> strip_tac >>
  `~cx.txn.is_static` by
    (CCONTR_TAC >> fs[vyperStorageBackendTheory.write_storage_slot_eq]) >>
  drule_all stmtSimAssignStorageFactsTheory.encode_value_word_typed >> strip_tac >>
  drule tupleTargetStorePropsTheory.tuple_target_storage_scope_frame >> strip_tac >>
  qexistsl [`tr`, `n2w k`, `es.storage_trace ++ [StorageRoot tr k tv]`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H
    (es with storage_trace := es.storage_trace ++ [StorageRoot tr k tv]).storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:unit``]
       vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl [`write_storage_slot cx tr (n2w k) tv v`, `INL ()`, `es'`] >>
     simp[vyperStorageTraceTheory.storage_trace_frame_write_storage_slot]) >>
  `MEM (tr,n2w k,tv) (FST H)` by
    (qpat_x_assum `valid_horizon _ _ _ (es with storage_trace := _).storage_trace` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       vyperStorageFootprintTheory.storage_trace_regions_def, EVERY_APPEND]) >>
  `type_slot_size tv = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  metis_tac[accountsRelPropsTheory.storage_dead_update_word_region]
QED

Resume body_assign_tuple_nonlocal_write_ready[field]:
  qmatch_asmsub_abbrev_tac `struct_field_slot fs fld = SOME (off,tv)` >>
  drule_all tupleTargetStorePropsTheory.tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tupleTargetStorePropsTheory.tuple_target_storage_assignment >> strip_tac >>
  `~cx.txn.is_static` by
    (CCONTR_TAC >> fs[vyperStorageBackendTheory.write_storage_slot_eq]) >>
  drule_all stmtSimAssignStorageFactsTheory.encode_value_word_typed >> strip_tac >>
  drule tupleTargetStorePropsTheory.tuple_target_storage_scope_frame >> strip_tac >>
  qexistsl [`tr`, `n2w k + n2w off`,
    `es.storage_trace ++ [StorageRoot tr k (StructTV fs)]`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H
    (es with storage_trace := es.storage_trace ++ [StorageRoot tr k (StructTV fs)]).storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:unit``]
       vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl [`write_storage_slot cx tr (n2w k + n2w off) tv v`, `INL ()`, `es'`] >>
     simp[vyperStorageTraceTheory.storage_trace_frame_write_storage_slot]) >>
  `MEM (tr,n2w k,StructTV fs) (FST H)` by
    (qpat_x_assum `valid_horizon _ _ _ (es with storage_trace := _).storage_trace` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       vyperStorageFootprintTheory.storage_trace_regions_def, EVERY_APPEND]) >>
  `type_slot_size tv = 1` by metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  metis_tac[accountsRelPropsTheory.storage_dead_update_struct_word_field]
QED

Finalise body_assign_tuple_nonlocal_write_ready

(* A successful nonlocal head observes its root before the joint slot store. *)
Theorem body_assign_tuple_nonlocal_head_full_path:
  compile_tuple_store_all cenv [ty] [g] [op] sa = ((),sb) /\
  assign_tuple_targets cx g v es = (INL (),es') /\
  tuple_target_aligned cenv cx g ty tv /\
  (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\ op_taint tn op = {} /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_call_ctx.cc_static = cx.txn.is_static /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  es'.scopes = es.scopes /\
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    t.vs_immutables = s.vs_immutables /\ t.vs_call_ctx = s.vs_call_ctx /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==>
      ptr_covers Gf tf x t cap) /\
    (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
      stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es' t) /\
    (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
      storage_well_formed_on cx es (FST H) ==>
      storage_well_formed_on cx es' (FST H)) /\
    (!st0 H D d. valid_horizon cx st0 H es'.storage_trace /\
      dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d cenv cx es' Gf tf t)
Proof
  strip_tac >> drule_all body_assign_tuple_nonlocal_write_ready >>
  disch_then (qx_choosel_then [`bt`,`tr`,`slot`,`obs`,`ee`]
    (map_every assume_tac o CONJUNCTS)) >>
  `well_formed_type_value tv` by
    (fs[tuple_target_aligned_def] >>
     metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed]) >>
  `!st0 H. valid_horizon cx st0 H es'.storage_trace /\
    storage_well_formed_on cx es (FST H) ==>
    storage_well_formed_on cx es' (FST H)` by
    (rpt strip_tac >> irule tuple_target_storage_write_wf >>
     gvs[] >> metis_tac[]) >>
  gvs[tuple_target_aligned_def] >- suspend "scalar" >>
  suspend "field"
QED

Resume body_assign_tuple_nonlocal_head_full_path[scalar]:
  drule_all tuple_target_toplevel_place >>
  disch_then (qspec_then `es` assume_tac) >> gvs[] >>
  drule_all stmtSimAssignStorageFactsTheory.compile_get_target_ptr_toplevel >>
  disch_then (qspec_then `sa` assume_tac) >> gvs[] >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def,comp_return_def] >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k) /\
   op_taint tn (Lit (n2w k)) = {}` by simp[eval_operand_def,op_taint_def] >>
  `es'.scopes = (es with storage_trace := obs).scopes` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    body_assign_tuple_storage_head_path) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`t`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `!H. stmt_state_rel _ _ _ _ _ _ _ /\ _ ==> _`
    (mk_asm "store_rel") >>
  qpat_x_assum `!H D d. _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
    (mk_asm "store_ghost") >>
  qexistsl [`t`,`G`,`tf`] >>
  qpat_x_assum `t = _` kall_tac >> qpat_x_assum `tf = _` kall_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!st0 H. valid_horizon _ _ _ _ ==> _`
        (drule_then assume_tac) >>
      asm "store_rel" (qspec_then `H` mp_tac) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_storage_trace]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!st0 H. valid_horizon _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  asm "store_ghost" (qspecl_then [`H`,`D`,`d`] mp_tac) >>
  simp[bodyPtrDefsTheory.ghost_inv_at_storage_trace]
QED

Resume body_assign_tuple_nonlocal_head_full_path[field]:
  drule_all tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >> gvs[] >>
  Cases_on `emit_op ADD [Lit (n2w k); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] sa` >>
  rename1 `emit_op ADD _ sa = (dst,sm)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def,comp_return_def] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `cs_extends sm sb` by
    metis_tac[externalEntryShapeTheory.compile_store_at_loc_labels,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] body_assign_tuple_field_add_path) >>
  disch_then (qspecl_then [`tn`,`explicit`,`es`,`cx`,`PG`,`G`]
    (qx_choosel_then [`out`,`mid`,`GM`,`tm`] (map_every assume_tac o CONJUNCTS))) >>
  map_every (fn q => qpat_x_assum q kall_tac) [`mid = _`,`GM = _`,`tm = _`] >>
  qpat_x_assum `!H. stmt_state_rel _ _ _ _ _ _ _ ==> _` (mk_asm "add_rel") >>
  qpat_x_assum `!D d. ghost_inv_at _ _ _ _ _ _ _ _ _ ==> _` (mk_asm "add_ghost") >>
  `mid.vs_fmp = s.vs_fmp /\ mid.vs_immutables = s.vs_immutables /\
   mid.vs_call_ctx = s.vs_call_ctx` by fs[state_frame_def] >>
  `allocas_from lo mid /\ lo <= mid.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp mid)` by
    (fs[allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
  `eval_operand dst mid = SOME (n2w k + n2w (struct_field_offset_slots
     (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) /\
   op_taint tm dst = {}` by simp[eval_operand_def] >>
  `eval_operand op mid = SOME (typed_val_to_w256 tv v) /\ op_taint tm op = {}` by
    (Cases_on `op` >> fs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `es'.scopes = (es with storage_trace := obs).scopes` by simp[] >>
  `~mid.vs_call_ctx.cc_static` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    body_assign_tuple_storage_head_path) >>
  disch_then (qspecl_then [`explicit`,`PG`,`GM`]
    (qx_choosel_then [`t`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `!H. stmt_state_rel _ _ _ _ _ _ _ /\ _ ==> _`
    (mk_asm "store_rel") >>
  qpat_x_assum `!H D d. _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
    (mk_asm "store_ghost") >>
  qpat_x_assum `t = _` kall_tac >> qpat_x_assum `tf = _` kall_tac >>
  qexistsl [`t`,`GM`,`tf`] >> simp[] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (s,_,_) _ _`
        (qspec_then `D` mp_tac) >>
      qpat_x_assum `!D. gas_origin_ptr_path _ (mid,_,_) _ _`
        (qspec_then `D` mp_tac) >>
      POP_ASSUM_LIST (K all_tac) >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!st0 H. valid_horizon _ _ _ _ ==> _`
        (drule_then assume_tac) >>
      asm "add_rel" (drule_then assume_tac) >>
      asm "store_rel" (qspec_then `H` mp_tac) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_storage_trace]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!st0 H. valid_horizon _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  asm "add_ghost" (drule_then assume_tac) >>
  asm "store_ghost" (qspecl_then [`H`,`D`,`d`] mp_tac) >>
  simp[bodyPtrDefsTheory.ghost_inv_at_storage_trace]
QED

Finalise body_assign_tuple_nonlocal_head_full_path

(* One local write, at the current source scope, retains the tuple snapshot. *)
Theorem body_assign_tuple_local_head_full_path:
  compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] sa = ((),sb) /\
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') /\
  tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty entry.type /\
  tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty entry.type v /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  lookup_var p s = SOME dw /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s id (w2n dw) cap /\
  type_memory_size entry.type <= cap /\ lo <= w2n dw /\
  ptr_covers G tn p s (type_memory_size entry.type) /\
  w2n dw + type_memory_size entry.type < dimword (:256) /\
  w2n dw + type_memory_size entry.type <= s.vs_alloca_next /\
  value_has_type entry.type v /\ val_wf entry.type v /\
  (if is_word_type ty then
     eval_operand op s = SOME (typed_val_to_w256 entry.type v) /\ op_taint tn op = {}
   else ?xs sw. op = Var xs /\ not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory entry.type v (w2n sw) mem) /\
     ptr_covers G tn xs s (type_memory_size entry.type) /\
     w2n sw + type_memory_size entry.type < dimword (:256) /\
     w2n sw + type_memory_size entry.type <= s.vs_alloca_next /\
     (w2n sw + type_memory_size entry.type <= w2n dw \/
      w2n dw + type_memory_size entry.type <= w2n sw)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  (b + type_memory_size (TupleTV tvs) <= w2n dw \/
   w2n dw + type_memory_size entry.type <= b) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size entry.type) s t /\
    (!H D d. stmt_state_rel H ctx func cenv cx es s /\
      ghost_inv_at D lo d cenv cx es G tn s ==>
      stmt_state_rel H ctx func cenv cx es' t /\
      ghost_inv_at D lo d cenv cx es' Gf tf t) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!name a len. local_region cenv es'.scopes t name a len <=>
      local_region cenv es.scopes s name a len) /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size entry.type) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      (!name a len. local_region cenv es.scopes s name a len ==>
        off + sz <= a \/ a + len <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory /\
      (!i. off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `cenv.ce_var_type id = SOME ty /\
   evaluate_type (get_tenv cx) ty = SOME entry.type /\
   type_memory_bytes cenv ty = type_memory_size entry.type /\
   entry.assignable /\
   (is_word_type ty ==> store_lays_out entry.type entry.type v)` by
    (gvs[tuple_target_aligned_local,tuple_target_layout_local]) >>
  `es' = es with scopes := pre ++
     (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` by
    (drule_all tuple_target_local_assignment >> simp[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  drule_all tuple_store_local_singleton_code >> strip_tac >>
  `?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory entry.type v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory entry.type v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size entry.type) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size entry.type) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` by
    (Cases_on `is_word_type ty`
     >- suspend "word" >>
     qpat_x_assum `if is_word_type ty then _ else _` mp_tac >>
     asm_rewrite_tac[] >>
     disch_then (qx_choose_then `xs` (qx_choose_then `sw`
       (map_every assume_tac o CONJUNCTS))) >>
     qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
     `type_widens_to (get_tenv cx) ty ty` by simp[type_widens_to_refl] >>
     qpat_x_assum `(if is_word_type ty then _ else _) sa = _` mp_tac >>
     asm_rewrite_tac[] >> disch_tac >>
     Q.SUBGOAL_THEN `type_memory_size entry.type = 0 \/
       w2n sw + type_memory_size entry.type <= s.vs_alloca_next` assume_tac
     >- simp[] >>
     Q.SUBGOAL_THEN `type_memory_size entry.type = 0 \/
       w2n dw + type_memory_size entry.type <= s.vs_alloca_next` assume_tac
     >- simp[] >>
     drule_all body_full_memory_store_path >>
     disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
     qexistsl_tac [`t`,`Gf`,`tf`] >> simp[]) >>
  suspend "post"
QED

Resume body_assign_tuple_local_head_full_path[word]:
  qpat_x_assum `if is_word_type ty then _ else _` mp_tac >>
  asm_rewrite_tac[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `store_lays_out entry.type entry.type v` by metis_tac[] >>
  `type_memory_size entry.type = 32` by fs[store_lays_out_def] >>
  qpat_x_assum `(if is_word_type ty then _ else _) sa = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_void_same_blocks,same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MSTORE [Var p;op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `u = mstore (w2n dw) (typed_val_to_w256 entry.type v) s` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id MSTORE [Var p;op] []` >>
  qabbrev_tac `tf = step_taint ins s u tn` >>
  `step_prov PG G ins u = G /\ tf.t_var = tn.t_var /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   tf.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` by
    (simp[Abbr `tf`,Abbr `ins`,Abbr `u`] >>
     irule mstore_ghost_frame >> simp[]) >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,`G`,`tf`] >>
  conj_tac
  >- (gen_tac >>
      `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
         step_prov PG G ins u,step_taint ins s u tn)` by
        (qunabbrev_tac `ins` >>
         irule (Q.INST [`i` |-> `mk_inst sa.cs_next_id MSTORE [Var p;op] []`]
           fragGasSeqPtrTheory.straight_line_origin_ptr_edge |>
           SIMP_RULE (srw_ss()) []) >>
         simp[venomInstTheory.is_terminator_def,
           below_frontier_MSTORE,eval_operand_def,Abbr `u`,
           venomExecSemanticsTheory.step_inst_base_opcode_eqs,
           venomExecSemanticsTheory.exec_write2_def] >>
         gvs[exprPtrUnwrapCopyEdgesTheory.ptr_inst_ok_mstore_tainted]) >>
      `~u.vs_halted` by simp[Abbr `u`,mstore_def] >>
      qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
      simp[] >> strip_tac >>
      drule (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      disch_then (qspec_then `[]` (irule o SRULE [])) >>
      irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>
  conj_tac
  >- (simp[Abbr `u`] >> fs[store_lays_out_def]) >>
  conj_tac
  >- (simp[Abbr `u`] >> rpt strip_tac >>
      irule store_lays_out_robust_ptr >> goal_assum (drule_at Any) >> simp[]) >>
  `tf.t_imm = tn.t_imm` by
    (simp[Abbr `tf`,Abbr `ins`] >>
     irule (cj 3 decoderGhostFramePtrTheory.step_taint_nonmemory_frame) >> simp[]) >>
  simp[Abbr `u`,typed_copy_mstore_state_frame,mstore_def,
    write_memory_with_expansion_def,lookup_var_def,op_taint_def]
QED

Resume body_assign_tuple_local_head_full_path[post]:
  qexistsl_tac [`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
        (qspec_then `D` assume_tac) >>
      drule_all body_assign_tuple_local_copy_snapshot_post >>
      asm_rewrite_tac[] >> strip_tac >> simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  asm_rewrite_tac[] >> conj_tac
  >- (drule tuple_target_local_domain_frame >>
      disch_then (qspec_then `v` assume_tac) >>
      simp[] >> rpt gen_tac >>
      `local_region cenv
        (pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
        t name a len <=> local_region cenv es.scopes t name a len` by
        metis_tac[tupleMemoryFrameTheory.local_region_scopes_domain] >>
      asm_rewrite_tac[] >> irule local_region_lookup_cong >>
      rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size entry.type) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (drule val_footprint_le >> strip_tac >>
      `!i. b <= i /\ i < b + val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) ==>
        ~(w2n dw <= i /\ i < w2n dw + type_memory_size entry.type)` by
        (rpt strip_tac >> decide_tac) >>
      qpat_assum `!mem. _ ==> val_in_memory (TupleTV tvs) _ b mem`
        (mp_then (Pos (el 5)) mp_tac robust_val_in_memory_exterior_frame) >>
      disch_then (qspecl_then [`tf.t_mem`, `t.vs_memory`,
        `{i | w2n dw <= i /\ i < w2n dw + type_memory_size entry.type}`] mp_tac) >>
      simp[]) >>
  conj_tac >- (rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name a len. local_region _ _ _ _ _ _ ==> _`
    (qspecl_then [`id`,`w2n dw`,`cap`] mp_tac) >>
  asm_rewrite_tac[] >> disch_tac >> conj_tac
  >- (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
      simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  `~(w2n dw <= i /\ i < w2n dw + type_memory_size entry.type)` by decide_tac >>
  metis_tac[]
QED

Finalise body_assign_tuple_local_head_full_path

Theorem body_assign_tuple_static_head_full_exit:
  !ctx func cenv cx s g ty tv v op st sf RetQ RetP ee lo explicit PG G tn.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    op_taint tn op = {} /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s.vs_call_ctx.cc_static = cx.txn.is_static /\ fn_has_code st sf func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ cx.txn.is_static ==>
    ?r Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tf)) /\
      exit_result r /\
      (!H tail. stmt_exit (RetQ H) (ee with gas_obs := tail)
        (INR (Error (RuntimeError "write in static context"))) r) /\
      (!H tail. stmt_exit_ptr (RetP H) (ee with gas_obs := tail)
        (INR (Error (RuntimeError "write in static context"))) (Gf,tf) r)
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- (drule_all compile_get_target_ptr_toplevel >>
      disch_then (qspec_then `st` assume_tac) >> gvs[] >>
      drule_all tuple_store_word_step >> strip_tac >>
      qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
      gvs[compile_tuple_store_all_def, comp_return_def] >>
      `s.vs_call_ctx.cc_static` by metis_tac[] >>
      `emit_void (if tr then TSTORE else SSTORE) [Lit (n2w k); op] st = ((),sf)` by
        (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
      `eval_operand (Lit (n2w k)) s = SOME (n2w k) /\
       op_taint tn (Lit (n2w k)) = {}` by simp[eval_operand_def,op_taint_def] >>
      qexistsl_tac [`Abort ExHalt_abort (halt_state (set_returndata [] s))`,`G`,`tn`] >>
      simp[exit_result_def,stmt_exit_def,stmt_exit_ptr_def,expr_exit_def] >>
      gen_tac >> irule storage_emit_static_origin_ptr >> metis_tac[]) >>
  Cases_on `emit_op ADD [Lit (n2w k); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] st` >>
  rename1 `emit_op ADD _ st = (dst,sp)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  `cs_extends st sp /\ cs_extends sp sf` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def] >>
     metis_tac[ci_mono_emit_op,ci_mono_emit_void,ci_mono_def,pairTheory.SND]) >>
  `fn_has_code st sp func /\ fn_has_code sp sf func` by
    metis_tac[fn_has_code_split] >>
  drule_all body_assign_tuple_field_add_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`ee`,`cx`,`PG`,`G`] mp_tac) >>
  disch_then (qx_choosel_then [`out`,`mid`,`Gm`,`tm`] strip_assume_tac) >>
  `eval_operand op mid = SOME (typed_val_to_w256 tv v) /\
   op_taint tm op = {}` by
    (Cases_on `op` >> gvs[eval_operand_def,op_taint_def]) >>
  `mid.vs_call_ctx.cc_static /\ allocas_from lo mid /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp mid)` by
    (simp[update_var_def,allocas_from_def,allocas_below_fmp_def] >>
     metis_tac[allocas_from_def,allocas_below_fmp_def]) >>
  `emit_void (if tr then TSTORE else SSTORE) [dst; op] sp = ((),sf)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  `?addr. eval_operand dst mid = SOME addr` by
    metis_tac[eval_operand_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (mid,Gm,tm) []
    (Abort ExHalt_abort (halt_state (set_returndata [] mid)),Gm,tm)` by
    (gen_tac >> irule storage_emit_static_origin_ptr >> metis_tac[]) >>
  qexistsl_tac [`Abort ExHalt_abort (halt_state (set_returndata [] mid))`,`Gm`,`tm`] >>
  simp[exit_result_def,stmt_exit_def,stmt_exit_ptr_def,expr_exit_def] >>
  gen_tac >> metis_tac[gas_origin_ptr_path_append,APPEND]
QED
(* Compose singleton stores over the fixed post-load snapshot.  The seed
   identifies the caller regions independently of the final trace horizon. *)
Theorem body_assign_tuple_store_targets_full_path:
  !gs tys tvs vs ops k m b fulltys fullvs ctx func cenv cx es s st sf
     tops env es0 eseed sseed Hseed Dseed lo G tn explicit PG RetQ RetP.
    compile_tuple_store_all cenv tys gs ops st = ((),sf) /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
      tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH gs ==>
      ?x. EL i ops = Var x /\ not_fresh_at st x /\ op_taint tn (Var x) = {} /\
          (if is_word_type (EL i tys) then
             lookup_var x s = SOME (typed_val_to_w256 (EL i tvs) (EL i vs))
           else m /\
             lookup_var x s = SOME (n2w (b + SUM (MAP type_memory_size (TAKE (k+i) fulltys)))) /\
             ptr_covers G tn x s (type_memory_size (EL i tvs)))) /\
    (m ==> DROP k fulltys = tvs /\ DROP k fullvs = vs /\
           LENGTH fulltys = LENGTH fullvs /\ k <= LENGTH fulltys /\
           b + type_memory_size (TupleTV fulltys) < dimword (:256) /\
           b + type_memory_size (TupleTV fulltys) <= s.vs_alloca_next /\
           val_wf (TupleTV fulltys) (ArrayV (TupleV fullvs)) /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                  val_in_memory (TupleTV fulltys) (ArrayV (TupleV fullvs)) b mem) /\
           (!i id a cap. i < LENGTH gs /\ EL i gs = BaseTarget (NameTarget id) /\
              local_region cenv es.scopes s id a cap ==>
              b + type_memory_size (TupleTV fulltys) <= a \/
              a + type_memory_size (EL i tvs) <= b)) /\
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
    stmt_state_rel Hseed ctx func cenv cx eseed sseed /\ dead_lo_ok Hseed Dseed lo cenv cx /\
    (!name a len. local_region cenv es.scopes s name a len <=>
                   local_region cenv eseed.scopes sseed name a len) /\
    (!name. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes name es.scopes) =
            OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes name eseed.scopes)) /\
    (!x. not_fresh_at st x /\ (?id cap. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) cap)) ==>
         lookup_var x s = lookup_var x sseed) /\
    (!id entry x cap. lookup_scopes id es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) cap) ==> ptr_covers G tn x s cap) /\
    local_ptrs_reserved cenv st /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
                                sz = type_memory_size tv) fields) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    s.vs_alloca_next = sseed.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s.vs_call_ctx.cc_static = cx.txn.is_static /\
    fn_has_code st sf func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?res es' r Gf tf.
      (!tail. assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
              (res,es' with gas_obs := tail)) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tf)) /\
      ((res = INL () /\ ?t. r = OK t /\
          (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated sf) /\
          ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
          t.vs_inst_idx = LENGTH sf.cs_current_insts /\
          t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
          (!x. not_fresh_at st x ==>
            lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
            op_taint tf (Var x) = op_taint tn (Var x)) /\
          (!name a len. local_region cenv es'.scopes t name a len <=>
                         local_region cenv es.scopes s name a len) /\
          (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
            (!name a len. local_region cenv es.scopes s name a len ==>
              off + sz <= a \/ a + len <= off) ==>
            mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory /\
            (!i. off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn.t_mem)) /\
          (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
            storage_well_formed_on cx es (FST H) ==> storage_well_formed_on cx es' (FST H)) /\
          (!st0 H D d. valid_horizon cx st0 H es'.storage_trace /\
            dead_lo_ok H D lo cenv cx /\ stmt_state_rel H ctx func cenv cx es s /\
            ghost_inv_at D lo d cenv cx es G tn s ==>
            stmt_state_rel H ctx func cenv cx es' t /\ ghost_inv_at D lo d cenv cx es' Gf tf t)) \/
       (res = INR (Error (RuntimeError "write in static context")) /\ exit_result r /\
        (!H tail. stmt_exit (RetQ H) (es' with gas_obs := tail) res r) /\
        (!H tail. stmt_exit_ptr (RetP H) (es' with gas_obs := tail) res (Gf,tf) r)))
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def,comp_return_def] >>
      qexistsl [`INL ()`,`es`,`OK s`,`G`,`tn`] >>
      simp[Once evaluate_def,return_def,cj 1 gas_origin_ptr_path_rules]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) (h::gs) (op::ops1) st = _` >>
  rename1 `values_have_types (tv::tvs1) (v::vs1)` >>
  last_x_assum (mk_asm "ih") >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv v /\ val_wf tv v` by
    fs[vyperTypingTheory.value_has_type_def,valueEncodingDefsTheory.val_wf_def] >>
  drule_all tupleTargetStoreAbortTheory.tuple_target_source_outcome >>
  disch_then (qx_choosel_then [`hr`,`he`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tupleAssignPartsTheory.tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tupleAssignPartsTheory.tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm sf func` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> ?x. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss() -* ["Unwind"]) [] >>
  strip_tac >>
  reverse (Cases_on `hr = INL ()`)
  >- (qpat_x_assum `hr = INL () \/ _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
      `is_word_type ty` by
        (irule tuple_target_aligned_nonlocal_word >> qexistsl [`cenv`,`cx`,`BaseTarget bt`,`tv`] >> simp[]) >>
      `eval_operand op s = SOME (typed_val_to_w256 tv v) /\
       op_taint tn op = {} /\ (!y. op = Var y ==> not_fresh_at st y)` by
        fs[venomStateTheory.eval_operand_def] >>
      qpat_x_assum `hr = INR _` SUBST_ALL_TAC >>
      `!tail. assign_tuple_target_list cx (BaseTarget bt::gs) (v::vs1) (es with gas_obs := tail) =
              (INR (Error (RuntimeError "write in static context")),he with gas_obs := tail)` by
        (gen_tac >> simp[Once assign_tuple_target_list_cons] >>
         qexistsl [`INR (Error (RuntimeError "write in static context"))`,`he with gas_obs := tail`] >> simp[]) >>
      qexistsl [`INR (Error (RuntimeError "write in static context"))`,`he`] >> simp[] >>
      irule body_assign_tuple_static_head_full_exit >> simp[] >>
      qexistsl [`cenv`,`cx`,`BaseTarget bt`,`op`,`sm`,`st`,`tv`,`ty`,`v`] >> simp[]) >>
  qpat_x_assum `hr = INL ()` SUBST_ALL_TAC >>
  `es with gas_obs := es.gas_obs = es` by (Cases_on `es` >> simp[]) >>
  qabbrev_tac `em = he with gas_obs := es.gas_obs` >>
  `assign_tuple_targets cx (BaseTarget bt) v es = (INL (),em)` by
    (simp[NoAsms, Abbr `em`] >>
     qpat_assum `!tail. assign_tuple_targets _ _ _ _ = _`
       (qspec_then `es.gas_obs` mp_tac) >>
     qpat_assum `es with gas_obs := es.gas_obs = es`
       (fn th => rewrite_tac[th])) >>
  `!tail. assign_tuple_targets cx (BaseTarget bt) v (es with gas_obs := tail) =
          (INL (),em with gas_obs := tail)` by simp[Abbr `em`] >>
  qpat_x_assum `!name. OPTION_MAP _ (lookup_scopes name es.scopes) = _`
    (mk_asm "seed_layout") >>
  drule_all tuple_target_assignment_scope_frame >> strip_tac >>
  `~block_is_terminated sm` by (irule tuple_store_singleton_open >> qexistsl [`cenv`,`BaseTarget bt`,`op`,`st`,`ty`] >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `st` >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists `st` >> simp[]) >>
  `!name p cap. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) cap) ==>
     not_fresh_at st p` by
    (rpt strip_tac >>
     qpat_assum `local_ptrs_reserved cenv st`
       (mp_tac o cj 2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
     disch_then (qspecl_then [`name`,`name`,`p`,`cap`,`cap`] mp_tac) >> simp[]) >>
  `?smach Gm tm.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK smach,Gm,tm)) /\
     ~smach.vs_halted /\ smach.vs_current_bb = sm.cs_current_bb /\
     smach.vs_inst_idx = LENGTH sm.cs_current_insts /\
     smach.vs_allocas = s.vs_allocas /\ smach.vs_alloca_next = s.vs_alloca_next /\
     allocas_from lo smach /\ (ctx_has_dalloca ctx ==> allocas_below_fmp smach) /\
     smach.vs_call_ctx.cc_static = cx.txn.is_static /\
     (!x. not_fresh_at st x ==>
       lookup_var x smach = lookup_var x s /\ FLOOKUP Gm x = FLOOKUP G x /\
       op_taint tm (Var x) = op_taint tn (Var x)) /\
     (!x cap. not_fresh_at st x /\ ptr_covers G tn x s cap ==> ptr_covers Gm tm x smach cap) /\
     (!name a len. local_region cenv em.scopes smach name a len <=>
                   local_region cenv es.scopes s name a len) /\
     (m ==> !mem. mem_agree_outside tm.t_mem smach.vs_memory mem ==>
           val_in_memory (TupleTV fulltys) (ArrayV (TupleV fullvs)) b mem) /\
     (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       (!name a len. local_region cenv es.scopes s name a len ==>
         off + sz <= a \/ a + len <= off) ==>
       mem_bytes_at off sz smach.vs_memory = mem_bytes_at off sz s.vs_memory /\
       (!i. off <= i /\ i < off + sz /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
     (!st0 H. valid_horizon cx st0 H em.storage_trace /\
       storage_well_formed_on cx es (FST H) ==> storage_well_formed_on cx em (FST H)) /\
     (!st0 H D d. valid_horizon cx st0 H em.storage_trace /\
       dead_lo_ok H D lo cenv cx /\ stmt_state_rel H ctx func cenv cx es s /\
       ghost_inv_at D lo d cenv cx es G tn s ==>
       stmt_state_rel H ctx func cenv cx em smach /\ ghost_inv_at D lo d cenv cx em Gm tm smach)` by
    suspend "head" >>
  suspend "tail"
QED

Resume body_assign_tuple_store_targets_full_path[head]:
  reverse (Cases_on `?id. bt = NameTarget id`)
  >- suspend "nonlocal" >>
  qpat_x_assum `?id. bt = NameTarget id` (qx_choose_then `id` SUBST_ALL_TAC) >>
  fs[tuple_target_aligned_local,tuple_target_layout_local] >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap)` >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  drule_all tuple_target_local_assignment >>
  disch_then (qx_choosel_then [`pre`,`sc`,`rest`] strip_assume_tac) >>
  `?entry0. lookup_scopes id eseed.scopes = SOME entry0 /\ entry0.type = entry.type` by
    (asm "seed_layout" (qspec_then `id` mp_tac) >>
     Cases_on `lookup_scopes id eseed.scopes` >> simp[]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `?dw. lookup_var p sseed = SOME dw /\
        w2n dw + cap <= sseed.vs_alloca_next /\ type_memory_size entry.type <= cap` by
    (qpat_assum `local_ptrs_rel _ _ _ _` (mp_tac o cj 1 o REWRITE_RULE [local_ptrs_rel_def]) >>
     disch_then (qspecl_then [`id`,`entry0`,`p`,`cap`] mp_tac) >> simp[] >>
     disch_then (qx_choose_then `w` strip_assume_tac) >> qexists `w` >> simp[]) >>
  `not_fresh_at st p` by
    (qpat_assum `!name p cap. FLOOKUP cenv.ce_vars name = _ ==> _`
       (qspecl_then [`id`,`p`,`cap`] mp_tac) >> simp[]) >>
  `lookup_var p s = SOME dw` by
    (qpat_assum `!x. not_fresh_at st x /\ (?id cap. _) ==> _`
       (qspec_then `p` mp_tac) >> impl_tac >- (simp[] >> qexistsl [`id`,`cap`] >> simp[]) >> simp[]) >>
  `local_region cenv eseed.scopes sseed id (w2n dw) cap` by
    (simp[local_region_def] >> qexistsl [`p`,`dw`,`entry0`] >> simp[]) >>
  `0 < cap` by gvs[] >>
  `lo <= w2n dw` by
    (irule body_full_local_region_lower_bound >>
     qexistsl [`Dseed`,`Hseed`,`cenv`,`ctx`,`cx`,`env`,`eseed`,`es0`,`func`,`id`,`cap`,`sseed`,`tops`] >> simp[]) >>
  `sseed.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >>
     simp[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `w2n dw + type_memory_size entry.type < dimword (:256) /\
   w2n dw + type_memory_size entry.type <= s.vs_alloca_next` by decide_tac >>
  `local_region cenv es.scopes s id (w2n dw) cap` by simp[] >>
  `ptr_covers G tn p s (type_memory_size entry.type)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists `cap` >>
     simp[] >>
     qpat_assum `!id entry x cap. lookup_scopes id es.scopes = SOME entry /\ _ ==> _`
       (qspecl_then [`id`,`entry`,`p`,`cap`] mp_tac) >> simp[]) >>
  `tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty entry.type /\
   tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty entry.type v` by
    simp[tuple_target_aligned_local,tuple_target_layout_local] >>
  `m ==> b + type_memory_size (TupleTV fulltys) <= w2n dw \/
         w2n dw + type_memory_size entry.type <= b` by
    (disch_tac >> qpat_assum `m ==> DROP k fulltys = _ /\ _`
       (mp_tac o List.last o CONJUNCTS o UNDISCH) >>
     disch_then (qspecl_then [`0`,`id`,`w2n dw`,`cap`] mp_tac) >> simp[]) >>
  qabbrev_tac `snapbase = if m then b else w2n dw` >>
  qabbrev_tac `snaptys = if m then fulltys else []` >>
  qabbrev_tac `snapvs = if m then fullvs else []` >>
  Q.SUBGOAL_THEN `val_wf (TupleTV snaptys) (ArrayV (TupleV snapvs)) /\
   (snapbase + type_memory_size (TupleTV snaptys) <= w2n dw \/
    w2n dw + type_memory_size entry.type <= snapbase) /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory (TupleTV snaptys) (ArrayV (TupleV snapvs)) snapbase mem)`
    (map_every assume_tac o CONJUNCTS) >-
    (Cases_on `m` >-
       (qpat_assum `m ==> DROP k fulltys = _ /\ _`
          (map_every assume_tac o CONJUNCTS o UNDISCH) >>
        qpat_assum `T ==> b + type_memory_size (TupleTV fulltys) <= w2n dw \/ _`
          (mp_tac o UNDISCH) >>
        simp[Abbr `snapbase`, Abbr `snaptys`, Abbr `snapvs`]) >>
     simp[Abbr `snapbase`, Abbr `snaptys`, Abbr `snapvs`,
          valueEncodingDefsTheory.val_wf_def,valueEncodingDefsTheory.val_in_memory_def,
          valueEncodingTheory.type_memory_size_def]) >>
  `(if is_word_type ty then
      eval_operand op s = SOME (typed_val_to_w256 entry.type v) /\ op_taint tn op = {}
    else ?xs sw. op = Var xs /\ not_fresh_at st xs /\ lookup_var xs s = SOME sw /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory entry.type v (w2n sw) mem) /\
      ptr_covers G tn xs s (type_memory_size entry.type) /\
      w2n sw + type_memory_size entry.type < dimword (:256) /\
      w2n sw + type_memory_size entry.type <= s.vs_alloca_next /\
      (w2n sw + type_memory_size entry.type <= w2n dw \/
       w2n dw + type_memory_size entry.type <= w2n sw))` by
    (Cases_on `is_word_type ty` >- fs[venomStateTheory.eval_operand_def] >>
     suspend "snapshot_member") >>
  drule (INST_TYPE [``:'a`` |-> ``:256``] body_assign_tuple_local_head_full_path) >>
  disch_then (drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`snapvs`,`snaptys`,`explicit`,`ctx`,`snapbase`,`PG`] mp_tac) >>
  (impl_tac >-
    (simp[] >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _` mp_tac >>
     gvs[])) >>
  disch_then (qx_choosel_then [`smach`,`Gm`,`tm`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "local_join"
QED

Resume body_assign_tuple_store_targets_full_path[snapshot_member]:
  qpat_assum `~is_word_type ty` (fn mode =>
    qpat_assum `if is_word_type ty then lookup_var x s = _ else _`
      (strip_assume_tac o SRULE [mode])) >>
  qpat_assum `m ==> DROP k fulltys = _ /\ _`
    (strip_assume_tac o UNDISCH) >>
  `k < LENGTH fulltys` by
    (qpat_assum `DROP k fulltys = _::_`
       (mp_tac o AP_TERM ``LENGTH : type_value list -> num``) >> simp[]) >>
  `EL k fulltys = entry.type /\ EL k fullvs = v` by
    (conj_tac >-
       (qpat_assum `DROP k fulltys = _::_`
          (mp_tac o AP_TERM ``EL 0 : type_value list -> type_value``) >>
        simp[listTheory.EL_DROP]) >>
     `k < LENGTH fullvs` by decide_tac >>
     qpat_assum `DROP k fullvs = _::_`
       (mp_tac o AP_TERM ``EL 0 : value list -> value``) >>
     simp[listTheory.EL_DROP]) >>
  `type_memory_size_list (TAKE k fulltys) + type_memory_size entry.type <=
    type_memory_size (TupleTV fulltys)` by
    (qspecl_then [`fulltys`,`k`,`LENGTH fulltys`] mp_tac
       placeMemoryIndexRebuildTheory.tuple_memory_cells_ordered >>
     pure_rewrite_tac[listTheory.TAKE_LENGTH_ID] >>
     simp[valueEncodingTheory.type_memory_size_def]) >>
  qabbrev_tac `addr = b + SUM (MAP type_memory_size (TAKE k fulltys))` >>
  `b <= addr /\ addr + type_memory_size entry.type <= b + type_memory_size (TupleTV fulltys)` by
    (qpat_assum `type_memory_size_list (TAKE k fulltys) + _ <= _` mp_tac >>
     pure_rewrite_tac[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     gvs[Abbr `addr`]) >>
  `addr + type_memory_size entry.type < dimword (:256) /\
   addr + type_memory_size entry.type <= s.vs_alloca_next /\ addr < dimword (:256)` by decide_tac >>
  qpat_assum `~is_word_type ty` (fn th => rewrite_tac[th]) >>
  qexistsl [`x`,`n2w addr`] >> simp[wordsTheory.w2n_n2w_compute] >>
  conj_tac >-
    (qspecl_then [`fullvs`,`fulltys`,`b`,`s.vs_memory`,`tn`,`k`] mp_tac
       typedCopyLayoutPtrTheory.tuple_in_memory_robust_element >>
     (impl_tac >-
       (simp[] >> qpat_assum `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory (TupleTV fulltys) _ _ mem`
          (mp_tac o SRULE [valueEncodingDefsTheory.val_in_memory_def]) >> simp[])) >>
     simp[Abbr `addr`]) >>
  qpat_assum `entry.type = tv` SUBST_ALL_TAC >>
  qpat_assum `s.vs_alloca_next = sseed.vs_alloca_next` SUBST_ALL_TAC >>
  qpat_assum `m ==> b + type_memory_size (TupleTV fulltys) <= w2n dw \/ _`
    (mp_tac o UNDISCH) >> decide_tac
QED

Resume body_assign_tuple_store_targets_full_path[local_join]:
  qpat_assum `typed_copy_state_frame _ _ _ s smach`
    (strip_assume_tac o SRULE [typed_copy_state_frame_def,
                             venomStateTheory.venom_state_component_equality]) >>
  `allocas_from lo smach /\ (ctx_has_dalloca ctx ==> allocas_below_fmp smach)` by
    (pure_rewrite_tac[ptrDisciplineTheory.allocas_from_def,ptrDisciplineTheory.allocas_below_fmp_def] >>
     pure_asm_rewrite_tac[] >> conj_tac >-
       (qpat_assum `allocas_from lo s`
          (ACCEPT_TAC o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def])) >>
  `!x cap. not_fresh_at st x /\ ptr_covers G tn x s cap ==> ptr_covers Gm tm x smach cap` by
    (rpt strip_tac >> irule appendStorageGhostPtrTheory.ptr_covers_old_transport >>
     qexistsl [`G`,`s`,`st`,`tn`] >> simp[]) >>
  `!R : (bool # 256 word # type_value) list.
     storage_well_formed_on cx em R <=> storage_well_formed_on cx es R` by
    (gen_tac >> irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  qexistsl [`smach`,`Gm`,`tm`] >> simp[] >>
  conj_tac >-
    ((disch_tac >>
     qpat_assum `!mem. mem_agree_outside tm.t_mem smach.vs_memory mem ==> _`
       mp_tac >> simp[Abbr `snapbase`,Abbr `snaptys`,Abbr `snapvs`] >> (gvs[]))) >>
  conj_tac >-
    (qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` mp_tac >> simp[]) >>
  qpat_assum `em = es with scopes := _` (SUBST1_TAC o SYM) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H D d. stmt_state_rel H ctx func cenv cx es s /\
                        ghost_inv_at D lo d cenv cx es G tn s ==> _`
    (drule_all_then ACCEPT_TAC)
QED

Resume body_assign_tuple_store_targets_full_path[nonlocal]:
  `!id. BaseTarget bt <> BaseTarget (NameTarget id)` by gvs[] >>
  `is_word_type ty` by
    (irule tuple_target_aligned_nonlocal_word >> qexistsl [`cenv`,`cx`,`BaseTarget bt`,`tv`] >> simp[]) >>
  `eval_operand op s = SOME (typed_val_to_w256 tv v) /\
   op_taint tn op = {} /\ (!y. op = Var y ==> not_fresh_at st y)` by
    fs[venomStateTheory.eval_operand_def] >>
  drule body_assign_tuple_nonlocal_head_full_path >>
  disch_then (drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = {}`)) >>
  disch_then (qspecl_then [`tv`,`explicit`,`ctx`,`PG`,`G`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`smach`,`Gm`,`tm`] (map_every assume_tac o CONJUNCTS))) >>
  `smach.vs_initial_fmp = s.vs_initial_fmp` by
    (`!memory sites C fn a marks r. gas_origin_path memory sites C fn a marks r ==>
         !z. r = OK z ==> z.vs_initial_fmp = a.vs_initial_fmp` suffices_by
       (strip_tac >> qpat_assum `!D. gas_origin_ptr_path _ (s,_,_) [] (OK smach,_,_)`
          (qspec_then `Dseed` (mp_tac o cj 1 o MATCH_MP gas_origin_ptr_path_projections)) >>
        disch_tac >> first_x_assum drule >> simp[]) >>
     POP_ASSUM_LIST (K all_tac) >>
     ho_match_mp_tac fragGasOriginTheory.gas_origin_path_ind >>
     simp[fragGasOriginTheory.gas_origin_edge_def,exit_result_def] >>
     rpt strip_tac >> gvs[venomStateTheory.jump_to_def] >>
     metis_tac[ctxLookupAgreeHelpersTheory.step_inst_initial_fmp,
               ctxLookupAgreeHelpersTheory.eval_phis_initial_fmp]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp smach)` by
    (pure_rewrite_tac[ptrDisciplineTheory.allocas_below_fmp_def] >>
     pure_asm_rewrite_tac[] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def])) >>
  `!name a len. local_region cenv em.scopes smach name a len <=>
                local_region cenv es.scopes s name a len` by
    (qpat_assum `em.scopes = es.scopes` (fn th => pure_rewrite_tac[th]) >>
     rpt gen_tac >> match_mp_tac local_region_lookup_cong >> rpt strip_tac >>
     `not_fresh_at st p` by (qpat_assum `!name p cap. FLOOKUP _ name = _ ==> _` drule >> simp[]) >> simp[]) >>
  `allocas_from lo smach` by
    (qpat_assum `smach.vs_allocas = s.vs_allocas` (fn th =>
       rewrite_tac[ptrDisciplineTheory.allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  qexistsl [`smach`,`Gm`,`tm`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_assum `!st0 H. valid_horizon cx st0 H em.storage_trace /\ stmt_state_rel _ _ _ _ _ _ _ ==> _`
        (qspecl_then [`st0`,`H`] mp_tac) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  qpat_assum `!st0 H D d. valid_horizon cx st0 H em.storage_trace /\ _ ==> _`
    (qspecl_then [`st0`,`H`,`D`,`d`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Resume body_assign_tuple_store_targets_full_path[tail]:
  `!g ty tv v. tuple_target_layout em.scopes g ty tv v <=>
               tuple_target_layout es.scopes g ty tv v` by
    (rpt gen_tac >> irule tuple_target_layout_transport >> first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
    (mk_asm "head_protected") >>
  asm "ih" (qspecl_then [`tys1`,`tvs1`,`vs1`,`ops1`,`SUC k`,`m`,`b`,`fulltys`,`fullvs`,
    `ctx`,`func`,`cenv`,`cx`,`em`,`smach`,`sm`,`sf`,`tops`,`env`,`es0`,`eseed`,`sseed`,
    `Hseed`,`Dseed`,`lo`,`Gm`,`tm`,`explicit`,`PG`,`RetQ`,`RetP`] mp_tac) >>
  impl_tac >-
    (asm "seed_layout" assume_tac >> simp[] >>
     `LENGTH gs = LENGTH tys1 /\ LENGTH tys1 = LENGTH tvs1 /\
      LENGTH tvs1 = LENGTH vs1 /\ LENGTH ops1 = LENGTH vs1` by fs[] >>
     `values_have_types tvs1 vs1 /\ tuple_val_wf vs1 tvs1` by
       fs[vyperTypeDefaultsTheory.values_have_types_LIST_REL,
          typedCopyOriginPtrFieldsTheory.tuple_val_wf_LIST_REL] >>
     simp[] >>
     conj_tac >-
       (qx_gen_tac `i` >> disch_tac >>
        `SUC i < LENGTH (BaseTarget bt::gs)` by simp[] >>
        qpat_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
          (qspec_then `SUC i` (fn th =>
            qpat_assum `SUC i < LENGTH (BaseTarget bt::gs)`
              (mp_tac o MATCH_MP th))) >>
        disch_then (map_every assume_tac o CONJUNCTS o
          REWRITE_RULE [listTheory.EL_restricted]) >> simp[]) >>
     conj_tac >-
       (qx_gen_tac `i` >> disch_tac >>
        `SUC i < LENGTH (BaseTarget bt::gs)` by simp[] >>
        qpat_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> ?x. _`
          (qspec_then `SUC i` (fn th =>
            qpat_assum `SUC i < LENGTH (BaseTarget bt::gs)`
              (qx_choose_then `y` (map_every assume_tac o CONJUNCTS) o
               REWRITE_RULE [listTheory.EL_restricted,arithmeticTheory.ADD_CLAUSES] o MATCH_MP th))) >>
        qexists `y` >> Cases_on `is_word_type (EL i tys1)` >> fs[arithmeticTheory.ADD_CLAUSES]) >>
     conj_tac >-
       (disch_tac >>
        qpat_assum `m ==> DROP k fulltys = _ /\ _` (mp_tac o UNDISCH) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        simp[rich_listTheory.DROP_SUC] >>
        qpat_assum `DROP k fullvs = v::vs1`
          (mp_tac o AP_TERM ``LENGTH : value list -> num``) >> simp[] >>
        disch_tac >> map_every qx_gen_tac [`i`,`id`,`a`,`cap`] >> strip_tac >>
        `local_region cenv es.scopes s id a cap` by simp[] >>
        qpat_assum `!i id a cap. i < LENGTH (BaseTarget bt::gs) /\ _ ==> _`
          (qspecl_then [`SUC i`,`id`,`a`,`cap`] mp_tac) >> simp[listTheory.EL_restricted]) >>
     conj_tac >-
       (rpt strip_tac >>
        `not_fresh_at st x'` by
          (qpat_assum `!name p cap. FLOOKUP cenv.ce_vars name = _ ==> _`
             (qspecl_then [`id`,`x'`,`cap`] mp_tac) >> simp[]) >>
        simp[] >> qpat_assum `!x. not_fresh_at st x /\ (?id cap. _) ==> _`
          (qspec_then `x'` mp_tac) >>
        impl_tac >- (simp[] >> qexistsl [`id`,`cap`] >> simp[]) >> simp[]) >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_assum `!x cap. not_fresh_at st x /\ ptr_covers G tn x s cap ==> _`
          (qspecl_then [`x'`,`cap`] mp_tac) >>
        impl_tac >- (
          conj_tac >- (qpat_assum `!name p cap. FLOOKUP cenv.ce_vars name = _ ==> _`
                         (qspecl_then [`id`,`x'`,`cap`] mp_tac) >> simp[]) >>
          `?old. lookup_scopes id es.scopes = SOME old` by
            (Cases_on `lookup_scopes id es.scopes` >-
               (drule_all vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom >> simp[]) >>
             simp[]) >>
          qpat_assum `!id entry x cap. lookup_scopes id es.scopes = SOME entry /\ _ ==> _`
            (qspecl_then [`id`,`old`,`x'`,`cap`] mp_tac) >> simp[]) >> simp[]) >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
       mp_tac >> simp[]) >>
  disch_then (qx_choosel_then [`res`,`ef`,`r`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`res`,`ef`,`r`,`Gf`,`tf`] >>
  conj_tac >-
    (gen_tac >> simp[Once assign_tuple_target_list_cons] >>
     qexistsl [`INL ()`,`em with gas_obs := tail`] >> simp[]) >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`Gm`,`smach`,`tm`] >> simp[]) >>
  qpat_x_assum `(res = INL () /\ _) \/ _` (DISJ_CASES_THEN STRIP_ASSUME_TAC) >>
  simp[] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!aid off sz. FLOOKUP smach.vs_allocas aid = _ /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >>
     (impl_tac >- (first_assum ACCEPT_TAC)) >> strip_tac >>
     asm "head_protected" (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >>
     (impl_tac >- (first_assum ACCEPT_TAC)) >> strip_tac >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `?obs. ef.storage_trace = em.storage_trace ++ obs` by
    (`storage_trace_frame (assign_tuple_target_list cx gs vs1)` by
       simp[cj 10 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     qpat_assum `!tail. assign_tuple_target_list cx gs vs1 _ = _`
       (qspec_then `em.gas_obs` assume_tac) >>
     drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[]) >>
  `!st0 H. valid_horizon cx st0 H ef.storage_trace ==>
           valid_horizon cx st0 H em.storage_trace` by
    (rpt strip_tac >> irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists `obs` >>
     qpat_assum `ef.storage_trace = em.storage_trace ++ obs`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (rpt strip_tac >>
     `valid_horizon cx st0 H em.storage_trace` by
       (qpat_assum `!st0 H. valid_horizon cx st0 H ef.storage_trace ==> _`
          (qspecl_then [`st0`,`H`] mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
        disch_then ACCEPT_TAC) >>
     `storage_well_formed_on cx em (FST H)` by
       (qpat_assum `!st0 H. valid_horizon cx st0 H em.storage_trace /\ storage_well_formed_on _ _ _ ==> _`
          (qspecl_then [`st0`,`H`] mp_tac) >>
        impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
     qpat_assum `!st0 H. valid_horizon cx st0 H ef.storage_trace /\ _ ==> _`
       (qspecl_then [`st0`,`H`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H em.storage_trace` by
    (qpat_assum `!st0 H. valid_horizon cx st0 H ef.storage_trace ==> _`
       (qspecl_then [`st0`,`H`] mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
     disch_then ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx em smach /\
   ghost_inv_at D lo d cenv cx em Gm tm smach` by
    (qpat_assum `!st0 H D d. valid_horizon cx st0 H em.storage_trace /\ _ ==> _`
       (qspecl_then [`st0`,`H`,`D`,`d`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  qpat_assum `!st0 H D d. valid_horizon cx st0 H ef.storage_trace /\ _ ==> _`
    (qspecl_then [`st0`,`H`,`D`,`d`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Finalise body_assign_tuple_store_targets_full_path


Theorem body_assign_tuple_widened_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    lowered_value_type cenv e <> expr_type e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* Every target a local, a scalar top-level variable or a storage word field. *)
Theorem body_assign_tuple_targets_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule tuple_targets_typing >> disch_then (qx_choose_then `tys` strip_assume_tac) >>
  drule_then assume_tac bodySimStmtFactsTheory.body_inv_mcopy >>
  drule_then assume_tac bodyExprPreFactsTheory.supported_stmt_body_safe >>
  `~supported_stmt_expr_exists (const_name_root cx)
      (Assign (TupleTarget gs) e)` by
    (drule (cj 1 supportedNameRootTheory.supported_stmts_no_name_root) >>
     disch_then irule >> drule_then ACCEPT_TAC body_inv_const_name_root) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    fs[body_inv_def] >>
  drule_then assume_tac gasContextTheory.cx_tops_module >>
  `expr_body_pre cenv cx env e es` by
    (irule bodyExprPreFactsTheory.stmt_expr_body_pre >>
     fs[bodyExprPreFactsTheory.stmt_exprs_ok_flat,
        supportedStmtTraverseTheory.body_stmt_safe_def,
        supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
        vyperTypeCallGraphTheory.int_calls_stmt_def, EVERY_APPEND, EVERY_CONJ,
        DE_MORGAN_THM, GSYM supportedExprTraverseTheory.expr_has_evm_run_def] >>
     conj_tac >- (fs[allocLimitsTheory.alloc_limits_stmt_def] >>
                  drule_then ACCEPT_TAC allocLimitsPropsTheory.alloc_limits_expr_not_extcode) >>
     qexists_tac `[]` >> simp[] >>
     drule_then ACCEPT_TAC vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (TupleT tys) e es` by
    (qpat_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o PURE_ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy)` by simp[] >>
  drule_all tupleAssignPartsTheory.assign_tuple_targets_code_parts >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`vv`,`sc`,`op`,`su`,`staged`,`sl`,`elems`,`ss`]
      (map_every assume_tac o CONJUNCTS))) >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def,comp_bind_def] >>
  `?shadow_su. lower_value compile_expr cenv (TupleT tys) (gas_shadow_expr e)
      shadow_sa = (op,shadow_su) /\ gas_shadow_state su shadow_su` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `TupleT tys`, `e` |-> `e`]
       gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (TupleT tys) (gas_shadow_expr e) shadow_sa` >>
     simp[]) >>
  `fn_has_code shadow_sa shadow_su shadow_func` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_stmt_def,gas_shadow_assignment_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (Assign _ e) sa = _` kall_tac >>
     `expr_type (gas_shadow_expr e) = TupleT tys /\
       lowered_value_type cenv (gas_shadow_expr e) = expr_type (gas_shadow_expr e)` by
       simp[gasShadowCompilePureTheory.gas_shadow_lowered_value_type] >>
     drule_all tupleAssignPartsTheory.assign_tuple_targets_code_parts >>
     disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
       (qx_choosel_then [`svv`,`shadow_sc`,`sop`,`su2`,`sstaged`,`shadow_sl`,`selems`,`shadow_ss`]
         (map_every assume_tac o CONJUNCTS))) >>
     `op = sop /\ shadow_su = su2` by
       gvs[lower_value_def,comp_bind_def] >>
     `cs_extends shadow_sa su2` by metis_tac[cs_extends_trans] >>
     `cs_extends su2 shadow_sb` by metis_tac[cs_extends_trans] >>
     irule (cj 1 fn_has_code_split) >> conj_tac >- gvs[] >>
     qexists_tac `shadow_sb` >> gvs[]) >>
  `cs_extends sa su /\ cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  drule_then assume_tac exprSimSourceTheory.expr_body_pre_gas_admissible >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`su`,`shadow_sa`,`shadow_su`,`op`,
    `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        mp_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  disch_tac >>
  rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >~ [`storage_trace_frame (assign_tuple_targets _ _ _)`]
  >- simp[cj 9 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rhsQ _` >>
  qexists_tac `\H res ee G tn t. rhsQ H res ee G tn t /\
                 ~t.vs_halted /\ ee.gas_obs = []` >> reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      rpt gen_tac >> POP_ASSUM_LIST (K all_tac) >> strip_tac >>
      Cases_on `res` >> fs[expr_exit_def] >> rename1 `expr_exit (INR exc) r` >>
      simp[stmt_exit_ptr_def, GSYM (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        stmtSimPropsTheory.expr_exit_INR_type)] >>
      `!ir s. r <> IntRet ir s` by
        (rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `exc` >> gvs[expr_exit_def] >>
         rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
      simp[] >>
      irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        haltExitProjTheory.halt_exit_INR_type)) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  fs[Abbr `rhsQ`] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2
      (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (map_every assume_tac o CONJUNCTS)))
      assume_tac)
    (map_every assume_tac o CONJUNCTS)) >>
  simp[] >>
  `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs) =
       (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `mid.gas_obs` mp_tac) >>
     simp[NoAsms, evaluation_state_component_equality]) >>
  `?tv er. eval_expr cx e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs) =
       (INL tv,er) /\ read_result cx tv er = (INL v,mid)` by
    (qpat_assum `bind _ _ _ = (INL v,mid)`
       (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split) >>
     simp[]) >>
  `body_tuple_target_full_ok cx (TupleTarget gs) v` by
    (qpat_assum `!s tv t s' v t'. _ ==> body_tuple_target_full_ok _ _ _`
       (qspecl_then [`es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs`,
                     `tv`,`er`,`er`,`v`,`mid`] mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
    bodySimStmtFactsTheory.expr_body_pre_eval) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `v` assume_tac)) >>
  `env.type_defs = get_tenv cx` by
    (irule exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >>
     qexists_tac `cenv` >> qexists_tac `es` >> simp[]) >>
  qpat_x_assum `INL v = INL v ==> value_runtime_typed _ _ v` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  disch_then (qx_choose_then `rtv` (map_every assume_tac o CONJUNCTS)) >>
  drule_all stmtSimReturnTheory.tuple_type_value >>
  disch_then (qx_choosel_then [`tvs`,`vs`]
    (CONJUNCTS_THEN2 SUBST_ALL_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC
       (map_every assume_tac o CONJUNCTS)))) >>
  `LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
   LENGTH tvs = LENGTH vs` by
    (fs[vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
     metis_tac[LIST_REL_LENGTH]) >>
  qpat_assum `expr_post _ ctx func cenv cx e es sa su s0 mid _ op t`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_vars_rels >>
  `!i. i < LENGTH gs ==>
     tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
     (~is_word_type (EL i tys) ==> type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
     tuple_target_layout mid.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)` by
    (gen_tac >> disch_tac >>
     `well_typed_atarget env (EL i gs) (EL i tys) /\
      evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
      value_has_type (EL i tvs) (EL i vs)` by
       fs[LIST_REL_EL_EQN, vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
     qpat_assum `EVERY _ gs`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_EL]) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (assume_tac o BETA_RULE) >>
     drule_all (Q.INST [`es` |-> `mid`]
       bodySimStmtFactsTheory.body_tuple_target_ready) >>
     simp[]) >>
  `!i. i < LENGTH tys ==>
      evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
      type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
      0 < type_memory_size (EL i tvs)` by
    (gen_tac >> disch_tac >> irule stmtSimAssignTupleTargetsTheory.tuple_target_aligned_sizes >>
     qexists_tac `EL i gs` >> simp[]) >>
  `LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs` by
    simp[LIST_REL_EL_EQN] >>
  `SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs` by
    (drule tuple_prefix_sizes >> disch_then (qspec_then `LENGTH tys` mp_tac) >>
     simp[listTheory.TAKE_LENGTH_ID_rwt,valueEncodingProofsTheory.type_memory_size_list_sum]) >>
  `post_value_type cenv e = TupleT tys` by simp[post_value_type_lowered] >>
  `local_ptrs_reserved cenv su` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    (irule tupleStagePropsTheory.type_memory_bytes_tuple_list >> first_assum ACCEPT_TAC) >>
  `?sw. eval_operand op t = SOME sw` by
    (qpat_assum `expr_val_rel _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >> (simp[])) >>
  Cases_on `gs = []`
  >- (`tys = [] /\ tvs = [] /\ vs = []` by
        (qpat_assum `LENGTH tys = LENGTH tvs` mp_tac >>
         qpat_assum `LENGTH gs = LENGTH tys` mp_tac >>
         qpat_assum `LENGTH tvs = LENGTH vs` mp_tac >>
         simp[] >> metis_tac[LENGTH_NIL]) >>
      gvs[compile_tuple_load_all_def, compile_tuple_store_all_def, comp_return_def] >>
      `expr_body_pre cenv cx env e
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
        simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      `~block_is_terminated sc` by
        (drule_all exprOpenMainTheory.compile_expr_open_general >> simp[]) >>
      `~block_is_terminated sb` by
        (drule_all exprOpenTerminalsTheory.unwrap_value_open >> simp[]) >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
      conj_tac >- (
        qexistsl_tac [`G1`,`mid`,`INL ()`,`t`,`tn1`] >>
        conj_tac >- simp[NoAsms, cj 57 vyperInterpreterTheory.evaluate_def,
                         cj 58 vyperInterpreterTheory.evaluate_def, return_def] >>
        gen_tac >> disch_tac >> BETA_TAC >>
        conj_tac >- simp[cj 1 gas_origin_ptr_path_rules] >>
        `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
        `valid_horizon cx st0 H es.storage_trace` by
          (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
             (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
              simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
                   vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
           `valid_horizon cx st0 H
              (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace` suffices_by simp[] >>
           irule (INST_TYPE [alpha |-> ``:value``]
             vyperStorageFootprintTheory.valid_horizon_frame) >>
           qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`,
             `INL (ArrayV (TupleV []))`,`mid`] >>
           simp[vyperStateTheory.bind_def]) >>
        qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        `MAP FDOM mid.scopes = MAP FDOM es.scopes` by fs[locals_kept_def] >>
        `alloca_frame cenv es sa s0 cenv mid t` by
          (drule_all stmtSimDefsTheory.expr_post_alloca_frame >> simp[]) >>
        `return_buf_frame d cenv sb t` by
          (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
           qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
        fs[expr_post_def,ghost_kept_at_def] >>
        `return_buf_sep d cenv mid t` by
          (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
           conj_tac >- fs[] >>
           qexistsl_tac [`H`, `ctx`, `cx`, `es`, `func`, `s0`, `sa`] >>
           rpt conj_tac >> first_assum ACCEPT_TAC) >>
        gvs[stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl,
            return_buf_sep_gas_obs] >>
        first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     `valid_horizon cx st0 H
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``]
       vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`,
       `INL (ArrayV (TupleV vs))`,`mid`] >> gvs[vyperStateTheory.bind_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by fs[locals_kept_def] >>
  `alloca_frame cenv es sa s0 cenv mid t` by
    (drule_all stmtSimDefsTheory.expr_post_alloca_frame >> simp[]) >>
  qpat_x_assum `(if _ then _ else comp_return op) su = (staged,sl)`
    (assume_tac o REWRITE_RULE [tupleStagePropsTheory.optional_tuple_stage_code]) >>
  `tys <> []` by (strip_tac >> fs[]) >>
  `0 < type_memory_size_list tvs` by
    (irule tupleStagePropsTheory.tuple_memory_size_positive >>
     qexists_tac `get_tenv cx` >> qexists_tac `tys` >> simp[] >>
     qx_gen_tac `i` >> disch_tac >> disj2_tac >>
     qexistsl_tac [`EL i tys`,`EL i tvs`] >> simp[]) >>
  `op_taint tn1 op = {} /\
   (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n sw) mem)` by
    (qpat_assum `ptr_val_ok _ _ _ op G1 tn1 t`
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (K ALL_TAC) mp_tac) o
        PURE_REWRITE_RULE [ptr_val_ok_def]) >>
     simp[] >>
     disch_then (qspecl_then [`TupleTV tvs`,`sw`] mp_tac o
       PURE_REWRITE_RULE [ptr_mem_ok_def]) >> simp[]) >>
  `ptr_buf_ok cenv e op G1 t` by simp[] >>
  `?xs. op = Var xs /\ ptr_covers G1 tn1 xs t (type_memory_size_list tvs)` by
    (drule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     disch_then (qspecl_then [`tn1`,`sw`,`type_memory_size_list tvs`] mp_tac) >> simp[]) >>
  `w2n sw + type_memory_size_list tvs <= t.vs_alloca_next` by
    (qpat_assum `expr_store_bound _ _ _ op t`
       (qspecl_then [`TupleTV tvs`,`sw`] mp_tac o
        PURE_REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
     simp[exprSimPropsTheory.val_store_size_def,valueEncodingTheory.type_memory_size_def]) >>
  `expr_val_rel cx (TupleT tys) (ArrayV (TupleV vs)) op t /\
   expr_val_at cenv cx (TupleT tys) sa su mid (ArrayV (TupleV vs)) op t` by
    metis_tac[] >>
  drule_all tupleStagePropsTheory.expr_tuple_memory_owned >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`rhs_base`,`rhs_cap`] (map_every assume_tac o CONJUNCTS)))) >>
  `w2n sw + type_memory_size_list tvs < dimword (:256)` by
    (`rhs_base + rhs_cap < dimword (:256)` by
       (drule_all tupleTypedLoadTheory.tuple_container_bound >> simp[]) >>
     decide_tac) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid G1 tn1 t`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `lookup_var xs t = SOME sw /\ not_fresh_at su xs` by
    (conj_tac
     >- (qpat_assum `eval_operand op t = SOME sw` mp_tac >>
         simp[] >> gvs[GSYM venomStateTheory.eval_operand_def]) >>
     qpat_assum `!x. op = Var x ==> not_fresh_at su x`
       (qspec_then `xs` mp_tac) >> simp[]) >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
   type_memory_size (TupleTV tvs) = type_memory_size_list tvs` by
    simp[valueEncodingDefsTheory.val_wf_def,valueEncodingTheory.type_memory_size_def] >>
  qmatch_asmsub_abbrev_tac `if stage_guard then _ else comp_return op` >>
  `?u root w Gu nu.
     staged = Var root /\ not_fresh_at sl root /\ lookup_var root u = SOME w /\
     ptr_covers Gu nu root u (type_memory_size_list tvs) /\
     w2n w + type_memory_size_list tvs < dimword (:256) /\
     w2n w + type_memory_size_list tvs <= u.vs_alloca_next /\
     (!mem. mem_agree_outside nu.t_mem u.vs_memory mem ==>
            val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) mem) /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (t,G1,tn1) [] (OK u,Gu,nu)) /\
     (!(H : (bool # 256 word # type_value) list # num list).
        stmt_state_rel H ctx func cenv cx mid t ==> stmt_state_rel H ctx func cenv cx mid u) /\
     (!D. ghost_inv_at D lo d cenv cx mid G1 tn1 t ==> ghost_inv_at D lo d cenv cx mid Gu nu u) /\
     ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
     u.vs_inst_idx = LENGTH sl.cs_current_insts /\
     allocas_from lo u /\ lo <= u.vs_alloca_next /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     (!aid ent. FLOOKUP t.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
     (!x. not_fresh_at su x ==> not_fresh_at sl x /\ lookup_var x u = lookup_var x t /\
          FLOOKUP Gu x = FLOOKUP G1 x /\ op_taint nu (Var x) = op_taint tn1 (Var x)) /\
     alloca_frame cenv mid su t cenv mid u /\
     (!aid off sz i. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ aid < su.cs_next_id /\
       (!name a len. local_region cenv mid.scopes t name a len ==> off+sz <= a \/ a+len <= off) /\
       off <= i /\ i < off+sz /\ i IN nu.t_mem ==> i IN tn1.t_mem) /\
     (stage_guard ==> !name a len. local_region cenv mid.scopes u name a len ==>
                       regions_disjoint (w2n w) (type_memory_size_list tvs) a len) /\
     (~stage_guard ==> u = t /\ root = xs /\ w = sw /\ sl = su)` by
    (reverse (Cases_on `stage_guard`)
     >- (qpat_assum `(if F then _ else _) su = _`
           (strip_assume_tac o REWRITE_RULE [boolTheory.COND_CLAUSES,comp_return_def, pairTheory.PAIR_EQ]) >>
         qexistsl [`t`,`xs`,`sw`,`G1`,`tn1`] >>
         qpat_x_assum `op = staged` (SUBST_ALL_TAC o SYM) >>
         qpat_x_assum `su = sl` (SUBST_ALL_TAC o SYM) >>
         simp[cj 1 gas_origin_ptr_path_rules,alloca_frame_def] >>
         rpt gen_tac >> disch_then (ACCEPT_TAC o cj 3)) >>
     qpat_x_assum `(if T then _ else _) su = _` mp_tac >>
     simp[comp_bind_def,comp_ignore_bind_def] >>
     Cases_on `compile_alloc_buffer (type_memory_size_list tvs) su` >>
     rename1 `compile_alloc_buffer _ su = (buf,sm)` >>
     Cases_on `emit_void MCOPY [buf.buf_operand;Var xs;Lit (n2w (type_memory_size_list tvs))] sm` >>
     rename1 `emit_void MCOPY _ sm = (ret,sm')` >> Cases_on `ret` >>
     simp[comp_return_def] >> strip_tac >>
     `compile_copy_memory buf.buf_operand (Var xs) (type_memory_size_list tvs) sm = ((),sl)` by
       (`?n. type_memory_size_list tvs = SUC n` by
          metis_tac[arithmeticTheory.num_CASES,arithmeticTheory.NOT_ZERO_LT_ZERO] >>
        qpat_assum `emit_void MCOPY _ sm = ((),sm')` mp_tac >>
        gvs[compile_copy_memory_def]) >>
     `cs_extends su sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
     `cs_extends sm sl` by
       (drule_then strip_assume_tac abiTuplePropsTheory.compile_copy_memory_extends >>
        gvs[exprLoweringPropsTheory.same_blocks_def] >>
        irule compileEnvTheory.cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
     `fn_has_code su sm func /\ fn_has_code sm sl func` by
       (irule fn_has_code_split >> simp[]) >>
     `type_memory_size_list tvs < dimword (:256)` by decide_tac >>
     `expr_val_at cenv cx (TupleT tys) sa su mid (ArrayV (TupleV vs)) (Var xs) t` by
       (qpat_assum `op = Var xs` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `buf.buf_operand = staged` (SUBST_ALL_TAC o SYM) >>
     `?u root b Gu nu.
       (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (t,G1,tn1) [] (OK u,Gu,nu)) /\
       (!(H : (bool # 256 word # type_value) list # num list).
          stmt_state_rel H ctx func cenv cx mid t ==> stmt_state_rel H ctx func cenv cx mid u) /\
       (!D d. ghost_inv_at D lo d cenv cx mid G1 tn1 t ==> ghost_inv_at D lo d cenv cx mid Gu nu u) /\
       ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
       u.vs_inst_idx = LENGTH sl.cs_current_insts /\
       buf.buf_operand = Var root /\ not_fresh_at sl root /\
       lookup_var root u = SOME (n2w b) /\ ptr_covers Gu nu root u (type_memory_size_list tvs) /\
       FLOOKUP u.vs_allocas su.cs_next_id = SOME (b,type_memory_size_list tvs) /\
       lo <= b /\ b + type_memory_size_list tvs < dimword (:256) /\
       b + type_memory_size_list tvs <= u.vs_alloca_next /\
       (!name a len. local_region cenv mid.scopes u name a len ==>
         regions_disjoint b (type_memory_size_list tvs) a len) /\
       (!mem. mem_agree_outside nu.t_mem u.vs_memory mem ==>
         val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) /\
       allocas_from lo u /\ lo <= u.vs_alloca_next /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       (!aid ent. FLOOKUP t.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
       (!x. not_fresh_at su x ==> not_fresh_at sl x /\ lookup_var x u = lookup_var x t /\
         FLOOKUP Gu x = FLOOKUP G1 x /\ op_taint nu (Var x) = op_taint tn1 (Var x)) /\
       alloca_frame cenv mid su t cenv mid u /\
       (!aid off sz i. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ aid < su.cs_next_id /\
         (!name a len. local_region cenv mid.scopes t name a len ==> off+sz <= a \/ a+len <= off) /\
         off <= i /\ i < off+sz /\ i IN nu.t_mem ==> i IN tn1.t_mem)` by
       (irule (INST_TYPE [alpha |-> ``:256``]
          bodyFullMemoryStageTheory.body_full_memory_stage_frame_path) >>
        simp[] >> conj_tac
        >- (qexists `storage_trace_horizon mid.storage_trace` >> first_assum ACCEPT_TAC) >>
        qexistsl [`sa`,`TupleT tys`,`sw`,`xs`] >>
        simp[arithmeticTheory.ADD_COMM]) >>
     `b < dimword (:256)` by decide_tac >>
     qexistsl [`u`,`root`,`n2w b`,`Gu`,`nu`] >>
     simp[wordsTheory.w2n_n2w] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `compile_tuple_load_all cenv (Var root) tys 0 sl = (elems,ss)` by
    (qpat_assum `staged = Var root` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv sl` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `su` >> simp[]) >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sl x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sl x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `!mem. mem_agree_outside nu.t_mem u.vs_memory mem ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) [valueEncodingDefsTheory.val_in_memory_def]) >>
  qpat_assum `compile_tuple_load_all _ (Var root) _ 0 sl = _`
    (mp_then (Pos hd) mp_tac
      (Q.INST [`capacity` |-> `type_memory_size_list tvs`, `tvs` |-> `tvs`,
        `vs` |-> `vs`, `G` |-> `Gu`, `tn` |-> `nu`, `s` |-> `u`,
        `w` |-> `w`, `es` |-> `mid`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
        `PG` |-> `PG`] (INST_TYPE [alpha |-> ``:256``] body_assign_tuple_load_all_path))) >>
  disch_then (qspecl_then [`w`,`vs`,`u`,`tvs`,`shadow_ctx`,`nu`,`mid`,`lo`,
    `func`,`cx`,`ctx`,`PG`,`Gu`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`z`,`Gz`,`nz`] (map_every assume_tac o CONJUNCTS)))) >>
  `!id a cap. local_region cenv mid.scopes z id a cap <=>
              local_region cenv mid.scopes u id a cap` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `sl` >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid u` by
    (first_assum (MATCH_MP_TAC o SPEC_ALL) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid z` by
    (first_assum (MATCH_MP_TAC o SPEC_ALL) >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv mid.scopes z` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx mid z`
      (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!i id a cap. i < LENGTH gs /\ EL i gs = BaseTarget (NameTarget id) /\
     local_region cenv mid.scopes z id a cap ==>
     w2n w + type_memory_size (TupleTV tvs) <= a \/
     a + type_memory_size (EL i tvs) <= w2n w` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) (EL i tys) (EL i tvs) /\
      tuple_target_layout mid.scopes (BaseTarget (NameTarget id)) (EL i tys) (EL i tvs) (EL i vs)` by
       (qpat_assum `!i. i < LENGTH gs ==> tuple_target_aligned _ _ _ _ _ /\ _`
          (qspec_then `i` (strip_assume_tac o UNDISCH)) >>
        qpat_assum `EL i gs = BaseTarget (NameTarget id)` (SUBST_ALL_TAC) >> simp[]) >>
     qpat_assum `tuple_target_layout _ (BaseTarget (NameTarget id)) _ _ _`
       (qx_choose_then `dst_entry` (map_every assume_tac o CONJUNCTS) o
        PURE_REWRITE_RULE [tuple_target_layout_local]) >>
     `type_memory_size (EL i tvs) <= cap` by
       (qpat_assum `local_region cenv mid.scopes z id a cap`
          (qx_choosel_then [`region_entry`,`dst_p`,`dst_w`] (map_every assume_tac o CONJUNCTS) o
           PURE_REWRITE_RULE [local_region_def]) >>
        `region_entry = dst_entry` by
          (qpat_assum `lookup_scopes id mid.scopes = SOME region_entry` mp_tac >>
           qpat_assum `lookup_scopes id mid.scopes = SOME dst_entry` mp_tac >> simp[]) >>
        qpat_assum `local_ptrs_rel func cenv mid.scopes z`
          (qspecl_then [`id`,`dst_entry`,`dst_p`,`cap`] mp_tac o cj 1 o
           PURE_REWRITE_RULE [local_ptrs_rel_def]) >>
        simp[] >> strip_tac >> simp[]) >>
     `local_region cenv mid.scopes u id a cap` by (simp[] >> (metis_tac[])) >>
     ASM_CASES_TAC ``stage_guard:bool``
     >- (qpat_assum `stage_guard ==> !name a len. local_region _ _ _ _ _ _ ==> _`
           (drule_then (qspecl_then [`id`,`a`,`cap`] mp_tac)) >>
         simp[regions_disjoint_def] >> decide_tac) >>
     qpat_assum `~stage_guard ==> u = t /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     `local_region cenv mid.scopes t id a cap` by fs[] >>
     qpat_assum `expr_val_at cenv cx (TupleT tys) sa su mid _ op t`
       (qspec_then `TupleTV tvs` mp_tac o PURE_REWRITE_RULE [loweringPostsTheory.expr_val_at_def]) >>
     simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
     disch_then (DISJ_CASES_THEN2
       (qx_choosel_then [`rhs_aid`,`own_base`,`own_cap`] (map_every assume_tac o CONJUNCTS))
       (qx_choosel_then [`lender`,`borrow_base`,`borrow_cap`] (map_every assume_tac o CONJUNCTS)))
     >- (qpat_assum `!n lb lsz. local_region cenv mid.scopes t n lb lsz ==> _`
           (qspecl_then [`id`,`a`,`cap`] mp_tac) >>
         simp[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     `id <> lender` by
       (strip_tac >>
        drule tuplePlaceBorrowTheory.tuple_place_borrowed_tuple_path >>
        rewrite_tac[loweringPostsTheory.local_path_at_def] >>
        disch_then (qx_choosel_then [`lend_ty`,`lend_tv`,`lend_path`]
          (map_every assume_tac o CONJUNCTS)) >>
        qpat_assum `tuple_target_aligned _ _ (BaseTarget (NameTarget id)) _ _`
          (strip_assume_tac o PURE_REWRITE_RULE [tuple_target_aligned_local]) >>
        `lend_ty = EL i tys` by
          (qpat_assum `id = lender` (SUBST_ALL_TAC o SYM) >>
           UNDISCH_TAC ``cenv.ce_var_type id = SOME lend_ty`` >> simp[]) >>
        `lend_tv = EL i tvs` by
          (qpat_assum `lend_ty = EL i tys` SUBST_ALL_TAC >>
           UNDISCH_TAC ``evaluate_type (get_tenv cx) (EL i tys) = SOME lend_tv`` >> simp[]) >>
        `MEM (EL i tvs) tvs` by (irule listTheory.EL_MEM >> simp[] >> decide_tac) >>
        drule vyperTypingTheory.MEM_type_value_size_TupleTV >>
        drule tuplePlaceGeometryTheory.tuple_place_path_rank >>
        simp[] >> decide_tac) >>
     `local_region cenv mid.scopes z lender borrow_base borrow_cap` by
       (qpat_assum `!id a cap. local_region cenv mid.scopes z id a cap <=> _`
          (qspecl_then [`lender`,`borrow_base`,`borrow_cap`] (SUBST1_TAC)) >> fs[]) >>
     qpat_assum `local_ptrs_rel func cenv mid.scopes z`
       (qspecl_then [`lender`,`id`,`borrow_base`,`borrow_cap`,`a`,`cap`] mp_tac o cj 2 o
        PURE_REWRITE_RULE [local_ptrs_rel_def]) >>
     `lender <> id` by metis_tac[] >>
     simp[regions_disjoint_def] >> decide_tac) >>
  qspecl_then [`gs`,`tys`,`tvs`,`vs`,`elems`,`0`,`T`,`w2n w`,`tvs`,`vs`,
    `ctx`,`func`,`cenv`,`cx`,`mid`,`z`,`ss`,`sb`,`tops`,`env`,`es`,`mid`,`z`,
    `storage_trace_horizon mid.storage_trace`,
    `DF (storage_trace_horizon mid.storage_trace)`,`lo`,`Gz`,`nz`,
    `gas_explicit_sites ctx shadow_ctx`,`PG`,
    `\H v es r. ?gt. RetQ H v es gt r`,`RetQ`] mp_tac
    (INST_TYPE [alpha |-> ``:256``]
      body_assign_tuple_store_targets_full_path) >>
  (impl_tac >-
    (`ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid Gu nu u` by simp[] >>
     `ghost_inv_at (DF (storage_trace_horizon mid.storage_trace)) lo d cenv cx mid Gz nz z` by simp[] >>
     qpat_assum `ghost_inv_at _ lo d cenv cx mid Gz nz z`
       (strip_assume_tac o PURE_REWRITE_RULE [ghost_inv_at_def]) >>
     `z.vs_call_ctx.cc_static = cx.txn.is_static` by
       (qpat_assum `stmt_state_rel _ ctx func cenv cx mid z`
          (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel o
           MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
        simp[call_ctx_rel_def]) >>
     `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
       (disch_tac >>
        `allocas_below_fmp u` by simp[] >>
        `z.vs_initial_fmp = u.vs_initial_fmp` by
          (qpat_assum `state_frame z = state_frame _`
             (mp_tac o AP_TERM ``\s:venom_state. s.vs_initial_fmp``) >>
           simp[NoAsms,state_frame_def]) >>
        `z.vs_fmp = u.vs_fmp` by
          (qpat_assum `state_frame z = state_frame _`
             (mp_tac o AP_TERM ``\s:venom_state. s.vs_fmp``) >>
           simp[NoAsms,state_frame_def]) >>
        pure_rewrite_tac[ptrDisciplineTheory.allocas_below_fmp_def] >>
        qpat_assum `z.vs_initial_fmp = u.vs_initial_fmp` SUBST1_TAC >>
        qpat_assum `z.vs_fmp = u.vs_fmp` SUBST1_TAC >>
        qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
        qpat_assum `allocas_below_fmp u`
          (ACCEPT_TAC o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def])) >>
     `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at ss x) /\
      (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at ss x)` by
       (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
        qexists `sl` >> simp[]) >>
     `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
     qpat_assum `expr_sim_inv cenv cx env es`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_def]) >>
     simp[] >>
     conj_tac >-
       ((qx_gen_tac `i` >> disch_tac >>
        qpat_assum `!i. i < LENGTH tys ==> ?x. EL i elems = Var x /\ _`
          (qspec_then `i` mp_tac) >> (impl_tac >- simp[]) >>
        disch_then (qx_choose_then `x` (map_every assume_tac o CONJUNCTS)) >>
        qexists `x` >>
        rpt (conj_tac >- first_assum ACCEPT_TAC) >>
        qpat_x_assum `if is_word_type (EL i tys) then _ else _` mp_tac >>
        Cases_on `is_word_type (EL i tys)` >>
        pop_assum (fn th => simp_tac bool_ss [th,arithmeticTheory.ADD_0,AC ADD_ASSOC ADD_COMM]) >> (simp[]))) >>
     conj_tac >-
       (map_every qx_gen_tac [`i`,`id`,`a`,`cap`] >> strip_tac >>
        qpat_assum `!i id a cap. i < LENGTH gs /\ EL i gs = BaseTarget (NameTarget id) /\
                                local_region cenv mid.scopes z id a cap ==> _`
          (qspecl_then [`i`,`id`,`a`,`cap`] mp_tac) >> (impl_tac >- simp[]) >>
        simp[ADD_COMM]) >>
     conj_tac >-
       (map_every qx_gen_tac [`id`,`entry`,`x`,`cap`] >> strip_tac >>
        qpat_assum `!name entry p sz. lookup_scopes name mid.scopes = SOME entry /\
                       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> _`
          (qspecl_then [`id`,`entry`,`x`,`cap`] mp_tac) >> simp[]) >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
       ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`res`,`ee`,`r`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  `!tail. assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs))
        (mid with gas_obs := tail) = (res,ee with gas_obs := tail)` by
    (gen_tac >> simp[cj 57 vyperInterpreterTheory.evaluate_def]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (r,Gf,tf)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gz`,`z`,`nz`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`nu`] >> simp[]) >>
  reverse (qpat_x_assum `(res = INL () /\ _) \/ _`
    (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (qx_choose_then `sf` (map_every assume_tac o CONJUNCTS)))
      (map_every assume_tac o CONJUNCTS)))
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
      conj_tac >- (qexistsl_tac [`Gf`,`ee`,`r`,`res`,`tf`] >> simp[] >>
        qx_gen_tac `H` >> disch_tac >> conj_tac
        >- (qpat_assum `res = INR _` (SUBST1_TAC o SYM) >> simp[]) >>
        conj_tac >- (irule haltExitProjTheory.halt_exit_not_halt >> simp[]) >>
        disch_tac >> qpat_assum `!H tail. stmt_exit _ _ res r`
          (qspecl_then [`H`,`[]`] mp_tac) >>
        qpat_assum `res = INR _` SUBST1_TAC >>
        Cases_on `r` >> simp[stmtSimDefsTheory.stmt_exit_def,exprSimDefsTheory.expr_exit_def]) >>
      simp[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL ()`,`sf`,`tf`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) mid =
       (INL (),ee with gas_obs := mid.gas_obs)` by
    (qpat_assum `!tail. assign_tuple_targets _ _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >>
     simp[NoAsms,evaluation_state_component_equality]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:unit``]
       vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl_tac [`assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs))`,
                   `INL ()`,`ee with gas_obs := mid.gas_obs`] >>
     simp[cj 9 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_post H ctx func cenv cx e es sa su s0 mid _ op t`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
  `stmt_state_rel H ctx func cenv cx mid u /\
   ghost_inv_at (DF H) lo d cenv cx mid Gu nu u` by simp[] >>
  `stmt_state_rel H ctx func cenv cx mid z /\
   ghost_inv_at (DF H) lo d cenv cx mid Gz nz z` by simp[] >>
  qpat_assum `!st H D d. _ ==> stmt_state_rel H ctx func cenv cx ee sf /\ _`
    (qspecl_then [`st0`,`H`,`DF H`,`d`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!st H. _ ==> storage_well_formed_on cx ee (FST H)`
    (qspecl_then [`st0`,`H`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  `sa.cs_next_id <= su.cs_next_id` by
    (qpat_assum `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)`
       (ACCEPT_TAC o cj 3 o MATCH_MP (cj 2 exprLoweringPropsTheory.compile_expr_grows))) >>
  `alloca_frame cenv es sa s0 cenv mid u` by
    (irule stmtSimDefsTheory.alloca_frame_trans >>
     qexistsl_tac [`cenv`,`mid`,`t`,`su`] >> simp[]) >>
  `!aid off sz.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) ==>
      FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ aid < su.cs_next_id /\
      (!n b len. local_region cenv mid.scopes t n b len ==> off+sz <= b \/ b+len <= off) /\
      FLOOKUP z.vs_allocas aid = SOME (off,sz) /\
      (!n b len. local_region cenv mid.scopes z n b len ==> off+sz <= b \/ b+len <= off) /\
      mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz s0.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_frame cenv es sa s0 cenv mid t`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac o PURE_REWRITE_RULE [alloca_frame_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     qpat_assum `alloca_frame cenv es sa s0 cenv mid u`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac o PURE_REWRITE_RULE [alloca_frame_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by simp[] >>
     `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by simp[] >>
     `aid < su.cs_next_id` by simp[] >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_marked_path T ctx func t 0 (OK sf)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (r,Gf,tf)`
       (qspec_then `DF H` (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
         CONJUNCT1 o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >> simp[]) >>
  `alloca_inv t` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
       (ACCEPT_TAC o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv)) >>
  `alloca_history func sf /\ t.vs_alloca_next <= sf.vs_alloca_next` by
    (drule_all bodyMemBopRestWordPathTheory.rest_word_marked_allocation_posts >> simp[]) >>
  `s0.vs_alloca_next <= sf.vs_alloca_next` by simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x /\
       not_fresh_at sl x /\ not_fresh_at ss x` by
    (gen_tac >> disch_tac >> rpt conj_tac >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
          lookup_var x sf = SOME v` by
    (rpt strip_tac >> simp[]) >>
  `return_buf_frame d cenv sb sf` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `return_buf_frame d cenv su t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `return_buf_sep d cenv mid t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- fs[] >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `ctx`, `cx`,
                   `es`, `func`, `s0`, `sa`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!bw cap. d = SOME (bw, cap) ==> allocas_from (w2n bw + cap) sf` by
    (`gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK sf,Gf,tf)` by
       (qpat_assum `r = OK sf` (fn eq =>
          qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (r,Gf,tf)`
            (qspec_then `DF H` (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK sf,Gf,tf)` (fn path =>
       qpat_assum `return_buf_frame d cenv su t` (fn frame =>
         qpat_assum `return_buf_sep d cenv mid t` (fn sep =>
           mp_tac (MATCH_MP return_buf_allocas_path (LIST_CONJ [path,frame,sep]))))) >>
     simp[]) >>
  `return_buf_sep d cenv ee sf` by
    (irule return_buf_sep_transport >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cenv`, `mid`, `t`] >> simp[] >>
     rpt strip_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.local_region_kept) >>
     conj_tac
     >- (qexistsl_tac [`mid`, `u`, `su`] >> simp[]) >>
     qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
    (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
                           op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (gen_tac >> disch_tac >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee sf` by
    (rewrite_tac[alloca_frame_def] >>
     map_every qx_gen_tac [`aid`,`off`,`sz`] >> strip_tac >>
     qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _ /\ _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     qpat_assum `!aid off sz. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     simp[] >> metis_tac[]) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
     (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) /\
     off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem` by
    (map_every qx_gen_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
     qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _ /\ _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     qpat_assum `!aid off sz. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     `i IN nz.t_mem` by simp[IgnAsm `nz.t_mem = nu.t_mem`] >>
     `i IN nu.t_mem` by
       (qpat_assum `nz.t_mem = nu.t_mem` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     `i IN tn1.t_mem` by
       (qpat_assum `!aid off sz i. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
       (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sf` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee sf`
       (mp_then Any mp_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  `storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (qpat_assum `storage_well_formed_on cx ee (FST H)` mp_tac >>
     simp[NoAsms,vyperStorageFootprintTheory.storage_well_formed_on_def,
          stmtSimAppendStorageComposeTheory.get_storage_gas_obs]) >>
  `ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gf tf sf` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gf tf sf` mp_tac >>
     simp[NoAsms,ghost_inv_at_def] >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `gas_marked_path T ctx func t 0 (OK u)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,Gu,nu)`
       (qspec_then `DF H` (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
         CONJUNCT1 o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `gas_marked_path T ctx func t 0 (OK u)`
       (mp_then Any mp_tac bodyMemBopRestWordPathTheory.rest_word_marked_allocation_posts) >>
     qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >> simp[]) >>
  conj_tac >-
    (qpat_assum `r = OK sf` (SUBST1_TAC o SYM) >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,G1,tn1) [] (r,Gf,tf)`
       (qspec_then `DF H` ACCEPT_TAC)) >>
  conj_tac >-
    (rewrite_tac[stmt_lands_def] >> disj1_tac >>
     rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  conj_tac >- MATCH_ACCEPT_TAC stmtSimPropsTheory.cenv_top_ext_refl >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         simp_tac (srw_ss()) [stmt_state_rel_start_gas_obs, return_buf_sep_gas_obs] >>
         first_assum ACCEPT_TAC,
         qpat_assum `alloca_frame cenv es sa s0 cenv ee sf` mp_tac >>
         simp_tac (srw_ss()) [alloca_frame_def]]
QED

(* Every target a local. *)
Theorem body_assign_tuple_locals_full:
  !cx ids e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) ids /\
    lowered_value_type cenv e = expr_type e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)))
      (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule body_assign_tuple_targets_full >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bindings`, `env`, `env'`, `tops`] >>
  simp[EVERY_MAP] >>
  first_assum ACCEPT_TAC
QED

Triviality tuple_immutable_exact_slot_size:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st ==>
  !ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size tv
Proof
  strip_tac >>
  qpat_assum `body_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  rpt strip_tac >>
  qpat_assum `cenv.ce_struct_fields = _` (SUBST1_TAC o SYM) >>
  rewrite_tac[type_mem_bytes_type_memory_bytes] >>
  irule expr_sim_inv_memory_size >> simp[] >> metis_tac[]
QED

Theorem tuple_immutable_slot_span[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (NONE,id) = SOME ty /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  evaluate_type (type_env tops) ty = SOME tv /\
  (?pre post vis slot.
     tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
     off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre) /\
  off + type_memory_size tv <= lo
Proof
  strip_tac >>
  drule body_inv_immutable_section_layout >>
  rewrite_tac[immutable_section_layout_def] >> strip_tac >>
  first_x_assum drule >>
  disch_then (qx_choosel_then [`pre`,`post`,`vis`,`ty'`,`slot`] strip_assume_tac) >>
  `MEM (VariableDecl vis Immutable id ty' slot) tops` by simp[] >>
  qpat_assum `body_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `ty' = ty` by
    (drule_all build_maps_variable >> strip_tac >>
     qpat_assum `!i. cenv.ce_module_var_type _ = _`
       (qspec_then `id` mp_tac) >>
     gvs[optionTheory.SOME_11]) >>
  qpat_x_assum `ty' = ty` SUBST_ALL_TAC >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  `evaluate_type (type_env tops) ty = SOME tv` by metis_tac[] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
   type_memory_size tv` by
    (drule_all tuple_immutable_exact_slot_size >> simp[]) >>
  drule_then assume_tac cx_tops_module >>
  `lo = imm_len tops` by fs[dead_lo_ok_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`pre`,`post`,`vis`,`slot`] >> asm_rewrite_tac[]) >>
  qpat_assum `lo = imm_len _` SUBST1_TAC >>
  rewrite_tac[imm_len_def] >>
  qpat_assum `off = _` SUBST1_TAC >>
  qpat_assum `type_mem_bytes _ _ = _` (SUBST1_TAC o SYM) >>
  qpat_assum `tops = _` SUBST1_TAC >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`off` |-> `0`] (SPEC_ALL immutable_declaration_interval_bound)))
QED

(* A tuple head needs exact sizes at the two declaration occurrences,
   not uniqueness of the entire struct namespace. *)

Theorem tuple_immutable_section_post[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st /\
  tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  LENGTH sec2 = LENGTH sec1 /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < LENGTH sec1 /\ j IN M1 ==> imm_section_dead tops sec1 j) /\
  (!j. j < LENGTH sec1 /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes sec2 off tv j) ==>
  !j. j < LENGTH sec2 /\ j IN M2 ==> imm_section_dead tops sec2 j
Proof
  strip_tac >>
  `!tt vv. evaluate_type (type_env tops) tt = SOME vv ==>
     type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) tt =
     type_memory_size vv` by
    (rpt strip_tac >> drule_all tuple_immutable_exact_slot_size >> simp[]) >>
  gen_tac >> strip_tac >>
  Cases_on `off <= j /\ j < off + type_memory_size tv`
  >- (rewrite_tac[imm_section_dead_def] >>
      qexistsl_tac [`pre`,`vis`,`id`,`ty`,`slot`,`post`,`tv`] >>
      metis_tac[]) >>
  `imm_section_dead tops sec1 j` by metis_tac[] >>
  qpat_x_assum `imm_section_dead tops sec1 j` mp_tac >>
  rewrite_tac[imm_section_dead_def] >>
  disch_then (qx_choosel_then [`p`,`vis'`,`id'`,`ty'`,`slot'`,`r`,`tv'`]
    strip_assume_tac) >>
  `pre ++ VariableDecl vis Immutable id ty slot :: post =
   p ++ VariableDecl vis' Immutable id' ty' slot' :: r` by metis_tac[] >>
  qabbrev_tac `a = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) p` >>
  `pre <> p` by
    (strip_tac >>
     qpat_x_assum `pre = p` SUBST_ALL_TAC >>
     qpat_x_assum `_ ++ _ = _ ++ _` (strip_assume_tac o SRULE []) >>
     qpat_x_assum `ty = ty'` (SUBST_ALL_TAC o SYM) >>
     `tv' = tv` by
       (qpat_assum `evaluate_type _ _ = SOME tv` (fn th =>
          qpat_assum `evaluate_type _ _ = SOME tv'` (mp_tac o REWRITE_RULE [th])) >>
        simp[NoAsms, EQ_SYM_EQ]) >>
     `off = a` by simp[Abbr `a`] >>
     drule_then assume_tac (CONJUNCT1 mem_dead_bytes_range) >>
     qpat_x_assum `tv' = tv` SUBST_ALL_TAC >> decide_tac) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty = type_memory_size tv` by metis_tac[] >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' = type_memory_size tv'` by metis_tac[] >>
  `off + type_memory_size tv <= a \/ a + type_memory_size tv' <= off` by
    (drule imm_frame_occurrence_separation >>
     disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
     simp[Abbr `a`]) >>
  qexistsl_tac [`p`,`vis'`,`id'`,`ty'`,`slot'`,`r`,`tv'`] >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  qpat_assum `Abbrev (a = _)`
    (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `mem_dead_bytes sec2 a tv' = mem_dead_bytes sec1 a tv'` suffices_by simp[] >>
  irule mem_dead_bytes_frame >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  first_assum (irule_at (Pos (el 1))) >> decide_tac
QED

Theorem tuple_immutable_word_mem_ok[local]:
  compile_imm_store_word imm dst v sa = ((),sb) /\
  eval_operand dst s = SOME a /\ w2n a + 32 <= s.vs_alloca_next /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> namedCases_on `imm` ["", "reg"]
  >- (fs[compile_imm_store_word_def] >>
      drule emitted_insts_emit_void >> simp[] >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_ISTORE,
           inst_dload_in_section_def, mk_inst_def]) >>
  drule compile_imm_store_word_result >> strip_tac >>
  `eval_operand reg s = SOME 0w` by fs[] >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id ADD [reg; dst] ["%" ++ toString sa.cs_next_var];
      mk_inst (sa.cs_next_id + 1) ISTORE
        [Var ("%" ++ toString sa.cs_next_var); v] []]` by
    simp[emitted_insts_def, DROP_APPEND] >>
  conj_tac >- simp[] >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_ISTORE] >>
  simp[inst_dload_in_section_def, mk_inst_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, wordsTheory.WORD_ADD_0,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Only the access checks: the range's byte and ghost effects come from
   the immutable transfer suppliers. The LocCode destination is a literal. *)

Theorem tuple_immutable_copy_one_mem_ok[local]:
  immutable_store_one imm src (Lit b) off sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!base x. imm = SOME base /\ base = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w) /\
  w2n a + off + 32 <= s.vs_alloca_next /\ w2n a + off < dimword (:256) /\
  w2n b + off + 32 <= s.vs_alloca_next /\ w2n b + off < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  `!c. compile_lit_byte_offset (Lit b) off c = (Lit (b + n2w off),c)` by
    (Cases_on `off = 0` >> simp[compile_lit_byte_offset_def,
       compileEnvTheory.comp_return_def, wordsTheory.WORD_ADD_0]) >>
  simp[immutable_store_one_def, immutable_comp_bind_cases] >>
  rpt strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sp,c1)` >>
  rename1 `emit_op MLOAD [sp] c1 = (loaded,c2)` >>
  drule_all immutable_byte_offset_old_execution >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  drule_all exprSimMapKeyTheory.emit_MLOAD_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  drule emit_op_extends >> strip_tac >>
  `s1.vs_alloca_next = s.vs_alloca_next /\ s2.vs_alloca_next = s.vs_alloca_next /\
   s2.vs_labels = s.vs_labels` by fs[venom_state_component_equality] >>
  `!base. imm = SOME base ==> eval_operand base s2 = SOME 0w` by
    (rpt strip_tac >> irule ctorAbiActualObservationsTheory.ctor_actual_old_operand >>
     qexistsl_tac [`s`,`sa`] >> simp[] >> rpt strip_tac >>
     `not_fresh_at c1 x` by fs[loweringStateRelDefsTheory.not_fresh_at_def] >> simp[]) >>
  `w2n (a + n2w off : bytes32) + 32 <= s1.vs_alloca_next /\
   w2n (b + n2w off : bytes32) + 32 <= s2.vs_alloca_next` by
    (simp[] >> conj_tac >>
     irule bodyImmutableCopyMemoryTheory.body_immutable_copy_offset_range >> simp[]) >>
  `eval_operand (Lit (b + n2w off)) s2 = SOME (b + n2w off)` by simp[eval_operand_def] >>
  drule_all tuple_immutable_word_mem_ok >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts c1 c2) s1` by
    (drule_all allocaFootprintTheory.emit_mload_mem_ok >> simp[]) >>
  `emitted_insts c1 sb = emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    (irule emitted_insts_append >> simp[]) >>
  `sb.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 sb` by
    simp[listTheory.APPEND_ASSOC] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
       emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    (`emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
       (irule emitted_insts_append >> first_assum (irule_at Any) >>
        first_assum ACCEPT_TAC) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa c1) s` by
    (qpat_assum `compile_lit_byte_offset src off sa = _`
       (mp_then Any mp_tac bodyImmutableCopyMemoryTheory.body_immutable_byte_offset_mem_ok) >> simp[]) >>
  `run_inst_seq (emitted_insts sa c1 ++ emitted_insts c1 c2) s = OK s2` by
    (qpat_assum `run_inst_seq (emitted_insts sa c1) s = _`
       (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  asm_rewrite_tac[listTheory.APPEND_ASSOC] >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  irule run_inst_seq_mem_ok_append >> simp[]
QED

Theorem tuple_immutable_copy_range_mem_ok[local]:
  !n off sa sb s a.
    compile_imm_store_words imm src (Lit b) n off sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!base x. imm = SOME base /\ base = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME a /\
    (!base. imm = SOME base ==> eval_operand base s = SOME 0w) /\
    w2n a + off + 32*n <= s.vs_alloca_next /\
    w2n b + off + 32*n <= s.vs_alloca_next /\
    s.vs_alloca_next < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct
  >- simp[compile_imm_store_words_def, compileEnvTheory.comp_return_def,
           emitted_insts_def, run_inst_seq_mem_ok_def] >>
  simp[immutable_store_suc, compileEnvTheory.comp_ignore_bind_def,
       immutable_comp_bind_cases] >>
  rpt strip_tac >>
  rename1 `immutable_store_one imm src (Lit b) off sa = ((),sm)` >>
  `off + (w2n a + 32) <= s.vs_alloca_next /\ off + w2n a < dimword (:256) /\
   off + (w2n b + 32) <= s.vs_alloca_next /\ off + w2n b < dimword (:256)` by
    (fs[arithmeticTheory.MULT_SUC] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (drule tuple_immutable_copy_one_mem_ok >>
     disch_then (qspec_then `s` mp_tac) >> simp[] >>
     qexists_tac `a` >> simp[]) >>
  `eval_operand (Lit b) s = SOME b` by simp[eval_operand_def] >>
  drule (SRULE [] (Q.INST [`dst` |-> `Lit b`] immutable_store_one_old_execution)) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    fs[venom_state_component_equality] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand src t = SOME a /\
   (!base. imm = SOME base ==> eval_operand base t = SOME 0w)` by
    metis_tac[ctorAbiActualObservationsTheory.ctor_actual_old_operand] >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (first_x_assum irule >> simp[] >> qexists_tac `off + 32` >>
     fs[arithmeticTheory.MULT_SUC] >> decide_tac) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (drule (SRULE [] (Q.INST [`dst` |-> `Lit b`] immutable_store_words_old_execution)) >>
     disch_then (qspecl_then [`a`,`t`] mp_tac) >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  pop_assum SUBST1_TAC >> irule run_inst_seq_mem_ok_append >> simp[]
QED

(* The segment overwrites an emitted temporary if it was already bound.
   Only the compiler's live names, not the entire register domain, matter. *)
Theorem tuple_immutable_word_segment[local]:
  compile_imm_store_word imm dst v sa = ((),sb) /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
     op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tf u.
    run_inst_seq (emitted_insts sa sb) s = OK u /\ same_blocks sa sb /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; ISTORE]) (emitted_insts sa sb) /\
    tf.t_mem = (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
      {w2n a + k | k IN op_taint tn v} /\
    tf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tf p u n)
Proof
  strip_tac >>
  `same_blocks sa sb` by
    (Cases_on `imm` >>
     gvs[compile_imm_store_word_def, emitHelperTheory.emit_op_def,
         emitHelperTheory.emit_void_def, fresh_id_def, fresh_var_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def, same_blocks_def]) >>
  namedCases_on `imm` ["", "reg"]
  >- (fs[compile_imm_store_word_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      qspecl_then [`dst`, `v`, `a`, `value`, `D`, `fn`, `PG`] mp_tac
        (Q.GENL [`arg`, `v`, `a`, `value`, `D`, `fn`, `PG`]
           (Q.INST [`id` |-> `sa.cs_next_id`] ctor_istore_segment)) >>
      (impl_tac >- simp[]) >>
      disch_then strip_assume_tac >>
      qexistsl_tac [`Gf`,`tnf`,`t`] >> gvs[mk_inst_def]) >>
  drule compile_imm_store_word_result >> strip_tac >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id ADD [reg; dst] ["%" ++ toString sa.cs_next_var];
      mk_inst (sa.cs_next_id + 1) ISTORE
        [Var ("%" ++ toString sa.cs_next_var); v] []]` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `!p. not_fresh_at sa p ==> p <> STRING #"%" (toString sa.cs_next_var)` by
    simp[not_fresh_at_def] >>
  `!x. v = Var x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> gvs[copy_old_operand_def, not_fresh_at_def]) >>
  `eval_operand reg s = SOME 0w /\ op_taint tn reg = {} /\ op_prov G reg = NONE` by fs[] >>
  mp_tac (Q.INST [`P` |-> `not_fresh_at sa`, `id` |-> `sa.cs_next_id`,
                 `tmp` |-> `STRING #"%" (toString sa.cs_next_var)`,
                 `region` |-> `reg`] ctor_word_store_seq) >>
  (impl_tac >- fs[copy_old_operand_def, not_fresh_at_def]) >> disch_then strip_assume_tac >>
  qexistsl_tac [`Gf`,`tnf`,`t`] >> gvs[mk_inst_def]
QED

Theorem tuple_immutable_word_path[local]:
  compile_imm_store_word imm dst v sa = ((),sb) /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
     op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gf tf.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
    same_blocks sa sb /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    u.vs_memory = (mstore (w2n a) value s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (w2n a,value) /\
    tf.t_mem =
      (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
        {w2n a + k | k IN op_taint tn v} /\
    tf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tf p u n)
Proof
  strip_tac >>
  drule_all tuple_immutable_word_segment >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `!x. v = Var x ==> not_fresh_at sa x` by fs[copy_old_operand_def] >>
  `!base. imm = SOME base ==> eval_operand base s = SOME 0w` by simp[] >>
  drule_all immutable_store_word_old_execution >> strip_tac >>
  gvs[immutable_execution_frame_def, Excl "GSYM"] >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  rename1 `tf.t_stor = tn.t_stor` >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ _ Gf tf` >>
  `w2n a + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all tuple_immutable_word_mem_ok >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >> simp[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> simp[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem tuple_immutable_word_base[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\ 0 < lo /\
  local_ptrs_reserved cenv sa /\ cenv.ce_imm_alloca = SOME bas ==>
  copy_old_operand sa bas /\ eval_operand bas s = SOME 0w /\
  op_taint tn bas = {} /\ op_prov G bas = NONE
Proof
  strip_tac >>
  drule_all membership_immutable_base_value >> strip_tac >>
  Cases_on `bas` >>
  fs[copy_old_operand_def, ptrDisciplineTheory.op_taint_def,
     ptrDisciplineTheory.op_prov_def, ghost_inv_at_def] >>
  metis_tac[local_ptrs_reserved_imm_base]
QED

(* This is the cursor adjustment of the very same mstore endpoint. *)

Theorem tuple_immutable_word_stmt_post[local]:
  stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
  expr_sim_inv ce cx env ee /\ local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\ value_has_type tv v /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
           vs_immutables := s.vs_immutables|>) = s /\
  u.vs_memory = (mstore off (typed_val_to_w256 tv v) s).vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\ ~block_is_terminated sb ==>
  stmt_post H ctx func cx lctx ce ce sa sb ee s (INL ()) fin
    (u with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `immutable_value_admissible tv v` by (irule evaluated_immutable_admissible >> metis_tac[]) >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  drule_all stmtSimDeclStoreTheory.typed_word_store >> disch_then (qspecl_then [`off`,`s`] strip_assume_tac) >>
  `immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) u.vs_memory)` by
    (irule immutable_memory_bytes >> simp[]) >>
  `~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  irule immutable_assign_suffix_stmt_post >>
  simp[LENGTH_mstore_eq] >>
  qexistsl_tac [`env`,`id`,`tv`,`ty`,`off`,`v`] >>
  gvs[] >> rpt strip_tac >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def,mstore_mem_bytes_at_disjoint]
QED

(* The byte and taint frame restores the boundary for all three LocCode
   suffixes, independently of how the bytes inside the slot were produced. *)

Theorem tuple_immutable_suffix_ghost_post[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st /\
  stmt_state_rel H ctx func cenv cx st s /\ ghost_inv_at D lo d cenv cx st G tn s /\
  dead_lo_ok H D lo cenv cx /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (NONE,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ st'.scopes = st.scopes /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
  q.vs_transient = s.vs_transient /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  allocas_from lo q /\ lo <= q.vs_alloca_next /\
  (!i. ~(off <= i /\ i < off + type_memory_size tv) ==>
       mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. ~(off <= i /\ i < off + type_memory_size tv) /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  (!i. off <= i /\ i < off + type_memory_size tv /\ i IN tf.t_mem ==>
       mem_dead_bytes (mem_bytes_at 0 lo q.vs_memory) off tv i) ==>
  ghost_inv_at D lo d cenv cx st' Gf tf q
Proof
  strip_tac >>
  `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
  `cenv.ce_module = NONE` by fs[body_inv_def, cenv_module_pins_def] >>
  `FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
   cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty` by simp[] >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_declared_region >> strip_tac >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  `!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p q n` by
    (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  simp[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
      `ptr_covers G tn p s sz /\
       (!w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory entry.type entry.value (w2n w) mem)` by metis_tac[] >>
      conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `local_region cenv st.scopes s name (w2n w) sz` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
        (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >>
         rewrite_tac[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
         disch_then (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac o CONJUNCT1) >>
         simp[] >> metis_tac[]) >>
      `val_footprint entry.type entry.value <= type_memory_size entry.type` by
        metis_tac[exprSimPropsTheory.val_footprint_le] >>
      `regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
      `!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
            ~(off <= i /\ i < off + type_memory_size tv)` by
        (qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
         rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
         rpt strip_tac >> decide_tac) >>
      irule ghostObservationPtrTheory.robust_val_in_memory_exterior_no_new_taint >> simp[] >>
      qexistsl_tac [`{i | off <= i /\ i < off + type_memory_size tv}`,
                    `s.vs_memory`,`q.vs_memory`,`tn.t_mem`,`tf.t_mem`] >> simp[]) >>
  conj_tac
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME r) _ _ _ _` >> PairCases_on `r` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- gs[stor_taint_ok_at_def,dead_lo_ok_def] >>
  conj_tac
  >- (`!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
          EL j (mem_bytes_at 0 lo q.vs_memory) = EL j (mem_bytes_at 0 lo s.vs_memory)` by
        (rpt strip_tac >>
         `mem_bytes_at j 1 q.vs_memory = mem_bytes_at j 1 s.vs_memory` by metis_tac[] >>
         qpat_assum `mem_bytes_at j 1 _ = _`
           (mp_tac o AP_TERM ``EL 0 : byte list -> byte``) >>
         simp[valueEncodingProofsTheory.EL_mem_bytes_at]) >>
      drule_all tuple_immutable_slot_span >> strip_tac >>
      rpt strip_tac >>
      qpat_x_assum `cx_tops cx = tops` SUBST_ALL_TAC >>
      irule tuple_immutable_section_post >>
      simp[valueEncodingPropsTheory.LENGTH_mem_bytes_at] >>
      reverse conj_tac >- metis_tac[] >>
      qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`id`,`post`,`pre`,
                    `mem_bytes_at 0 lo s.vs_memory`,`slot`,`tv`,`ty`,`vis`] >>
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM listTheory.APPEND_ASSOC,listTheory.APPEND]) >>
      rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >>
      qpat_x_assum `tops = _` SUBST_ALL_TAC >>
      qpat_x_assum `off = _` (SUBST1_TAC o SYM) >>
      simp[] >> metis_tac[]) >>
  metis_tac[local_ptrs_reserved_imm_base]
QED

Theorem tuple_immutable_word_head_joint[local]:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env st /\
  cx.in_deploy /\ supported_immutable_type tops (src,id) = SOME ty /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\ ~cx_const_name cx (src,id) /\
  ce.ce_is_ctor /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  is_word_type ty /\ value_has_type tv vi /\
  stmt_state_rel H0 ctx fn ce cx st s /\ dead_lo_ok H0 D0 lo ce cx /\
  ghost_inv_at D0 lo d ce cx st G tn s /\
  compile_store_at_loc ce.ce_imm_alloca (Lit (n2w off)) op (SOME LocCode) sa = ((),sb) /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  copy_old_operand sa op /\
  eval_operand op s = SOME (typed_val_to_w256 tv vi) /\ op_taint tn op = {} /\
  local_ptrs_reserved ce sa /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~block_is_terminated sb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?fin q Gf tf.
    eval_target_place cx (TopLevelNameTarget (src,id)) st = (INL (ImmutablePlace src id []),st) /\
    write_place cx (ImmutablePlace src id []) vi st = (INL (),fin) /\
    fin.scopes = st.scopes /\ fin.gas_obs = st.gas_obs /\ fin.storage_trace = st.storage_trace /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!H : (bool # 'b word # type_value) list # num list.
      stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
      stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!(H : (bool # 'b word # type_value) list # num list) D.
      stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
      ghost_inv_at D lo d ce cx st G tn s ==> ghost_inv_at D lo d ce cx fin Gf tf q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_fmp = s.vs_fmp /\ q.vs_call_ctx = s.vs_call_ctx /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p q n) /\
    (!a k. regions_disjoint a k off 32 ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32} /\
    (!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==> val_in_memory tv vi off mem) /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans
Proof
  strip_tac >>
  drule_all immutableAssignMetadataTheory.immutable_target_place_state >> strip_tac >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_target_layout >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `ce.ce_module = NONE` by fs[body_inv_def,cenv_module_pins_def] >>
  qpat_x_assum `src = ce.ce_module` SUBST_ALL_TAC >>
  `FLOOKUP ce.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
   ce.ce_module_var_type (NONE,id) = SOME ty` by metis_tac[] >>
  `off + type_memory_size tv <= lo` by
    (drule_all tuple_immutable_slot_span >> simp[]) >>
  `type_memory_size tv = 32` by metis_tac[stmtSimDeclStoreTheory.typed_word_store] >>
  `off + 32 <= lo /\ 0 < lo` by fs[] >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule stateRelProjTheory.stmt_state_rel_alloca_room >>
     simp[exprLoweringPropsTheory.alloca_room_def] >> decide_tac) >>
  `off < dimword (:256)` by decide_tac >>
  drule_all immutableDeployAssignSourceFrameTheory.immutable_assign_source_lookup >> strip_tac >>
  drule_all bodyImmutableAugAssignStoreTheory.immutable_augassign_write_source >>
  disch_then (qspec_then `vi` assume_tac) >>
  qmatch_asmsub_abbrev_tac `write_place _ _ _ _ = (INL (),fin)` >>
  `fin.scopes = st.scopes /\ fin.gas_obs = st.gas_obs /\ fin.storage_trace = st.storage_trace` by
    (drule vyperPlaceFramesTheory.write_immutable_place_frame >>
     disch_then strip_assume_tac >> simp[]) >>
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) op sa = ((),sb)` by
    fs[stmtLoweringTheory.compile_store_at_loc_def] >>
  `!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
       op_taint tn base = {} /\ op_prov G base = NONE` by
    (rpt strip_tac >> drule_all tuple_immutable_word_base >> simp[]) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {} /\ op_prov G (Lit (n2w off)) = NONE /\
   w2n (n2w off : bytes32) + 32 <= lo` by
    simp[eval_operand_def,ptrDisciplineTheory.op_taint_def,ptrDisciplineTheory.op_prov_def,
         wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  drule_all tuple_immutable_word_path >>
  disch_then (qspecl_then [`explicit`,`PG`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  `w2n (n2w off : bytes32) = off` by simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `!a k. regions_disjoint a k off 32 ==>
     mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[mstore_mem_bytes_at_disjoint]) >>
  qexistsl_tac [`fin`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tf`] >>
  simp[ghostPcTransportPtrTheory.ghost_inv_at_inst_idx,ptr_covers_def,lookup_var_def] >>
  conj_tac
  >- (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule tuple_immutable_word_stmt_post >>
      metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32}` by simp[] >>
      `!i. ~(off <= i /\ i < off + type_memory_size tv) ==>
           mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
        (rpt strip_tac >> qpat_assum `!a k. regions_disjoint a k off 32 ==> _` irule >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      `!i. ~(off <= i /\ i < off + type_memory_size tv) /\ i IN tf.t_mem ==> i IN tn.t_mem` by simp[] >>
      `!i. off <= i /\ i < off + type_memory_size tv /\ i IN tf.t_mem ==>
           mem_dead_bytes (mem_bytes_at 0 lo u.vs_memory) off tv i` by
        (simp[] >> metis_tac[]) >>
      `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
           FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
      `lo <= u.vs_alloca_next` by simp[] >>
      drule_all tuple_immutable_suffix_ghost_post >> simp[]) >>
  simp[GSYM lookup_var_def,allocas_from_def,allocas_below_fmp_def] >>
  metis_tac[assignTuplePtrStoreWordTheory.typed_word_store_robust_ptr]
QED

(* Match the ordinary byte transfer and the annotated run before moving
   the instruction cursor. The same run also discharges access safety. *)

(* The offset supplier already works with live old operands.  Its coverage
   theorem handles both the unchanged root and the generated ADD output. *)
Theorem tuple_immutable_read_segment[local]:
  compile_lit_byte_offset (Var root) off sa = (sp,sm) /\
  emit_op MLOAD [sp] sm = (v,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME b /\
  ptr_covers G tn root s capacity /\
  off + 32 <= capacity /\ w2n b + off < dimword (:256) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tf u.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    copy_old_operand sb v /\ (?value. eval_operand v u = SOME value) /\
    op_taint tf v = mem_word_taint tn.t_mem (w2n (b + n2w off)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p u n)
Proof
  strip_tac >>
  `copy_old_operand sa (Var root) /\ eval_operand (Var root) s = SOME b /\
   op_taint tn (Var root) = {}` by
    gvs[copy_old_operand_def,eval_operand_def,ptr_covers_def] >>
  drule_all exprPtrCodeCopyOffsetTheory.code_copy_source_offset >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sm t` >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `off < capacity` by decide_tac >>
  drule_all (Q.INST [`n` |-> `32`] exprPtrCodeCopyOffsetTheory.code_copy_destination_coverage) >>
  disch_then (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  drule_all exprSimMapKeyTheory.emit_MLOAD_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `lookup_var p t = SOME (b + n2w off)` by fs[eval_operand_def] >>
  `!q. not_fresh_at sm q ==> q <> STRING #"%" (toString sm.cs_next_var)` by
    simp[not_fresh_at_def] >>
  `run_inst_seq [mk_inst sm.cs_next_id MLOAD [Var p]
       [STRING #"%" (toString sm.cs_next_var)]] t = OK u` by fs[] >>
  drule_all (Q.INST [`P` |-> `not_fresh_at sm`] ctor_mload_segment) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule code_offset_insts >> strip_tac >>
  qexistsl_tac [`Gf'`,`tnf'`,`u`] >>
  fs[copy_runtime_frame_def,emit_op_same_blocks] >>
  `!q. not_fresh_at sa q ==> not_fresh_at sm q` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  rpt conj_tac
  >- metis_tac[run_inst_seq_append]
  >- simp[APPEND_ASSOC]
  >- fs[same_blocks_def]
  >- (simp[] >> irule instSeqComposePtrTheory.inst_seq_ptr_uniform_append >>
      conj_tac >- (qexistsl [`Gf`,`t`,`tnf`] >> simp[]) >>
      fs[EVERY_MEM,is_terminator_def])
  >- (simp[EVERY_APPEND,mk_inst_def] >> fs[EVERY_MEM] >> metis_tac[])
  >- simp[copy_old_operand_def,not_fresh_at_def]
  >> metis_tac[]
QED

Theorem tuple_immutable_copy_one_segment[local]:
  immutable_store_one imm (Var root) (Lit a) off sa = ((),sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME b /\
  ptr_covers G tn root s capacity /\
  off + 32 <= capacity /\ w2n b + off < dimword (:256) /\
  w2n (a + n2w off) + 32 <= lo /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tf u.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    (!x. x IN tf.t_mem <=>
      if w2n (a + n2w off) <= x /\ x < w2n (a + n2w off) + 32
      then w2n (b + n2w off) + (x - w2n (a + n2w off)) IN tn.t_mem
      else x IN tn.t_mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p u n)
Proof
  strip_tac >>
  drule immutable_store_one_old_execution >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[eval_operand_def] >>
  (impl_tac >- fs[copy_old_operand_def]) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  fs[immutable_store_one_def,immutable_comp_bind_cases] >>
  `!c. compile_lit_byte_offset (Lit a) off c = (Lit (a + n2w off),c)` by
    (Cases_on `off = 0` >> simp[compile_lit_byte_offset_def,comp_return_def,wordsTheory.WORD_ADD_0]) >>
  gvs[] >>
  rename1 `emit_op MLOAD [sp] sm = (v,sr)` >>
  `w2n b + off < dimword (:256)` by decide_tac >>
  drule_all tuple_immutable_read_segment >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sr) s = OK r` >>
  `!p. not_fresh_at sa p ==> not_fresh_at sr p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `r.vs_labels = s.vs_labels` by
    (qpat_assum `run_inst_seq (emitted_insts sa sr) s = OK r`
       (mp_then (Pos hd) mp_tac stmtReasonMemoryTheory.run_inst_seq_data_section) >>
     impl_tac >- (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[is_terminator_def]) >>
     simp[]) >>
  `!base. imm = SOME base ==> eval_operand base r = SOME 0w /\
      op_taint tf base = {} /\ op_prov Gf base = NONE` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> rpt conj_tac
     >- metis_tac[ctorAbiActualObservationsTheory.ctor_actual_old_operand,copy_old_operand_def]
     >- metis_tac[emittedSeqComposePtrTheory.old_operand_taint_frame,copy_old_operand_def]
     >> metis_tac[exprPtrCtorCodeLoadTheory.old_operand_prov_frame]) >>
  `eval_operand (Lit (a+n2w off)) r = SOME (a+n2w off) /\
   op_taint tf (Lit (a+n2w off)) = {} /\ op_prov Gf (Lit (a+n2w off)) = NONE` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  drule_all tuple_immutable_word_segment >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sr sb) r = OK t` >>
  `sb.cs_current_insts = sr.cs_current_insts ++ emitted_insts sr sb` by
    (Cases_on `imm`
     >- (fs[compile_imm_store_word_def] >> drule emit_void_extends >> simp[])
     >> drule compile_imm_store_word_result >> strip_tac >>
     PURE_REWRITE_TAC[emitted_insts_def] >>
     pop_assum (fn th => PURE_REWRITE_TAC[th]) >> simp[DROP_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa sr ++ emitted_insts sr sb` by
    (irule emitted_insts_append >> simp[]) >>
  `t = u` by metis_tac[run_inst_seq_append,exec_result_11] >>
  qpat_x_assum `t = u` SUBST_ALL_TAC >>
  `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sr sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `!x. x IN tf'.t_mem <=>
      if w2n (a + n2w off) <= x /\ x < w2n (a + n2w off) + 32
      then w2n (b + n2w off) + (x - w2n (a + n2w off)) IN tn.t_mem
      else x IN tn.t_mem` by
    (ASM_REWRITE_TAC[exprPtrCtorCodeLoadTheory.store_word_taint_pointwise]) >>
  qexistsl_tac [`Gf'`,`tf'`] >> fs[] >> rpt conj_tac
  >- (irule instSeqComposePtrTheory.inst_seq_ptr_uniform_append >>
      conj_tac >- (qexistsl [`Gf`,`r`,`tf`] >> simp[]) >>
      fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[is_terminator_def])
  >> metis_tac[]
QED

(* The destination interval is below the entire live source window;
   previous ISTOREs therefore do not change a later MLOAD's taints. *)
Theorem tuple_immutable_copy_range_segment[local]:
  !n j sa sb s G tn.
  compile_imm_store_words imm (Var root) (Lit a) n j sa = ((),sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME b /\
  ptr_covers G tn root s capacity /\
  w2n a + j + 32*n <= lo /\ lo <= w2n b /\
  j + 32*n <= capacity /\ w2n b + capacity < dimword (:256) /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tf u.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) (emitted_insts sa sb) /\
    (!x. x IN tf.t_mem <=>
      if w2n a + j <= x /\ x < w2n a + j + 32*n
      then w2n b + (x - w2n a) IN tn.t_mem else x IN tn.t_mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p len. not_fresh_at sa p /\ ptr_covers G tn p s len ==>
      ptr_covers Gf tf p u len)
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_imm_store_words_def,comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl [`G`,`tn`,`s`] >>
      simp[emitted_insts_def,run_inst_seq_def,inst_seq_ptr_def,same_blocks_def]) >>
  simp[immutable_store_suc,comp_ignore_bind_def,immutable_comp_bind_cases] >>
  strip_tac >>
  rename1 `immutable_store_one imm (Var root) (Lit a) j sa = ((),sm)` >>
  `w2n (a + n2w j) = w2n a + j /\ w2n (b + n2w j) = w2n b + j` by
    (Cases_on `a` >> Cases_on `b` >> fs[wordsTheory.word_add_n2w,MULT_SUC]) >>
  `j + 32 <= capacity /\ w2n b + j < dimword (:256) /\
   w2n (a + n2w j) + 32 <= lo` by fs[MULT_SUC] >>
  drule_all tuple_immutable_copy_one_segment >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `not_fresh_at sm root /\ lookup_var root u = SOME b /\
   ptr_covers Gf tf root u capacity` by metis_tac[] >>
  `u.vs_labels = s.vs_labels` by fs[venom_state_component_equality] >>
  `!base. imm = SOME base ==> eval_operand base u = SOME 0w /\
      copy_old_operand sm base /\ op_taint tf base = {} /\ op_prov Gf base = NONE` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> rpt conj_tac
     >- metis_tac[ctorAbiActualObservationsTheory.ctor_actual_old_operand,copy_old_operand_def]
     >- (irule copy_old_operand_mono >> metis_tac[])
     >- metis_tac[emittedSeqComposePtrTheory.old_operand_taint_frame,copy_old_operand_def]
     >> metis_tac[exprPtrCtorCodeLoadTheory.old_operand_prov_frame]) >>
  `w2n a + (j + 32) + 32*n <= lo /\ j + 32 + 32*n <= capacity` by fs[MULT_SUC] >>
  qpat_x_assum `!j sa sb s G tn. _`
    (qspecl_then [`j+32`,`sm`,`sb`,`u`,`Gf`,`tf`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) u = OK v` >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qexistsl [`Gf'`,`tf'`,`v`] >> rpt conj_tac
  >- metis_tac[run_inst_seq_append]
  >- fs[APPEND_ASSOC]
  >- fs[same_blocks_def]
  >- decide_tac
  >- (simp[] >> irule instSeqComposePtrTheory.inst_seq_ptr_uniform_append >>
      conj_tac >- (qexistsl [`Gf`,`u`,`tf`] >> simp[]) >>
      fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> fs[is_terminator_def])
  >- fs[EVERY_APPEND]
  >- (qspecl_then [`w2n b`,`w2n a`,`j`,`n`,`tn.t_mem`,`tf.t_mem`,`tf'.t_mem`]
        mp_tac exprPtrCtorCodeLoadTheory.copy_word_taint_compose >>
      impl_tac
      >- (rpt conj_tac
          >- (disj2_tac >> fs[MULT_SUC])
          >- (qpat_assum `!x. x IN tf.t_mem <=> _` mp_tac >> simp[])
          >> first_assum ACCEPT_TAC) >> simp[])
  >> metis_tac[]
QED

Theorem tuple_immutable_copy_range_path[local]:
  compile_imm_store_words imm (Var root) (Lit (n2w off)) n 0 sa = ((),sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME (n2w a) /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  off + 32*n <= lo /\ lo <= a /\ lo <= s.vs_alloca_next /\
  ptr_covers G tn root s capacity /\ 32*n <= capacity /\
  a + capacity < dimword (:256) /\ a + 32*n <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) /\ k <= 32*n /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gf tf.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    mem_bytes_at off k u.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!p len. p+len <= off \/ off+32*n <= p ==>
      mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory) /\
    (!x. x IN tf.t_mem <=>
       if off <= x /\ x < off+32*n then a+(x-off) IN tn.t_mem else x IN tn.t_mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p len. not_fresh_at sa p /\ ptr_covers G tn p s len ==>
       ptr_covers Gf tf p u len)
Proof
  strip_tac >>
  `off < dimword (:256) /\ a < dimword (:256) /\ a+k < dimword (:256) /\
   off+32*n < dimword (:256) /\ off+32*n <= a /\ off+32*n <= s.vs_alloca_next` by
    decide_tac >>
  `eval_operand (Var root) s = SOME (n2w a) /\
   eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   copy_old_operand sa (Lit (n2w off)) /\ op_taint tn (Lit (n2w off)) = {} /\
   op_prov G (Lit (n2w off)) = NONE` by
    simp[eval_operand_def,copy_old_operand_def,ptrDisciplineTheory.op_taint_def,
         ptrDisciplineTheory.op_prov_def] >>
  `!base x. imm = SOME base /\ base = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> gvs[copy_old_operand_def] >> metis_tac[]) >>
  `!base. imm = SOME base ==> eval_operand base s = SOME 0w` by metis_tac[] >>
  `w2n (n2w a : bytes32) = a /\ w2n (n2w off : bytes32) = off` by
    simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `w2n (n2w off : bytes32) + 32*n <= lo /\ lo <= w2n (n2w a : bytes32) /\
   w2n (n2w a : bytes32) + capacity < dimword (:256)` by simp[] >>
  drule_all (SRULE [] (tuple_immutable_copy_range_segment |> Q.SPEC `n` |> Q.SPEC `0`)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `Gf` (qx_choose_then `tf` (qx_choose_then `t` strip_assume_tac)))) >>
  drule (Q.INST [`src` |-> `Var root`, `dst` |-> `Lit (n2w off)`,
               `a` |-> `a`, `b` |-> `off`, `k` |-> `k`, `s` |-> `s`,
               `func` |-> `fn`] immutable_words_old_prefix_path) >>
  disch_then (qspecl_then [`s`,`k`,`fn`,`ctx`,`a`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `t = u` by metis_tac[exec_result_11] >>
  qpat_x_assum `t = u` SUBST_ALL_TAC >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule (SRULE [] (tuple_immutable_copy_range_mem_ok |> Q.SPEC `n` |> Q.SPEC `0`)) >>
     disch_then (qspecl_then [`s`,`n2w a`] mp_tac) >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >> fs[is_terminator_def]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (`s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
       simp[venom_state_component_equality] >>
     qpat_assum `!z. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `LENGTH sa.cs_current_insts` mp_tac) >>
     simp[] >> metis_tac[venom_state_component_equality]) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> simp[] >>
  conj_tac
  >- (`lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[] >> metis_tac[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* The unstaged tuple can be a view into a live local.  Take the floor
   from spatial ownership, not from the ghost site of the loaded child. *)

Theorem tuple_immutable_rhs_floor[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  stmt_state_rel H ctx func cenv cx es s /\ dead_lo_ok H D lo cenv cx /\
  allocas_from lo s /\ expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME (TupleTV tvs) /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ 0 < val_footprint (TupleTV tvs) v ==>
  lo <= w2n w
Proof
  strip_tac >>
  drule_all exprSimHashBoundaryTheory.expr_val_at_footprint >>
  disch_then strip_assume_tac
  >- (fs[ptrDisciplineTheory.allocas_from_def] >>
      `lo <= b` by metis_tac[] >> decide_tac)
  >- (`0 < sz` by decide_tac >>
      drule_all bodyFullMemoryFramesTheory.body_full_local_region_lower_bound >>
      decide_tac) >>
  decide_tac
QED

(* Use the enclosing load window to bound the actual child address. *)

Theorem tuple_immutable_loaded_window[local]:
  i < LENGTH tvs /\ off + type_memory_size_list tvs <= capacity /\
  w2n (w:bytes32) + capacity < dimword (:256) /\
  w2n w + capacity <= t.vs_alloca_next /\ lo <= w2n w /\
  a = w2n w + off + SUM (MAP type_memory_size (TAKE i tvs)) ==>
  lo <= a /\ a + type_memory_size (EL i tvs) <= t.vs_alloca_next /\
  a + type_memory_size (EL i tvs) < dimword (:256)
Proof
  strip_tac >>
  `SUM (MAP type_memory_size (TAKE i tvs)) + type_memory_size (EL i tvs) <=
     type_memory_size_list tvs` by
    (rewrite_tac[valueEncodingProofsTheory.type_memory_size_list_sum] >>
     irule abiEncoderInputTheory.abi_encoder_prefix_sum_bound >> simp[]) >>
  decide_tac
QED

(* Both fixed-size compiler branches are the same unrolled store. *)

Theorem tuple_immutable_fixed_suffix[local]:
  ~is_bytestring_type ty /\ type_memory_size tv = 32 * type_slot_size tv /\
  0 < type_slot_size tv ==>
  compile_assign_value ce dst LocCode op F src_loc ty ty (type_memory_size tv) =
    compile_imm_store_words ce.ce_imm_alloca op dst (type_slot_size tv) 0
Proof
  strip_tac >>
  simp[stmtLoweringTheory.compile_assign_value_def, FUN_EQ_THM,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
    arithmeticTheory.DIV_NUMERAL_THM] >>
  Cases_on `type_slot_size tv <= 1`
  >- (`type_slot_size tv = SUC 0` by decide_tac >>
      qpat_assum `type_slot_size tv = SUC 0` SUBST1_TAC >>
      rewrite_tac[compile_imm_store_words_def,compile_lit_byte_offset_def] >>
      simp[compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.comp_return_def] >>
      gen_tac >> pairarg_tac >> simp[] >>
      Cases_on `compile_imm_store_word ce.ce_imm_alloca dst loaded cs'` >> simp[]) >>
  `~(32 * type_slot_size tv <= 32)` by decide_tac >> simp[]
QED

(* A typed slot below lo has the same byte window in the section prefix. *)
Theorem tuple_immutable_prefix_interior_dead[local]:
  off + type_memory_size tv <= lo /\ well_formed_type_value tv /\
  value_has_type tv vi /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tv vi off m) /\
  off <= i /\ i < off + type_memory_size tv /\ i IN dirty ==>
  mem_dead_bytes (mem_bytes_at 0 lo mem) off tv i
Proof
  strip_tac >>
  `mem_bytes_at off (type_memory_size tv) (mem_bytes_at 0 lo mem) =
   mem_bytes_at off (type_memory_size tv) mem` by
    (simp[LIST_EQ_REWRITE,valueEncodingPropsTheory.LENGTH_mem_bytes_at] >>
     rpt strip_tac >>
     `off + x < lo` by decide_tac >>
     simp[valueEncodingProofsTheory.EL_mem_bytes_at,
          valueEncodingPropsTheory.LENGTH_mem_bytes_at]) >>
  `val_wf tv vi` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!m. mem_agree_outside dirty (mem_bytes_at 0 lo mem) m ==>
       val_in_memory tv vi off m` by
    (rpt strip_tac >> irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
     simp[] >> qexistsl_tac [`mem`,`mem_bytes_at 0 lo mem`,`type_memory_size tv`,
                             `off`,`dirty`,`dirty`] >>
     simp[exprSimPropsTheory.val_footprint_le]) >>
  `!j. j < type_memory_size tv /\ off+j IN dirty ==>
       mem_dead_bytes (mem_bytes_at 0 lo mem) off tv (off+j)` by
    (mp_tac (Q.SPECL [`tv`,`vi`,`off`,`mem_bytes_at 0 lo mem`,`dirty`]
       immutableRepSensitivityTheory.body_assign_immutable_rep_sensitivity) >> simp[]) >>
  `i - off < type_memory_size tv /\ off + (i - off) = i` by decide_tac >>
  first_x_assum (qspec_then `i - off` mp_tac) >> simp[]
QED

(* Statement transport and the copied representation use the very endpoint
   selected by the annotated fixed-size suffix, before any deadness proof. *)

Theorem tuple_immutable_fixed_stmt_path[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode (Var root) F NONE ty ty
    (type_memory_bytes ce ty) sa = ((),sb) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  ~is_bytestring_type ty /\ 0 < type_slot_size tv /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env st /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv vi /\
  write_place cx (ImmutablePlace ce.ce_module id []) vi st = (INL (),fin) /\
  not_fresh_at sa root /\ lookup_var root s = SOME (n2w a) /\
  (!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  off + type_memory_size tv <= lo /\ lo <= a /\ lo <= s.vs_alloca_next /\
  ptr_covers G tn root s (type_memory_size tv) /\
  a + type_memory_size tv < dimword (:256) /\
  a + type_memory_size tv <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv vi a mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~block_is_terminated sb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!H : (bool # 'b word # type_value) list # num list.
      stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
      stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!(H : (bool # 'b word # type_value) list # num list) D.
      stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
      ghost_inv_at D lo d ce cx st G tn s ==> ghost_inv_at D lo d ce cx fin Gf tf q) /\
    (!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==> val_in_memory tv vi off mem) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_fmp = s.vs_fmp /\ q.vs_call_ctx = s.vs_call_ctx /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p q n) /\
    (!p n. regions_disjoint p n off (type_memory_size tv) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!x. x IN tf.t_mem <=>
      if off <= x /\ x < off + type_memory_size tv then a+(x-off) IN tn.t_mem
      else x IN tn.t_mem)
Proof
  strip_tac >>
  `type_memory_size tv = 32 * type_slot_size tv` by simp[type_memory_size_slots] >>
  `compile_imm_store_words ce.ce_imm_alloca (Var root) (Lit (n2w off))
       (type_slot_size tv) 0 sa = ((),sb)` by
    metis_tac[tuple_immutable_fixed_suffix] >>
  drule (Q.INST [`k` |-> `type_memory_size tv`, `capacity` |-> `type_memory_size tv`]
      tuple_immutable_copy_range_path) >>
  disch_then (qspecl_then [`tv`,`tn`,`s`,`lo`,`fn`,`explicit`,`ctx`,`a`,`PG`,`G`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH u.vs_memory /\ sb.cs_current_bb = sa.cs_current_bb` by
    (simp[same_blocks_def] >> metis_tac[run_inst_seq_memory_length,same_blocks_def]) >>
  qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `!p n. regions_disjoint p n off (type_memory_size tv) ==>
    mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt gen_tac >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_assum `!p len. _ \/ _ ==> mem_bytes_at p len u.vs_memory = _`
       (qspecl_then [`p`,`n`] mp_tac) >> simp[]) >>
  `val_wf tv vi` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==> val_in_memory tv vi off mem` by
    (rpt strip_tac >> irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
     simp[] >> qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`type_memory_size tv`,`a`,`tn.t_mem`,`tf.t_mem`] >>
     simp[exprSimPropsTheory.val_footprint_le] >> rpt strip_tac >>
     qpat_assum `!x. x IN tf.t_mem <=> _` (qspec_then `off+i` mp_tac) >>
     simp[] >> decide_tac) >>
  `val_in_memory tv vi off u.vs_memory` by metis_tac[mem_agree_outside_def] >>
  `immutable_value_admissible tv vi` by metis_tac[evaluated_immutable_admissible] >>
  `immutable_value_bytes_rel tv vi (mem_bytes_at off (type_memory_size tv) u.vs_memory)` by
    metis_tac[immutable_memory_bytes,evaluate_type_well_formed_type_value] >>
  `!i. off <= i /\ i < off + type_memory_size tv /\ i IN tf.t_mem ==>
      mem_dead_bytes (mem_bytes_at 0 lo u.vs_memory) off tv i` by
    (`well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
     rpt strip_tac >> irule tuple_immutable_prefix_interior_dead >>
     simp[] >> qexistsl_tac [`tf.t_mem`,`vi`] >> simp[]) >>
  `ce.ce_module = NONE` by fs[body_inv_def,cenv_module_pins_def] >>
  `fin.scopes = st.scopes` by
    (drule vyperPlaceFramesTheory.write_immutable_place_frame >>
     disch_then strip_assume_tac >> simp[]) >>
  `lo <= u.vs_alloca_next` by simp[] >>
  `!i. ~(off <= i /\ i < off + type_memory_size tv) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> first_x_assum (irule o SIMP_RULE std_ss
      [loweringStateRelDefsTheory.regions_disjoint_def]) >> decide_tac) >>
  `!i. ~(off <= i /\ i < off + type_memory_size tv) /\ i IN tf.t_mem ==> i IN tn.t_mem` by (simp[] >> (metis_tac[])) >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tf`] >>
  simp[ptr_covers_def,lookup_var_def,ptrDisciplineTheory.allocas_from_def,
       ptrDisciplineTheory.allocas_below_fmp_def,ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
  conj_tac
  >- (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
      goal_assum (drule_at Any)) >>
  conj_tac
  >- (rpt strip_tac >> irule immutable_assign_suffix_stmt_post >>
      simp[GSYM lookup_var_def,venom_state_component_equality] >>
      qexistsl_tac [`env`,`id`,`tv`,`ty`,`off`,`vi`] >> fs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `stmt_state_rel H ctx fn ce cx st s`
        (mp_then Any mp_tac tuple_immutable_suffix_ghost_post) >>
      disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
      disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
      disch_then irule >>
      qpat_x_assum `!x. x IN tf.t_mem <=> _` kall_tac >>
      simp[] >> conj_tac
      >- (qexistsl_tac [`id`,`off`,`tv`,`ty`] >> gs[] >> metis_tac[]) >>
      qexists_tac `sa` >> simp[]) >>
  qx_gen_tac `x` >> strip_tac >>
  qpat_assum `!p. not_fresh_at sa p ==> lookup_var p u = _ /\ _`
    (drule_then (ACCEPT_TAC o CONJUNCT1) o
     REWRITE_RULE [lookup_var_def] o Q.SPEC `x`)
QED

(* Recover the compiler cursors of the non-bytes normalization, rewriting
   only its last segment as the equal-layout immutable suffix. *)
Theorem tuple_immutable_normalized_cursors[local]:
  compile_assign_value ce dst LocCode src F NONE dty sty n sa = ((),sb) /\
  dty <> sty /\ ~is_bytestring_type dty /\
  fn_has_code sa sb fn ==>
  ?buf sm su.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),su) /\
    compile_assign_value ce dst LocCode buf.buf_operand F NONE dty dty n su = ((),sb) /\
    fn_has_code sa sm fn /\ fn_has_code sm su fn /\ fn_has_code su sb fn /\
    ci_mono sm su
Proof
  strip_tac >> gvs[] >>
  drule_all immutableAssignStoreTheory.immutable_assign_normalized_compile >> simp[] >>
  disch_then (qx_choose_then `buf` (qx_choose_then `sm` (qx_choose_then `su` strip_assume_tac))) >>
  `compile_assign_value ce dst LocCode buf.buf_operand F NONE dty dty n su = ((),sb)` by
    (simp[stmtLoweringTheory.compile_assign_value_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_return_def]) >>
  `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm su` by
    (qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (fn th =>
       mp_tac (SRULE [th] (Q.SPECL [`ce`,`buf.buf_operand`,`dty`,`src`,`sty`,`sm`]
         (cj 1 externalEntryShapeTheory.typed_memory_family_labels)))) >> simp[]) >>
  `cs_extends su sb` by
    (Cases_on `n <= 32` >> fs[]
     >- (qpat_assum `(do loaded <- _; _ od) _ = _`
           (strip_assume_tac o REWRITE_RULE [immutable_comp_bind_cases]) >>
         drule exprSimAccountsTheory.emit_op_extends_next_var >> strip_tac >>
         `cs_extends st1 sb` by
           metis_tac[externalEntryShapeTheory.compile_imm_store_word_labels,pairTheory.SND] >>
         metis_tac[cs_extends_trans]) >>
     metis_tac[externalEntryShapeTheory.compile_imm_store_words_labels,pairTheory.SND]) >>
  qexistsl_tac [`buf`,`sm`,`su`] >> simp[] >>
  metis_tac[fn_has_code_split,cs_extends_trans,cj 1 ci_mono_typed_memory_family,pairTheory.SND]
QED

(* The allocation packet transports the horizon type selected at its input. *)
Theorem tuple_immutable_alloc_horizon_bridge[local]:
  stmt_state_rel (H0 : (bool # 'a word # type_value) list # num list) ctx fn ce cx st s /\
  (if (?Ha : (bool # 'b word # type_value) list # num list.
         stmt_state_rel Ha ctx fn ce cx st s)
   then (!H : (bool # 'b word # type_value) list # num list.
           stmt_state_rel H ctx fn ce cx st s ==> stmt_state_rel H ctx fn ce cx st u)
   else (!K : (bool # 'a word # type_value) list # num list.
           stmt_state_rel K ctx fn ce cx st s ==> stmt_state_rel K ctx fn ce cx st u)) ==>
  alloca_inv u /\
  (!H : (bool # 'b word # type_value) list # num list.
    stmt_state_rel H ctx fn ce cx st s ==> stmt_state_rel H ctx fn ce cx st u)
Proof
  IF_CASES_TAC >> simp[] >>
  metis_tac[bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv]
QED

Theorem tuple_immutable_normalized_prefix[local]:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dty (Var xs) sty sm = ((),su) /\
  fn_has_code sa sm fn /\ fn_has_code sm su fn /\ fn_inst_ids_distinct fn /\
  ci_mono sm su /\ local_ptrs_reserved ce sa /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  stmt_state_rel H0 ctx fn ce cx st s /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  p <= w2n sw /\ w2n sw + type_memory_size stv <= p+k /\
  (?a len. a <= p /\ p+k <= a+len /\
    ((?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len)) \/
     (?name. local_region ce st.scopes s name a len))) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t root b Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. stmt_state_rel H ctx fn ce cx st s ==> stmt_state_rel H ctx fn ce cx st t) /\
    (!D d. ghost_inv_at D lo d ce cx st G tn s ==> ghost_inv_at D lo d ce cx st Gf tf t) /\
    ~t.vs_halted /\ t.vs_current_bb = su.cs_current_bb /\ t.vs_inst_idx = LENGTH su.cs_current_insts /\
    local_ptrs_reserved ce su /\
    buf.buf_operand = Var root /\ not_fresh_at su root /\
    lookup_var root t = SOME (n2w b) /\ ptr_covers Gf tf root t (type_memory_size dtv) /\
    lo <= b /\ b + type_memory_size dtv < dimword (:256) /\
    b + type_memory_size dtv <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory dtv v b mem) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> not_fresh_at su x /\ lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x t cap) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory /\
    (!i. p <= i /\ i < p+k ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
      a <= i /\ i < a+sz /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
    alloca_frame ce st sa s ce st t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?Ha : (bool # 'b word # type_value) list # num list.
                stmt_state_rel Ha ctx fn ce cx st s`
  >- (drule_all bodyFullMemoryFramesTheory.body_full_alloc_buffer_path >>
      disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
        (qx_choose_then `u` (qx_choose_then `root` (qx_choose_then `b`
          (qx_choose_then `G1` (qx_choose_then `tn1`
            (fn packet => mk_asm "alloc_state" (cj 3 packet) >>
                          map_every assume_tac (CONJUNCTS packet)))))))) >>
      `alloca_inv u /\
       (!H : (bool # 'b word # type_value) list # num list.
         stmt_state_rel H ctx fn ce cx st s ==> stmt_state_rel H ctx fn ce cx st u)` by
        (match_mp_tac tuple_immutable_alloc_horizon_bridge >>
         asm_rewrite_tac[]) >>
      suspend "copy") >>
  drule_all (INST_TYPE [beta |-> alpha] bodyFullMemoryFramesTheory.body_full_alloc_buffer_path) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choose_then `u` (qx_choose_then `root` (qx_choose_then `b`
      (qx_choose_then `G1` (qx_choose_then `tn1`
        (fn packet => mk_asm "alloc_state" (cj 3 packet) >>
                      map_every assume_tac (CONJUNCTS packet)))))))) >>
  `alloca_inv u /\
   (!H : (bool # 'b word # type_value) list # num list.
     stmt_state_rel H ctx fn ce cx st s ==> stmt_state_rel H ctx fn ce cx st u)` by
    (match_mp_tac tuple_immutable_alloc_horizon_bridge >>
     asm_rewrite_tac[]) >>
  suspend "copy"
QED

Resume tuple_immutable_normalized_prefix[copy]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `n = type_memory_size dtv` >>
  `!name a len. local_region ce st.scopes u name a len <=>
     local_region ce st.scopes s name a len` by
    (irule exprSimPtrLiteralBufferTheory.literal_ptr_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  (Q_TAC (C SUBGOAL_THEN assume_tac) `p+k <= b \/ b+n <= p` >- suspend "separation") >>
  `!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem` by suspend "source" >>
  `s.vs_alloca_next <= u.vs_alloca_next /\ b+n <= u.vs_alloca_next` by suspend "frontier" >>
  `b < dimword (:256) /\ w2n sw + type_memory_size stv <= u.vs_alloca_next` by decide_tac >>
  (Q_TAC (C SUBGOAL_THEN assume_tac)
     `w2n sw + type_memory_size stv <= b \/ b+n <= w2n sw` >- decide_tac) >>
  `not_fresh_at sm xs /\ lookup_var xs u = SOME sw /\
   ptr_covers G1 tn1 xs u (type_memory_size stv)` by metis_tac[] >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  `val_wf stv v /\ val_wf dtv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `compile_store_memory_typed ce (Var root) dty (Var xs) sty sm = ((),su)` by metis_tac[] >>
  qunabbrev_tac `n` >>
  drule typedCopyOriginPtrTheory.compile_store_memory_typed_origin_ptr_path >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var root u = _`)) >>
  disch_then (drule_at (Pat `lookup_var xs u = _`)) >>
  disch_then (drule_at (Pat `ptr_covers G1 tn1 root u _`)) >>
  disch_then (qspecl_then [`v`,`lo`,`fn`,`explicit`,`dtv`,`ctx`,`PG`] mp_tac) >>
  qpat_assum `w2n ((n2w b):bytes32) = b` (fn eq =>
    pure_rewrite_tac [eq]) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then strip_assume_tac >>
  rename1 `typed_copy_state_frame sm b _ u t` >>
  rename1 `gas_origin_ptr_path _ (u,G1,tn1) [] (OK t,Gf,tf)` >>
  qabbrev_tac `n = type_memory_size dtv` >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\
       FLOOKUP Gf x = FLOOKUP G1 x /\ op_taint tf (Var x) = op_taint tn1 (Var x)` by
    (rpt strip_tac >> qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
     simp[]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_fmp = u.vs_fmp /\ t.vs_initial_fmp = u.vs_initial_fmp /\
   t.vs_call_ctx = u.vs_call_ctx /\ t.vs_accounts = u.vs_accounts /\
   t.vs_transient = u.vs_transient /\ t.vs_immutables = u.vs_immutables /\
   (!a len. a+len <= b \/ b+n <= a ==> mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory)` by
    ((qpat_assum `typed_copy_state_frame _ _ _ _ _`
      (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
         typedMemoryCopyTheory.typed_copy_frame_def,venomStateTheory.venom_state_component_equality]) >> simp[] >> (gvs[]))) >>
  `allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (gns[ptrDisciplineTheory.allocas_from_def,ptrDisciplineTheory.allocas_below_fmp_def] >>
     metis_tac[]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at su x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `local_ptrs_reserved ce su` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,exprLoweringPropsTheory.ci_mono_def] >>
  `!x cap. not_fresh_at sm x /\ ptr_covers G1 tn1 x u cap ==> ptr_covers Gf tf x t cap` by
    (rpt strip_tac >> irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G1`,`u`,`tn1`] >> simp[]) >>
  qexistsl_tac [`t`,`root`,`b`,`Gf`,`tf`] >> simp[] >>
  (conj_tac >- (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
    qexistsl_tac [`G1`,`u`,`tn1`] >> simp[])) >>
  (conj_tac >- suspend "state") >>
  (conj_tac >- suspend "ghost") >>
  suspend "post"
QED

Resume tuple_immutable_normalized_prefix[separation]:
  markerLib.RESUME_TAC >>
  (qpat_x_assum `?a len. _` strip_assume_tac
   >- (qpat_assum `!aid a len. _` (qspecl_then [`aid`,`a`,`len`] mp_tac) >>
       simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
   qpat_assum `!name a len. local_region ce st.scopes u name a len ==> _`
     (qspecl_then [`name`,`a`,`len`] mp_tac) >>
   simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
QED

Resume tuple_immutable_normalized_prefix[source]:
  markerLib.RESUME_TAC >>
  gen_tac >> disch_tac >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  (conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  qexistsl_tac [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,`tn1.t_mem`,
                `{i | b <= i /\ i < b+n}`] >>
  simp[] >>
  `val_footprint stv v <= type_memory_size stv` by
    metis_tac[exprSimPropsTheory.val_footprint_le,valueEncodingTypingTheory.value_has_type_val_wf] >>
  rpt strip_tac >> decide_tac
QED

Resume tuple_immutable_normalized_prefix[frontier]:
  markerLib.RESUME_TAC >>
  (conj_tac
   >- (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
         (qspec_then `cx_dead H0 cx` mp_tac) >>
       disch_then (strip_assume_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
       drule fragGasOriginTheory.gas_origin_path_erase >> strip_tac >>
       drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
       drule bodyMemBopRestWordPathTheory.rest_word_path_frontier >> simp[]) >>
   irule allocaSiteResourceTheory.alloca_site_registered_below >>
   simp[] >>
   qexists_tac `sa.cs_next_id` >> simp[])
QED

Resume tuple_immutable_normalized_prefix[state]:
  markerLib.RESUME_TAC >> qx_gen_tac `H` >> disch_tac >>
  IF (qpat_assum `~(?Ha. stmt_state_rel Ha ctx fn ce cx st s)` (K ALL_TAC))
    (qpat_x_assum `~(?Ha. stmt_state_rel Ha ctx fn ce cx st s)` mp_tac >>
     simp[] >> disch_then (qspec_then `H` mp_tac) >> simp[])
    (`stmt_state_rel H ctx fn ce cx st u` by
       (asm "alloc_state" (qspec_then `H` mp_tac) >> simp[]) >>
     drule_all actualAllocExecTheory.actual_alloc_buffer_site >> disch_tac >>
     irule placeStoreDynPrepareTheory.place_typed_copy_alloca_state_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     qexistsl_tac [`n`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
         [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[])
QED

Resume tuple_immutable_normalized_prefix[ghost]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[] >> metis_tac[]) >>
  `!name a len. local_region ce st.scopes s name a len ==> regions_disjoint b n a len`
    by metis_tac[] >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by simp[] >>
  irule bodyFullMemoryFramesTheory.body_full_memory_ghost_frame >> simp[] >>
  qexistsl_tac [`G`,`s`,`sa`,`tn`,`{i | b <= i /\ i < b+n}`] >>
  simp[] >>
  (conj_tac
   >- (map_every qx_gen_tac [`name`,`entry`,`xptr`,`sz`,`w`] >> strip_tac >>
       drule exprSimPtrLiteralBufferTheory.literal_ptr_local_footprint_exterior >>
       disch_then (qspecl_then [`n`,`b`,`name`,`entry`,`xptr`,`sz`,`w`] mp_tac) >>
       simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[])) >>
  (conj_tac
   >- (qx_gen_tac `i` >> strip_tac >>
       `i+1 <= b \/ b+n <= i` by decide_tac >> simp[])) >>
  qx_gen_tac `i` >> strip_tac >>
  `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]
QED

Resume tuple_immutable_normalized_prefix[post]:
  markerLib.RESUME_TAC >>
  (conj_tac >- (qpat_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _`
                  (qspecl_then [`p`,`k`] mp_tac) >> simp[])) >>
  (conj_tac >-
    (rpt strip_tac >>
     `~(b <= i /\ i < b+n)` by
       (qpat_assum `!aid a len. aid < sa.cs_next_id /\ _ ==> regions_disjoint b n a len`
          (qspecl_then [`aid`,`a`,`sz`] mp_tac) >>
        simp[regions_disjoint_def] >> decide_tac) >>
     metis_tac[])) >>
  `!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
     aid < sa.cs_next_id ==> mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by
    (map_every qx_gen_tac [`aid`,`off`,`sz`] >> strip_tac >>
     qpat_assum `!aid a len. aid < sa.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disch_tac >>
     qpat_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _`
       (qspecl_then [`off`,`sz`] mp_tac) >> simp[] >> decide_tac) >>
  drule stmtSimDefsTheory.alloca_frame_of_mem_frame >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Finalise tuple_immutable_normalized_prefix

(* The fixed store consumes the actual normalized buffer, while pending
   members keep their original tuple window. *)
Theorem tuple_immutable_normalized_fixed_joint[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode (Var xs) F NONE dty sty
    (type_memory_bytes ce dty) sa = ((),sb) /\
  dty <> sty /\ ~is_bytestring_type dty /\ 0 < type_slot_size dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~block_is_terminated sb /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env st /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME dty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME dty /\
  local_ptrs_reserved ce sa /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  write_place cx (ImmutablePlace ce.ce_module id []) v st = (INL (),fin) /\
  stmt_state_rel (H0 : (bool # 'a word # type_value) list # num list) ctx fn ce cx st s /\
  not_fresh_at sa xs /\ lookup_var xs s = SOME sw /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  off + type_memory_size dtv <= lo /\ lo <= p /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  p <= w2n sw /\ w2n sw + type_memory_size stv <= p+k /\
  (?a len. a <= p /\ p+k <= a+len /\
    ((?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len)) \/
     (?name. local_region ce st.scopes s name a len))) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q Gq tq.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gq,tq)) /\
    (!H : (bool # 'b word # type_value) list # num list.
      stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
      stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!(H : (bool # 'b word # type_value) list # num list) D.
      stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
      ghost_inv_at D lo d ce cx st G tn s ==> ghost_inv_at D lo d ce cx fin Gq tq q) /\
    (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==> val_in_memory dtv v off mem) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s.vs_alloca_next <= q.vs_alloca_next /\
    q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP q.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gq x = FLOOKUP G x /\ op_taint tq (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==> ptr_covers Gq tq x q cap) /\
    tq.t_stor = tn.t_stor /\ tq.t_trans = tn.t_trans /\
    mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory /\
    (!i. p <= i /\ i < p+k ==> (i IN tq.t_mem <=> i IN tn.t_mem)) /\
    (!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
      a <= i /\ i < a+sz /\ i IN tq.t_mem ==> i IN tn.t_mem) /\
    alloca_frame ce st sa s ce fin q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_immutable_normalized_cursors >>
  disch_then (qx_choose_then `buf` (qx_choose_then `sm` (qx_choose_then `su`
    (map_every assume_tac o CONJUNCTS)))) >>
  qpat_assum `type_memory_bytes ce dty = _` (fn eq =>
    qpat_x_assum `compile_alloc_buffer _ sa = _` (assume_tac o REWRITE_RULE [eq])) >>
  `ci_mono sa sm` by
    (qpat_assum `compile_alloc_buffer _ sa = _` (fn th =>
       mp_tac (Q.SPECL [`type_memory_size dtv`,`sa`]
         exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >> simp[th])) >>
  `sa.cs_next_id <= su.cs_next_id` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  (Cases_on `?Ha : (bool # 'b word # type_value) list # num list.
                   stmt_state_rel Ha ctx fn ce cx st s`
   >- (pop_assum (qx_choose_then `Ha` assume_tac) >>
       qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` kall_tac >>
       drule_all (INST_TYPE [alpha |-> beta] tuple_immutable_normalized_prefix) >>
       disch_then (qspecl_then [`explicit`,`PG`]
         (qx_choose_then `t` (qx_choose_then `root` (qx_choose_then `b`
           (qx_choose_then `G1` (qx_choose_then `tn1`
             (map_every assume_tac o CONJUNCTS))))))) >>
       `stmt_state_rel Ha ctx fn ce cx st t` by
         (qpat_assum `!H. stmt_state_rel H ctx fn ce cx st s ==> _`
            (drule_then ACCEPT_TAC)) >>
       suspend "suffix") >>
   drule_all (INST_TYPE [beta |-> alpha] tuple_immutable_normalized_prefix) >>
   disch_then (qspecl_then [`explicit`,`PG`]
     (qx_choose_then `t` (qx_choose_then `root` (qx_choose_then `b`
       (qx_choose_then `G1` (qx_choose_then `tn1`
         (map_every assume_tac o CONJUNCTS))))))) >>
   `stmt_state_rel H0 ctx fn ce cx st t` by
     (qpat_x_assum `!H. stmt_state_rel H ctx fn ce cx st s ==> _`
        (drule_then ACCEPT_TAC)) >>
   `!(H : (bool # 'b word # type_value) list # num list).
       stmt_state_rel H ctx fn ce cx st s ==> stmt_state_rel H ctx fn ce cx st t` by
     (qx_gen_tac `Hb` >> disch_tac >>
      `?Ha : (bool # 'b word # type_value) list # num list.
         stmt_state_rel Ha ctx fn ce cx st s` by (qexists_tac `Hb` >> simp[]) >>
      gvs[])) >>
  suspend "suffix"
QED

Resume tuple_immutable_normalized_fixed_joint[suffix]:
  markerLib.RESUME_TAC >>
  `alloca_room ctx fn t` by
    (qpat_assum `stmt_state_rel _ ctx fn ce cx st t`
       (mp_then Any ACCEPT_TAC stateRelProjTheory.stmt_state_rel_alloca_room)) >>
  `t.vs_alloca_next < dimword (:256)` by
    (drule_then ACCEPT_TAC exprLoweringPropsTheory.alloca_room_next_lt) >>
  `lo <= t.vs_alloca_next` by
    (irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >> simp[]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at su x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at su x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,G1,tn1)`
       (qspec_then `<| d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {} |>` assume_tac) >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     disch_then (mp_then Any ACCEPT_TAC stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_labels)) >>
  `!base. ce.ce_imm_alloca = SOME base ==> eval_operand base t = SOME 0w /\
    copy_old_operand su base /\ op_taint tn1 base = {} /\ op_prov G1 base = NONE` by
    (qx_gen_tac `base_op` >> disch_tac >>
     qpat_assum `!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     Cases_on `base_op` >> gvs[eval_operand_def,copy_old_operand_def,op_taint_def,op_prov_def]) >>
  qpat_assum `buf.buf_operand = Var root` (fn eq =>
    qpat_x_assum `compile_assign_value _ _ _ buf.buf_operand _ _ _ _ _ su = _`
      (assume_tac o REWRITE_RULE [eq])) >>
  drule_all (INST_TYPE [alpha |-> beta] tuple_immutable_fixed_stmt_path) >>
  disch_then (qspecl_then [`lctx`,`explicit`,`d`,`PG`]
    (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tq`
      (map_every assume_tac o CONJUNCTS))))) >>
  qexistsl_tac [`q`,`Gq`,`tq`] >>
  (conj_tac >- (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
    qexistsl_tac [`G1`,`t`,`tn1`] >> simp[])) >>
  (conj_tac >- suspend "stmt_post") >>
  (conj_tac >- suspend "ghost_post") >>
  suspend "frames"
QED

Resume tuple_immutable_normalized_fixed_joint[stmt_post]:
  markerLib.RESUME_TAC >>
  rpt strip_tac >>
  `stmt_state_rel H ctx fn ce cx st t` by simp[] >>
  irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
  qexistsl_tac [`st`,`t`,`su`] >> simp[]
QED

Resume tuple_immutable_normalized_fixed_joint[ghost_post]:
  markerLib.RESUME_TAC >>
  qx_gen_tac `Hb` >> qx_gen_tac `D` >> strip_tac >>
  `stmt_state_rel Hb ctx fn ce cx st t` by simp[] >>
  qpat_assum `!H D. _ ==> ghost_inv_at D lo d ce cx fin Gq tq q`
    (qspecl_then [`Hb`,`D`] mp_tac) >> simp[]
QED

Resume tuple_immutable_normalized_fixed_joint[frames]:
  markerLib.RESUME_TAC >>
  `regions_disjoint p k off (type_memory_size dtv)` by
    (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at p k q.vs_memory = mem_bytes_at p k t.vs_memory` by simp[] >>
  `!i. p <= i /\ i < p+k ==> (i IN tq.t_mem <=> i IN tn1.t_mem)` by
    (qx_gen_tac `i` >> strip_tac >>
     `~(i < off + type_memory_size dtv)` by decide_tac >> simp[]) >>
  `!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
     a <= i /\ i < a+sz /\ i IN tq.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `lo <= a` by
       (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
        disch_then (qspecl_then [`aid`,`a`,`sz`] mp_tac) >> simp[]) >>
     `~(i < off + type_memory_size dtv)` by decide_tac >>
     `i IN tn1.t_mem` by
       (qpat_assum `!x. x IN tq.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!aid a sz i. _ ==> i IN tn.t_mem`
       (qspecl_then [`aid`,`a`,`sz`,`i`] mp_tac) >> simp[]) >>
  `fin.scopes = st.scopes` by
    (drule_then ACCEPT_TAC vyperPlaceFramesTheory.write_immutable_place_scopes) >>
  `!x. not_fresh_at su x ==> lookup_var x q = lookup_var x t` by simp[] >>
  `alloca_frame ce st su t ce fin q` by
    (qpat_assum `stmt_state_rel _ ctx fn ce cx st t`
       (mp_then Any mp_tac immutableAssignComposeTheory.immutable_assign_suffix_alloca_frame) >>
     disch_then (drule_at (Pat `FLOOKUP ce.ce_module_vars _ = SOME (ImmutableLoc off)`)) >>
     disch_then (drule_all_then ACCEPT_TAC)) >>
  qpat_x_assum `!x. x IN tq.t_mem <=> _` kall_tac >>
  simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  irule stmtSimDefsTheory.alloca_frame_trans >>
  qexistsl_tac [`ce`,`st`,`t`,`su`] >> simp[]
QED

Finalise tuple_immutable_normalized_fixed_joint[local]

(* The loaded word may carry payload taint; reading does not change it in memory. *)
Theorem tuple_runtime_mload_cursor[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var p] [x]) /\
  ptr_covers G tn p s 32 /\ lookup_var p s = SOME a /\
  w2n a + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf. t = (update_var x (mload (w2n a) s) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand (Var x) t = SOME (mload (w2n a) s) /\
    op_taint tf (Var x) = mem_word_taint tn.t_mem (w2n a) /\
    op_prov Gf (Var x) = NONE /\
    (!q. q <> x ==> lookup_var q t = lookup_var q s /\
      FLOOKUP Gf q = FLOOKUP G q /\ op_taint tf (Var q) = op_taint tn (Var q)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME a` by simp[eval_operand_def] >>
  qabbrev_tac `i = mk_inst id MLOAD [Var p] [x]` >>
  qabbrev_tac `r = update_var x (mload (w2n a) s) s` >>
  qexistsl_tac [`r with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G i r`, `step_taint i s r tn`] >> simp[] >>
  conj_tac >-
    (gen_tac >> irule decoderNavigationPtrTheory.straight_line_step_origin >>
     goal_assum (drule_at Any) >>
     simp[Abbr `i`, Abbr `r`, ptr_inst_ok_mload_lo, step_MLOAD,
       below_frontier_MLOAD, inst_dload_in_section_def, mk_inst_def, is_terminator_def]) >>
  `op_prov (step_prov PG G i r) (Var x) = NONE` by
    (irule step_prov_out_none >>
     simp[Abbr `i`, mk_inst_def, out_prov_other_none]) >>
  simp[Abbr `i`, Abbr `r`,
    exprPtrCtorCodeLoadTheory.load_word_output_taint,
    exprPtrCtorCodeLoadTheory.load_word_taint_frame] >>
  simp[decoderGhostFramePtrTheory.step_prov_other_output,
    decoderGhostFramePtrTheory.step_taint_other_output, mk_inst_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Read the live bytestring header without assuming freshness of the machine. *)
Theorem tuple_runtime_header_load[local]:
  emit_op MLOAD [Var src] sa = (v,sm) /\ fn_has_code sa sm fn /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r Gf tf x. v = Var x /\ not_fresh_at sm x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK r,Gf,tf)) /\
    eval_operand v r = SOME (mload (w2n a) s) /\
    op_taint tf v = {} /\ op_prov Gf v = NONE /\
    (r with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p r = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\ ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString sa.cs_next_var)` >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MLOAD [Var src] [x])` by
    (qpat_assum `!j. j < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[] >> gvs[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all tuple_runtime_mload_cursor >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> qx_gen_tac `k` >>
     Cases_on `k < 32` >> simp[] >>
     qpat_assum `!i. w2n a <= i /\ _ ==> _` irule >> decide_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`,`x`] >>
  `!p. not_fresh_at sa p ==> p <> x` by simp[Abbr `x`, not_fresh_at_def] >>
  `v = Var x` by simp[Abbr `x`] >>
  gvs[update_var_def, not_fresh_at_def, Abbr `x`, ASCIInumbersTheory.toString_11,
      venom_state_component_equality] >> metis_tac[]
QED

(* The count and loop control consume the same clean scalar boundary. *)
Theorem tuple_runtime_scalar_cursor[local]:
  i.inst_outputs = [x] /\ augAssignPtrScalarCertificate$scalar_shape i /\
  EVERY (\p. op_prov G p = NONE /\ op_taint tn p = {}) i.inst_operands /\
  step_inst_base i s = OK (update_var x w s) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf. t = (update_var x w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand (Var x) t = SOME w /\ op_taint tf (Var x) = {} /\
    op_prov Gf (Var x) = NONE /\
    (!p. p <> x ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  qexistsl_tac [`update_var x w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G i (update_var x w s)`, `step_taint i s (update_var x w s) tn`] >>
  simp[] >> conj_tac
  >- (gen_tac >> irule decoderNavigationPtrTheory.straight_line_step_origin >>
      drule augAssignPtrScalarCertificateTheory.scalar_shape_control >> strip_tac >>
      `ptr_inst_ok D lo 0 ctx fn G tn i s` by
        (irule augAssignPtrScalarSafetyTheory.scalar_ptr_inst_ok_lo >> simp[]) >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all augAssignPtrScalarSafetyTheory.scalar_ambient_taint >> strip_tac >>
  drule_all augAssignPtrScalarRunTheory.scalar_step_prov >> strip_tac >>
  drule_all augAssignPtrScalarRunTheory.scalar_step_var_taint >> strip_tac >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem tuple_runtime_count_scalar[local]:
  emit_op opc [l;r] sa = (v,sm) /\ MEM opc [ADD; SHR] /\
  (!x. step_inst_base (mk_inst sa.cs_next_id opc [l;r] [x]) s =
       OK (update_var x w s)) /\
  op_taint tn l = {} /\ op_prov G l = NONE /\
  op_taint tn r = {} /\ op_prov G r = NONE /\
  fn_has_code sa sm fn /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf x. v = Var x /\ not_fresh_at sm x /\ ~not_fresh_at sa x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand v t = SOME w /\ op_taint tf v = {} /\ op_prov Gf v = NONE /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc [l;r] [x]` >>
  `i.inst_outputs = [x] /\ step_inst_base i s = OK (update_var x w s)` by
    simp[Abbr `i`, mk_inst_def] >>
  `augAssignPtrScalarCertificate$scalar_shape i /\
     EVERY (\p. op_prov G p = NONE /\ op_taint tn p = {}) i.inst_operands` by
    gvs[MEM, Abbr `i`, mk_inst_def, augAssignPtrScalarCertificateTheory.scalar_shape_def,
        augAssignPtrScalarCertificateTheory.scalar_binary_def] >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    gvs[MEM, Abbr `i`, mk_inst_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
        source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (qpat_assum `!j. j < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[] >> gvs[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all tuple_runtime_scalar_cursor >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`,`x`] >>
  `!p. not_fresh_at sa p ==> p <> x` by simp[Abbr `x`, not_fresh_at_def] >>
  `v = Var x` by simp[Abbr `x`] >>
  gvs[update_var_def, not_fresh_at_def, Abbr `x`, ASCIInumbersTheory.toString_11,
      venom_state_component_equality] >> metis_tac[]
QED

(* The runtime count includes the header even at length zero. *)
Theorem tuple_runtime_word_count[local]:
  compile_bytestring_word_count (Var src) sa = (cnt,sc) /\ fn_has_code sa sc fn /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n2w len /\ len + 63 < dimword (:256) /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf x. cnt = Var x /\ not_fresh_at sc x /\ ~not_fresh_at sa x /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand cnt t = SOME (n2w (1 + word_size len)) /\
    op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\ ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  Cases_on `emit_op MLOAD [Var src] sa` >> rename1 `_ = (lv,s1)` >>
  Cases_on `emit_op ADD [lv;Lit 63w] s1` >> rename1 `_ = (av,s2)` >>
  `emit_op SHR [Lit 5w;av] s2 = (cnt,sc)` by
    fs[compile_bytestring_word_count_def, comp_bind_def] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sc` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `cs_extends sa s2` by (irule cs_extends_trans >> qexists `s1` >> simp[]) >>
  `fn_has_code sa s2 fn /\ fn_has_code s2 sc fn` by
    (mp_tac (Q.SPECL [`sa`,`s2`,`sc`,`fn`] fn_has_code_split) >> simp[]) >>
  `fn_has_code sa s1 fn /\ fn_has_code s1 s2 fn` by
    (mp_tac (Q.SPECL [`sa`,`s1`,`s2`,`fn`] fn_has_code_split) >> simp[]) >>
  drule_all tuple_runtime_header_load >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r1` (qx_choose_then `G1` (qx_choose_then `t1` strip_assume_tac)))) >>
  `allocas_from lo r1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r1)` by
    (qpat_assum `(r1 with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!z. step_inst_base (mk_inst s1.cs_next_id ADD [lv;Lit 63w] [z]) r1 =
        OK (update_var z (n2w len + 63w) r1)` by
    (gen_tac >> irule step_ADD >> simp[eval_operand_def, IgnAsm `lv = Var _`]) >>
  qpat_assum `emit_op ADD _ s1 = _`
    (mp_then Any mp_tac (tuple_runtime_count_scalar |>
      Q.INST [`s` |-> `r1`, `w` |-> `n2w len + 63w`, `G` |-> `G1`, `tn` |-> `t1`])) >>
  disch_then (qspecl_then [`t1`,`r1`,`lo`,`len`,`fn`,`explicit`,`ctx`,`PG`,`G1`] mp_tac) >>
  (impl_tac >- simp[op_taint_def, op_prov_def]) >>
  disch_then (qx_choose_then `r2` (qx_choose_then `G2` (qx_choose_then `t2` strip_assume_tac))) >>
  `allocas_from lo r2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r2)` by
    (qpat_assum `(r2 with <|vs_vars := _; vs_inst_idx := _|>) = r1` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `!z. step_inst_base (mk_inst s2.cs_next_id SHR [Lit 5w;av] [z]) r2 =
        OK (update_var z ((n2w len + 63w) >>> 5) r2)` by
    (simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
          eval_operand_def, IgnAsm `av = Var _`]) >>
  qpat_assum `emit_op SHR _ s2 = _`
    (mp_then Any mp_tac (tuple_runtime_count_scalar |>
      Q.INST [`s` |-> `r2`, `w` |-> `(n2w len + 63w) >>> 5`, `G` |-> `G2`, `tn` |-> `t2`])) >>
  disch_then (qspecl_then [`t2`,`r2`,`lo`,`len`,`fn`,`explicit`,`ctx`,`PG`,`G2`] mp_tac) >>
  (impl_tac >- simp[op_taint_def, op_prov_def]) >>
  disch_then (qx_choose_then `r3` (qx_choose_then `G3` (qx_choose_then `t3` strip_assume_tac))) >>
  rename1 `cnt = Var out` >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var` by
    (qpat_assum `emit_op ADD _ s1 = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ sa = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at s1 p /\ not_fresh_at s2 p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`r3`,`G3`,`t3`,`out`] >>
  simp[bytestringCopyExecutionTheory.bytestring_word_count_exact] >>
  `~not_fresh_at sa out` by metis_tac[] >> simp[] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G1`,`r1`,`t1`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`G2`,`r2`,`t2`] >> simp[]) >>
  gvs[venom_state_component_equality]
QED

(* The EQ changes only the test register. JNZ consumes that exact result. *)
Theorem tuple_runtime_loop_test[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;cnt] [tv];
            mk_inst (id+1) JNZ [Var tv;Label done_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand (Var cv) s = SOME c /\ eval_operand cnt s = SOME n /\
  op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    t.vs_current_bb = (if c = n then done_lbl else body_lbl) /\
    t.vs_inst_idx = 0 /\ store_copy_normalize s t = s /\
    (!p. p <> tv ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `i = mk_inst id EQ [Var cv;cnt] [tv]` >>
  `step_inst_base i s = OK (update_var tv (bool_to_word (c = n)) s)` by
    (simp[Abbr `i`] >> irule step_EQ >> simp[]) >>
  `i.inst_outputs = [tv] /\ augAssignPtrScalarCertificate$scalar_shape i /\
    EVERY (\p. op_prov G p = NONE /\ op_taint tn p = {}) i.inst_operands /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`, mk_inst_def, augAssignPtrScalarCertificateTheory.scalar_shape_def,
      augAssignPtrScalarCertificateTheory.scalar_binary_def, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  drule_all tuple_runtime_scalar_cursor >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (r,Gr,tr) []
       (OK (jump_to (if c = n then done_lbl else body_lbl) r),Gr,tr)` by
    (gen_tac >>
     `bool_to_word (c = n) <> (0w:bytes32) <=> c = n` by
       (Cases_on `c = n` >> simp[bool_to_word_def]) >>
     irule (decoderNavigationPtrTheory.jnz_origin_ptr_path |>
       Q.INST [`v` |-> `bool_to_word (c = n)`] |> SRULE []) >>
     fs[update_var_def, allocas_from_def, allocas_below_fmp_def] >>
     (metis_tac[])) >>
  qexistsl_tac [`jump_to (if c = n then done_lbl else body_lbl) r`,`Gr`,`tr`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  gvs[jump_to_def, update_var_def, lookup_var_def,
      stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality]
QED

(* Entry and the back edge assign a clean counter before jumping to the header. *)
Theorem tuple_runtime_loop_assign_jump[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [op] [cv]; mk_inst (id+1) JMP [Label hdr] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand op s = SOME c /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ store_copy_normalize s t = s /\
    eval_operand (Var cv) t = SOME c /\ op_prov Gf (Var cv) = NONE /\
    op_taint tf (Var cv) = {} /\
    (!p. p <> cv ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `i = mk_inst id ASSIGN [op] [cv]` >>
  `step_inst_base i s = OK (update_var cv c s)` by
    simp[Abbr `i`, mk_inst_def, step_inst_base_opcode_eqs] >>
  `i.inst_outputs = [cv] /\ augAssignPtrScalarCertificate$scalar_shape i /\
    EVERY (\p. op_prov G p = NONE /\ op_taint tn p = {}) i.inst_operands /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`, mk_inst_def, augAssignPtrScalarCertificateTheory.scalar_shape_def,
      augAssignPtrScalarCertificateTheory.scalar_binary_def,
      augAssignPtrScalarCertificateTheory.scalar_unary_def, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  drule_all tuple_runtime_scalar_cursor >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (r,Gr,tr) []
       (OK (jump_to hdr r),Gr,tr)` by
    (gen_tac >> irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
     fs[update_var_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  qexistsl_tac [`jump_to hdr r`,`Gr`,`tr`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  gvs[jump_to_def, update_var_def, eval_operand_def, lookup_var_def,
      stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality]
QED

(* ISTORE has no register outputs and transfers the live word's taint. *)
Theorem tuple_runtime_istore_cursor[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ISTORE [arg;v] []) /\
  eval_operand arg s = SOME a /\ eval_operand v s = SOME w /\
  op_prov G arg = NONE /\ op_taint tn arg = {} /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf. t = (istore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!p. lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
      {w2n a + k | k IN op_taint tn v} /\
    tf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans
Proof
  strip_tac >>
  qabbrev_tac `i = mk_inst id ISTORE [arg;v] []` >>
  qabbrev_tac `r = istore (w2n a) w s` >>
  qexistsl_tac [`r with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G i r`,`step_taint i s r tn`] >>
  simp[Abbr `r`] >>
  conj_tac >-
    (gen_tac >>
     `ptr_inst_ok D lo 0 ctx fn G tn i s` by
       (simp[Abbr `i`] >> irule ptr_inst_ok_istore >> simp[] >> metis_tac[]) >>
     irule decoderNavigationPtrTheory.straight_line_step_origin >>
     goal_assum (drule_at Any) >>
     `w2n a + 32 <= s.vs_alloca_next` by decide_tac >>
     simp[Abbr `i`, step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          inst_dload_in_section_def, below_frontier_ISTORE] >> metis_tac[]) >>
  simp[Abbr `i`, istore_transferred_taint, lookup_var_def,
    decoderGhostFramePtrTheory.step_prov_other_output,
    decoderGhostFramePtrTheory.step_taint_other_output, mk_inst_def, istore_def, mstore_def]
QED

(* The loop's dynamic source address and its load are one live prefix. *)
Theorem tuple_runtime_source_word[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ADD [Var src;offset] [addr];
            mk_inst (id+1) MLOAD [Var addr] [x]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  eval_operand offset s = SOME (n2w off) /\ op_taint tn offset = {} /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  w2n a + off + 32 <= s.vs_alloca_next /\ src <> addr /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand (Var x) t = SOME (mload (w2n a + off) s) /\
    op_taint tf (Var x) = mem_word_taint tn.t_mem (w2n a + off) /\
    op_prov Gf (Var x) = NONE /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    t.vs_inst_idx = s.vs_inst_idx + 2 /\
    (!p. p <> addr /\ p <> x ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `i = mk_inst id ADD [Var src;offset] [addr]` >>
  qabbrev_tac `raw = update_var addr (a + n2w off) s` >>
  qabbrev_tac `r = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gr = step_prov PG G i raw` >>
  qabbrev_tac `tr = step_taint i s raw tn` >>
  `op_taint tn (Var src) = {}` by fs[ptr_covers_def] >>
  `step_inst_base i s = OK raw` by
    (simp[Abbr `i`, Abbr `raw`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK r,Gr,tr)` by
    (gen_tac >> simp[Abbr `r`, Abbr `Gr`, Abbr `tr`] >>
     irule decoderNavigationPtrTheory.straight_line_step_origin >>
     `ptr_inst_ok D lo 0 ctx fn G tn i s /\ inst_mem_below_frontier i s /\
       inst_dload_in_section i s` by
       (fs[Abbr `i`, Abbr `raw`] >>
        drule_all (typed_copy_origin_ptr_binop_checks |>
          Q.INST [`opc` |-> `ADD`] |> SRULE []) >> simp[]) >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `ptr_covers Gr tr addr r 32` by
    (simp[Abbr `r`, Abbr `Gr`, Abbr `tr`, Abbr `i`, Abbr `raw`] >>
     irule typed_copy_origin_ptr_offset_covers >> simp[] >> metis_tac[]) >>
  `w2n (a + n2w off) = w2n a + off` by
    (`off < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD]) >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb r.vs_inst_idx = SOME (mk_inst (id+1) MLOAD [Var addr] [x]) /\
   lookup_var addr r = SOME (a+n2w off) /\ ~r.vs_halted /\
   w2n (a+n2w off) + 32 <= r.vs_alloca_next /\ allocas_from lo r /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
     (simp[Abbr `r`, Abbr `raw`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all (Q.INST [`s` |-> `r`, `G` |-> `Gr`, `tn` |-> `tr`]
    tuple_runtime_mload_cursor) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `tr.t_mem = tn.t_mem /\ tr.t_stor = tn.t_stor /\
   tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
   (!p. p <> addr ==> lookup_var p r = lookup_var p s /\
     FLOOKUP Gr p = FLOOKUP G p /\ op_taint tr (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `r`, Abbr `Gr`, Abbr `tr`, Abbr `i`, Abbr `raw`,
       typed_copy_origin_ptr_binop_ghost_frame] >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  simp[] >>
  conj_tac >- simp[Abbr `r`, Abbr `raw`, update_var_def, mload_def] >>
  conj_tac >-
    simp[Abbr `r`, Abbr `raw`, update_var_def, venom_state_component_equality] >>
  simp[Abbr `r`] >> metis_tac[]
QED

(* Clean arithmetic used for destination addressing and the counter. *)
Theorem tuple_runtime_binary_prefix[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (mk_inst id opc [l;r] [x]::tail) (DROP s.vs_inst_idx bb.bb_instructions) /\
  MEM opc [ADD; MUL] /\ eval_operand l s = SOME a /\ eval_operand r s = SOME b /\
  op_prov G l = NONE /\ op_taint tn l = {} /\
  op_prov G r = NONE /\ op_taint tn r = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    eval_operand (Var x) t = SOME (if opc = ADD then a+b else a*b) /\
    op_prov Gf (Var x) = NONE /\ op_taint tf (Var x) = {} /\
    (!p. p <> Var x ==> eval_operand p t = eval_operand p s /\
      op_prov Gf p = op_prov G p /\ op_taint tf p = op_taint tn p) /\
    (!p. p <> x ==> FLOOKUP Gf p = FLOOKUP G p) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    store_copy_normalize s t = s /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ isPREFIX tail (DROP t.vs_inst_idx bb.bb_instructions) /\
    t.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted
Proof
  strip_tac >> drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `i = mk_inst id opc [l;r] [x]` >>
  qabbrev_tac `w = if opc = ADD then a+b else a*b` >>
  `step_inst_base i s = OK (update_var x w s)` by
    (fs[Abbr `i`, Abbr `w`] >> metis_tac[step_ADD, step_MUL]) >>
  `i.inst_outputs = [x] /\ augAssignPtrScalarCertificate$scalar_shape i /\
    EVERY (\p. op_prov G p = NONE /\ op_taint tn p = {}) i.inst_operands /\
    inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    gvs[Abbr `i`, mk_inst_def, augAssignPtrScalarCertificateTheory.scalar_shape_def,
      augAssignPtrScalarCertificateTheory.scalar_binary_def, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  drule_all tuple_runtime_scalar_cursor >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  simp[Abbr `w`] >>
  conj_tac >-
    (Cases_on `p` >> simp[eval_operand_def, op_prov_def, op_taint_def,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  fs[update_var_def, allocas_from_def, allocas_below_fmp_def,
     stmtSimStoreCopyTheory.store_copy_normalize_def] >> metis_tac[]
QED

(* Both representations end with the same immutable store; only the region ADD is optional. *)
Theorem tuple_runtime_region_store[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (case extra of
     NONE => arg = dst /\ at = dwrd /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ at = (rwrd:bytes32)+dwrd /\
       extra_code = [mk_inst id ADD [region;dst] [av]] /\ outs = [av] /\
       eval_operand region s = SOME rwrd /\ op_prov G region = NONE /\
       op_taint tn region = {} /\ v <> Var av) /\
  isPREFIX (extra_code ++ mk_inst (id+LENGTH extra_code) ISTORE [arg;v] []::tail)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand dst s = SOME dwrd /\ op_prov G dst = NONE /\ op_taint tn dst = {} /\
  eval_operand v s = SOME w /\ w2n at + 32 <= lo /\ lo <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    store_copy_normalize s t = istore (w2n at) w s /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH extra_code + 1 /\
    t.vs_current_bb = s.vs_current_bb /\ isPREFIX tail (DROP t.vs_inst_idx bb.bb_instructions) /\
    (!p. ~MEM p outs ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = (tn.t_mem DIFF {j | w2n at <= j /\ j < w2n at + 32}) UNION
      {w2n at + k | k IN op_taint tn v} /\
    tf.t_imm = key_update tn.t_imm (w2n at) (op_taint tn v) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    t.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted
Proof
  strip_tac >>
  `?r Gr tr.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK r,Gr,tr)) /\
     store_copy_normalize s r = s /\ r.vs_inst_idx = s.vs_inst_idx + LENGTH extra_code /\
     r.vs_current_bb = s.vs_current_bb /\ r.vs_alloca_next = s.vs_alloca_next /\
     isPREFIX (mk_inst (id+LENGTH extra_code) ISTORE [arg;v] []::tail)
       (DROP r.vs_inst_idx bb.bb_instructions) /\
     eval_operand arg r = SOME at /\ op_prov Gr arg = NONE /\ op_taint tr arg = {} /\
     eval_operand v r = SOME w /\ op_taint tr v = op_taint tn v /\
     (!p. ~MEM p outs ==> lookup_var p r = lookup_var p s /\
       FLOOKUP Gr p = FLOOKUP G p /\ op_taint tr (Var p) = op_taint tn (Var p)) /\
     tr.t_mem = tn.t_mem /\ tr.t_stor = tn.t_stor /\ tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
     allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\ ~r.vs_halted` by
    (Cases_on `extra` >-
       (gvs[Excl "isPREFIX"] >> qexistsl_tac [`s`,`G`,`tn`] >>
        simp[cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
             stmtSimStoreCopyTheory.store_copy_normalize_def, Excl "isPREFIX"]) >>
     PairCases_on `x` >> gvs[Excl "isPREFIX"] >>
     drule_all (tuple_runtime_binary_prefix |> Q.INST [`opc` |-> `ADD`] |> SRULE [Excl "isPREFIX"]) >>
     disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
     disch_then (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac))) >>
     qexistsl_tac [`r`,`Gr`,`tr`] >> simp[Excl "isPREFIX"] >>
     qx_gen_tac `p` >> strip_tac >>
     qpat_assum `!o'. o' <> Var x2 ==> _` (qspec_then `Var p` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_assum `isPREFIX (mk_inst _ ISTORE _ _::tail) (DROP r.vs_inst_idx _)`
    (mp_then Any strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor) >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `lo <= r.vs_alloca_next` by simp[] >>
  drule_all (tuple_runtime_istore_cursor |> Q.INST [`s` |-> `r`, `G` |-> `Gr`, `tn` |-> `tr`]) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  `store_copy_normalize s t = istore (w2n at) w s` by
    (qpat_x_assum `store_copy_normalize s r = s` (SUBST1_TAC o GSYM) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def, istore_def, mstore_def]) >>
  `SUC r.vs_inst_idx = s.vs_inst_idx + LENGTH extra_code + 1` by decide_tac >>
  simp[Excl "isPREFIX", istore_def, mstore_def, allocas_from_def, allocas_below_fmp_def] >>
  fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

(* Resolve the destination at its live cursor, then use the common store suffix. *)
Theorem tuple_runtime_destination_word[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (mk_inst id MUL [Var cv;Lit 32w] [dm]::
            mk_inst (id+1) ADD [dst;Var dm] [dv]::
            (extra_code ++ mk_inst (id+2+LENGTH extra_code) ISTORE [arg;Var vv] []::tail))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (case extra of
     NONE => arg = Var dv /\ at = bw+k*32w /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ at = rwrd+(bw+k*32w) /\
       extra_code = [mk_inst (id+2) ADD [region;Var dv] [av]] /\ outs = [av] /\
       eval_operand region s = SOME rwrd /\ op_prov G region = NONE /\
       op_taint tn region = {} /\ region <> Var dm /\ region <> Var dv /\ vv <> av) /\
  eval_operand dst s = SOME bw /\ op_prov G dst = NONE /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME k /\ op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
  dst <> Var dm /\ vv <> dm /\ vv <> dv /\ eval_operand (Var vv) s = SOME w /\
  w2n at + 32 <= lo /\ lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    store_copy_normalize s t = istore (w2n at) w s /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + 3 + LENGTH extra_code /\
    isPREFIX tail (DROP t.vs_inst_idx bb.bb_instructions) /\
    (!p. ~MEM p (dm::dv::outs) ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = (tn.t_mem DIFF {j | w2n at <= j /\ j < w2n at + 32}) UNION
      {w2n at + j | j IN op_taint tn (Var vv)} /\
    tf.t_imm = key_update tn.t_imm (w2n at) (op_taint tn (Var vv)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    t.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w /\ op_prov G (Lit 32w) = NONE /\
   op_taint tn (Lit 32w) = {}` by simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all (tuple_runtime_binary_prefix |> Q.INST [`opc` |-> `MUL`] |> SRULE [Excl "isPREFIX"]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `m` (qx_choose_then `Gm` (qx_choose_then `tm` strip_assume_tac)))) >>
  `lookup_block m.vs_current_bb fn.fn_blocks = SOME bb /\
   eval_operand dst m = SOME bw /\ op_prov Gm dst = NONE /\ op_taint tm dst = {}` by simp[] >>
  drule_all (tuple_runtime_binary_prefix |> Q.INST [`opc` |-> `ADD`,
    `s` |-> `m`, `G` |-> `Gm`, `tn` |-> `tm`] |> SRULE [Excl "isPREFIX"]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))) >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb /\ lo <= r.vs_alloca_next /\
   eval_operand (Var vv) r = SOME w /\ op_taint tr (Var vv) = op_taint tn (Var vv)` by simp[] >>
  `case extra of
     NONE => arg = Var dv /\ at = bw+k*32w /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ at = rwrd+(bw+k*32w) /\
       extra_code = [mk_inst (id+2) ADD [region;Var dv] [av]] /\ outs = [av] /\
       eval_operand region r = SOME rwrd /\ op_prov Gr region = NONE /\
       op_taint tr region = {} /\ Var vv <> Var av` by
    (Cases_on `extra` >- fs[] >> PairCases_on `x` >> fs[]) >>
  drule_all (tuple_runtime_region_store |> Q.INST [`s` |-> `r`, `G` |-> `Gr`, `tn` |-> `tr`]) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gm`,`m`,`tm`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  `store_copy_normalize s t = istore (w2n at) w s` by
    (`!base' mid end'. store_copy_normalize base' (store_copy_normalize mid end') =
                         store_copy_normalize base' end'` by
       simp[stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     `store_copy_normalize s r = s` by
       (qpat_assum `store_copy_normalize m r = m`
          (mp_tac o Q.AP_TERM `store_copy_normalize s`) >> simp[]) >>
     qpat_x_assum `store_copy_normalize r t = istore _ _ r`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     simp[] >>
     `store_copy_normalize s (istore (w2n at) w r) =
       istore (w2n at) w (store_copy_normalize s r)` by
       simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def, istore_def, mstore_def] >>
     simp[]) >>
  `t.vs_inst_idx = s.vs_inst_idx + 3 + LENGTH extra_code` by decide_tac >>
  simp[Excl "isPREFIX"] >> rpt strip_tac >>
  qpat_assum `!op. op <> Var dm ==> _` (qspec_then `Var p` mp_tac) >>
  qpat_assum `!op. op <> Var dv ==> _` (qspec_then `Var p` mp_tac) >>
  simp[eval_operand_def]
QED

(* One loop round, from the body cursor back to the header. *)
Theorem tuple_runtime_loop_round[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (mk_inst id MUL [Var cv;Lit 32w] [mv]::
            mk_inst (id+1) ADD [Var src;Var mv] [sv]::
            mk_inst (id+2) MLOAD [Var sv] [vv]::
            mk_inst (id+3) MUL [Var cv;Lit 32w] [dm]::
            mk_inst (id+4) ADD [dst;Var dm] [dv]::
            (extra_code ++ [mk_inst (id+5+LENGTH extra_code) ISTORE [arg;Var vv] [];
                            mk_inst (id+6+LENGTH extra_code) ADD [Var cv;Lit 1w] [nv];
                            mk_inst (id+7+LENGTH extra_code) ASSIGN [Var nv] [cv];
                            mk_inst (id+8+LENGTH extra_code) JMP [Label hdr] []]))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (case extra of
     NONE => arg = Var dv /\ bw = n2w dest /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ rwrd+bw = n2w dest /\
       extra_code = [mk_inst (id+5) ADD [region;Var dv] [av]] /\ outs = [av] /\
       eval_operand region s = SOME rwrd /\ op_prov G region = NONE /\
       op_taint tn region = {} /\ ~MEM region (MAP Var [mv;sv;vv;dm;dv])) /\
  ALL_DISTINCT (src::cv::mv::sv::vv::dm::dv::nv::outs) /\
  ~MEM dst (MAP Var [mv;sv;vv;dm]) /\
  eval_operand dst s = SOME bw /\ op_prov G dst = NONE /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w i) /\ op_prov G (Var cv) = NONE /\
  op_taint tn (Var cv) = {} /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  32*i+32 <= capacity /\ w2n a + 32*i < dimword (:256) /\
  w2n a + 32*i + 32 <= s.vs_alloca_next /\
  dest + 32*i + 32 <= lo /\ dest + 32*i < dimword (:256) /\
  lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
    op_prov Gf (Var cv) = NONE /\ op_taint tf (Var cv) = {} /\
    store_copy_normalize s t = istore (dest+32*i) (mload (w2n a+32*i) s) s /\
    (!p. ~MEM p (cv::mv::sv::vv::dm::dv::nv::outs) ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_mem = (tn.t_mem DIFF {j | dest+32*i <= j /\ j < dest+32*i+32}) UNION
      {dest+32*i + j | j | j IN mem_word_taint tn.t_mem (w2n a+32*i)} /\
    tf.t_imm = key_update tn.t_imm (dest+32*i) (mem_word_taint tn.t_mem (w2n a+32*i)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w /\ op_prov G (Lit 32w) = NONE /\
   op_taint tn (Lit 32w) = {}` by simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all (tuple_runtime_binary_prefix |> Q.INST [`opc` |-> `MUL`] |> SRULE [Excl "isPREFIX"]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `m` (qx_choose_then `Gm` (qx_choose_then `tm` strip_assume_tac)))) >>
  `lookup_block m.vs_current_bb fn.fn_blocks = SOME bb /\
   lookup_var src m = SOME a /\ ptr_covers Gm tm src m capacity /\
   eval_operand (Var mv) m = SOME (n2w (32*i)) /\ src <> sv /\
   w2n a + 32*i + 32 <= m.vs_alloca_next` by
    (`(n2w i:bytes32)*32w = n2w (32*i)` by
       simp[NoAsms, wordsTheory.word_mul_n2w, Once MULT_COMM] >>
     `src <> mv /\ src <> sv` by fs[Excl "isPREFIX"] >>
     `lookup_var src m = lookup_var src s /\ op_taint tm (Var src) = op_taint tn (Var src)` by
       (qpat_assum `!p. p <> Var mv ==> _` (qspec_then `Var src` mp_tac) >> simp[eval_operand_def]) >>
     gvs[NoAsms, wordsTheory.word_mul_n2w, Once MULT_COMM, Excl "isPREFIX",
         ptr_covers_def, eval_operand_def]) >>
  `isPREFIX [mk_inst (id+1) ADD [Var src;Var mv] [sv];
             mk_inst ((id+1)+1) MLOAD [Var sv] [vv]] (DROP m.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_) (DROP m.vs_inst_idx _)`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >> simp[GSYM ADD_ASSOC]) >>
  drule_all (tuple_runtime_source_word |> Q.INST [`s` |-> `m`, `G` |-> `Gm`, `tn` |-> `tm`]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))) >>
  `r.vs_current_bb = m.vs_current_bb /\ r.vs_memory = m.vs_memory /\
   r.vs_labels = m.vs_labels /\ r.vs_alloca_next = m.vs_alloca_next /\
   r.vs_allocas = m.vs_allocas /\ r.vs_fmp = m.vs_fmp /\
   r.vs_initial_fmp = m.vs_initial_fmp /\ r.vs_halted = m.vs_halted` by
    (qpat_assum `r with <|vs_vars := _; vs_inst_idx := _|> = m` mp_tac >>
     simp[NoAsms, venom_state_component_equality]) >>
  `m.vs_memory = s.vs_memory /\ m.vs_labels = s.vs_labels` by
    (conj_tac >-
       (qpat_assum `store_copy_normalize s m = s`
          (mp_tac o Q.AP_TERM `\q. q.vs_memory`) >>
        simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
     qpat_assum `store_copy_normalize s m = s`
       (mp_tac o Q.AP_TERM `\q. q.vs_labels`) >>
     simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bb /\ lo <= r.vs_alloca_next /\
   allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\ ~r.vs_halted /\
   eval_operand (Var vv) r = SOME (mload (w2n a+32*i) s)` by
    (`allocas_from lo r = allocas_from lo m` by
       (rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
     `allocas_below_fmp r = allocas_below_fmp m` by
       (rewrite_tac[allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
     simp[mload_def, Excl "isPREFIX"]) >>
  `!op. ~MEM op (MAP Var [mv;sv;vv]) ==>
     eval_operand op r = eval_operand op s /\ op_prov Gr op = op_prov G op /\
     op_taint tr op = op_taint tn op` by
    (gen_tac >> Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
     rpt strip_tac >>
     qpat_assum `!p. p <> sv /\ p <> vv ==> _` (qspec_then `s'` mp_tac) >>
     qpat_assum `!p. p <> Var mv ==> _` (qspec_then `Var s'` mp_tac) >>
     simp[eval_operand_def, op_prov_def]) >>
  `isPREFIX (mk_inst (id+3) MUL [Var cv;Lit 32w] [dm]::
            mk_inst ((id+3)+1) ADD [dst;Var dm] [dv]::
            (extra_code ++ [mk_inst ((id+3)+2+LENGTH extra_code) ISTORE [arg;Var vv] [];
                            mk_inst (id+6+LENGTH extra_code) ADD [Var cv;Lit 1w] [nv];
                            mk_inst (id+7+LENGTH extra_code) ASSIGN [Var nv] [cv];
                            mk_inst (id+8+LENGTH extra_code) JMP [Label hdr] []]))
    (DROP r.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_) (DROP m.vs_inst_idx _)`
       (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     qpat_assum `isPREFIX (_::_::_) (DROP (SUC m.vs_inst_idx) _)`
       (mp_tac o CONJUNCT2 o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     `r.vs_inst_idx = SUC (SUC m.vs_inst_idx)` by decide_tac >>
     qpat_assum `r.vs_inst_idx = _` SUBST1_TAC >>
     simp[Excl "isPREFIX", GSYM ADD_ASSOC]) >>
  qabbrev_tac `at:bytes32 = n2w (dest+32*i)` >>
  `case extra of
     NONE => arg = Var dv /\ at = bw+n2w i*32w /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ at = rwrd+(bw+n2w i*32w) /\
       extra_code = [mk_inst ((id+3)+2) ADD [region;Var dv] [av]] /\ outs = [av] /\
       eval_operand region r = SOME rwrd /\ op_prov Gr region = NONE /\
       op_taint tr region = {} /\ region <> Var dm /\ region <> Var dv /\ vv <> av` by
    (Cases_on `extra` >-
       gvs[Abbr `at`, Excl "isPREFIX", wordsTheory.word_mul_n2w,
           wordsTheory.word_add_n2w, Once MULT_COMM] >>
     PairCases_on `x` >> fs[Excl "isPREFIX", GSYM ADD_ASSOC] >>
     conj_tac >-
       (simp[NoAsms, Abbr `at`, wordsTheory.WORD_ADD_ASSOC] >>
        qpat_assum `_ + bw = n2w dest` SUBST1_TAC >>
        simp[NoAsms, GSYM wordsTheory.word_add_n2w,
          wordsTheory.word_mul_n2w, Once MULT_COMM]) >>
     qpat_assum `outs = [_]` SUBST_ALL_TAC >> fs[Excl "isPREFIX"]) >>
  `w2n at = dest+32*i` by simp[Abbr `at`, wordsTheory.w2n_n2w, LESS_MOD] >>
  `eval_operand dst r = SOME bw /\ op_prov Gr dst = NONE /\ op_taint tr dst = {} /\
   eval_operand (Var cv) r = SOME (n2w i) /\ op_prov Gr (Var cv) = NONE /\
   op_taint tr (Var cv) = {} /\ dst <> Var dm /\ vv <> dm /\ vv <> dv` by
    fs[Excl "isPREFIX"] >>
  `w2n at + 32 <= lo` by simp[] >>
  drule_all (tuple_runtime_destination_word |>
    Q.INST [`s` |-> `r`, `G` |-> `Gr`, `tn` |-> `tr`] |> SRULE [Excl "isPREFIX"]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac)))) >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   eval_operand (Var cv) u = SOME (n2w i) /\ op_prov Gu (Var cv) = NONE /\
   op_taint tu (Var cv) = {}` by
    (`cv <> dm /\ cv <> dv /\ ~MEM cv outs` by fs[Excl "isPREFIX"] >>
     qpat_assum `!p. _ ==> lookup_var p u = _ /\ _` (qspec_then `cv` mp_tac) >>
     simp[Excl "isPREFIX", eval_operand_def, op_prov_def] >>
     gvs[Excl "isPREFIX", eval_operand_def, op_prov_def]) >>
  `eval_operand (Lit 1w) u = SOME 1w /\ op_prov Gu (Lit 1w) = NONE /\
   op_taint tu (Lit 1w) = {}` by simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all (tuple_runtime_binary_prefix |> Q.INST [`opc` |-> `ADD`,
    `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`] |> SRULE [Excl "isPREFIX"]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z` (qx_choose_then `Gz` (qx_choose_then `tz` strip_assume_tac)))) >>
  `lookup_block z.vs_current_bb fn.fn_blocks = SOME bb /\
   eval_operand (Var nv) z = SOME (n2w (SUC i))` by
    simp[ADD1, wordsTheory.word_add_n2w, Excl "isPREFIX"] >>
  `isPREFIX [mk_inst (id+7+LENGTH extra_code) ASSIGN [Var nv] [cv];
             mk_inst ((id+7+LENGTH extra_code)+1) JMP [Label hdr] []]
    (DROP z.vs_inst_idx bb.bb_instructions)` by
    (`(id+7+LENGTH extra_code)+1 = id+8+LENGTH extra_code` by decide_tac >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all (tuple_runtime_loop_assign_jump |> Q.INST [`s` |-> `z`,
    `G` |-> `Gz`, `tn` |-> `tz`] |> SRULE [Excl "isPREFIX"]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)))) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gm`,`m`,`tm`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> simp[] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gz`,`z`,`tz`] >> simp[]) >>
  `!base' mid end'. store_copy_normalize base' (store_copy_normalize mid end') =
                     store_copy_normalize base' end'` by
    simp[stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  `store_copy_normalize s r = s` by
    (qpat_assum `r with <|vs_vars := _; vs_inst_idx := _|> = m`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def, NoAsms] >>
     qpat_assum `store_copy_normalize s m = s` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def, NoAsms]) >>
  `store_copy_normalize s u = istore (dest+32*i) (mload (w2n a+32*i) s) s` by
    (qpat_assum `store_copy_normalize r u = istore _ _ r`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     simp[Excl "isPREFIX"] >>
     `!p w x. store_copy_normalize s (istore p w x) =
                istore p w (store_copy_normalize s x)` by
       simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def, istore_def, mstore_def] >>
     simp[]) >>
  `store_copy_normalize s t = store_copy_normalize s u` by
    (qpat_assum `store_copy_normalize z t = z`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     qpat_assum `store_copy_normalize u z = u`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >> simp[]) >>
  simp[Excl "isPREFIX"] >> rpt strip_tac >>
  qpat_assum `!p. _ ==> lookup_var p t = _ /\ _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. _ ==> FLOOKUP Gz p = _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. _ ==> eval_operand p z = _ /\ _` (qspec_then `Var p` mp_tac) >>
  qpat_assum `!p. _ ==> lookup_var p u = _ /\ _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. _ ==> lookup_var p r = _ /\ _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. _ ==> FLOOKUP Gm p = _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. _ ==> eval_operand p m = _ /\ _` (qspec_then `Var p` mp_tac) >>
  simp[eval_operand_def, Excl "isPREFIX"]
QED

Theorem tuple_runtime_live_operand[local]:
  t.vs_labels = s.vs_labels /\
  (!p. op = Var p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) ==>
  eval_operand op t = eval_operand op s /\ op_prov Gf op = op_prov G op /\
  op_taint tf op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def]
QED

(* The recursive suffix cannot feed back into the source above the section. *)
Theorem tuple_runtime_taint_round[local]:
  i < n /\ b+32*n <= a /\
  M1 = (M DIFF {j | b+32*i <= j /\ j < b+32*i+32}) UNION
       {b+32*i+j | j | j IN mem_word_taint M (a+32*i)} /\
  (!x. x IN M2 <=> if b+32*SUC i <= x /\ x < b+32*n
                   then a+(x-b) IN M1 else x IN M1) ==>
  !x. x IN M2 <=> if b+32*i <= x /\ x < b+32*n
                 then a+(x-b) IN M else x IN M
Proof
  strip_tac >> gen_tac >>
  `b+32*i+32 = b+32*SUC i` by decide_tac >>
  Cases_on `x < b+32*i` >-
    (`x < b+32*SUC i` by decide_tac >> simp[mem_word_taint_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `x < b+32*SUC i` >-
    (`x < b+32*n` by decide_tac >>
     `?j. x = b+32*i+j /\ j < 32 /\ a+(x-b) = a+32*i+j` by
       (qexists `x-(b+32*i)` >> decide_tac) >>
     simp[mem_word_taint_def] >> metis_tac[]) >>
  Cases_on `x < b+32*n` >-
    (`b+32*SUC i <= a+(x-b)` by decide_tac >> simp[mem_word_taint_def] >>
     eq_tac >> rpt strip_tac >> gvs[] >> decide_tac) >>
  simp[mem_word_taint_def] >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

(* Recurse on the remaining count, using the ordinary transfer recurrence on
   the very state reached by the annotated body. *)
Theorem tuple_runtime_loop_suffix[local]:
  lookup_block hdr fn.fn_blocks = SOME bbh /\
  isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv];
            mk_inst (idh+1) JNZ [Var tv;Label done_lbl;Label body_lbl] []]
    bbh.bb_instructions /\
  lookup_block body_lbl fn.fn_blocks = SOME bbb /\
  isPREFIX (mk_inst idb MUL [Var cv;Lit 32w] [mv]::
            mk_inst (idb+1) ADD [Var src;Var mv] [sv]::
            mk_inst (idb+2) MLOAD [Var sv] [vv]::
            mk_inst (idb+3) MUL [Var cv;Lit 32w] [dm]::
            mk_inst (idb+4) ADD [dst;Var dm] [dv]::
            (extra_code ++ [mk_inst (idb+5+LENGTH extra_code) ISTORE [arg;Var vv] [];
                            mk_inst (idb+6+LENGTH extra_code) ADD [Var cv;Lit 1w] [nv];
                            mk_inst (idb+7+LENGTH extra_code) ASSIGN [Var nv] [cv];
                            mk_inst (idb+8+LENGTH extra_code) JMP [Label hdr] []]))
    bbb.bb_instructions /\
  (case extra of
     NONE => arg = Var dv /\ bw = n2w dest /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ rwrd+bw = n2w dest /\
       extra_code = [mk_inst (idb+5) ADD [region;Var dv] [av]] /\ outs = [av] /\
       ~MEM region (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs))) /\
  ALL_DISTINCT (src::tv::cv::mv::sv::vv::dm::dv::nv::outs) /\
  ~MEM dst (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs)) /\
  ~MEM cnt (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs)) /\
  32*n <= capacity /\ dest+32*n <= lo /\ lo <= w2n a /\
  w2n a+32*n < dimword (:256) ==>
  !remaining i s G tn.
    i+remaining = n /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} /\
    eval_operand cnt s = SOME (n2w n) /\ op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
    eval_operand dst s = SOME bw /\ op_prov G dst = NONE /\ op_taint tn dst = {} /\
    (!region rwrd av. extra = SOME (region,rwrd,av) ==>
       eval_operand region s = SOME rwrd /\ op_prov G region = NONE /\ op_taint tn region = {}) /\
    lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
    w2n a+32*n <= s.vs_alloca_next /\ lo <= s.vs_alloca_next /\ allocas_from lo s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ?t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
      t.vs_current_bb = done_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      store_copy_normalize s t = immutable_transfers T T a (n2w dest) remaining (32*i) s /\
      (!p. ~MEM p (tv::cv::mv::sv::vv::dm::dv::nv::outs) ==>
           lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
           op_taint tf (Var p) = op_taint tn (Var p)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      (!x. x IN tf.t_mem <=> if dest+32*i <= x /\ x < dest+32*n
                             then w2n a+(x-dest) IN tn.t_mem else x IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Induct
  >- suspend "base" >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < n /\ n < dimword (:256) /\ i < dimword (:256)` by decide_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bbh /\
   isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv];
             mk_inst (idh+1) JNZ [Var tv;Label done_lbl;Label body_lbl] []]
     (DROP s.vs_inst_idx bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  drule_all tuple_runtime_loop_test >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))) >>
  `r.vs_current_bb = body_lbl` by
    (`(n2w i:bytes32) <> n2w n` by simp[wordsTheory.n2w_11, LESS_MOD] >> simp[]) >>
  `r.vs_memory = s.vs_memory /\ r.vs_labels = s.vs_labels /\
   r.vs_allocas = s.vs_allocas /\ r.vs_initial_fmp = s.vs_initial_fmp /\
   r.vs_fmp = s.vs_fmp /\ r.vs_alloca_next = s.vs_alloca_next /\
   ~r.vs_halted` by
    (qpat_assum `store_copy_normalize s r = s`
       (strip_assume_tac o SIMP_RULE (srw_ss())
          [stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality]) >> simp[]) >>
  `!op. op <> Var tv ==>
     eval_operand op r = eval_operand op s /\ op_prov Gr op = op_prov G op /\
     op_taint tr op = op_taint tn op` by
    (gen_tac >> disch_tac >> match_mp_tac tuple_runtime_live_operand >> simp[] >> metis_tac[]) >>
  suspend "round"
QED

Resume tuple_runtime_loop_suffix[base]:
  simp[immutable_transfers_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bbh /\
   isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv];
             mk_inst (idh+1) JNZ [Var tv;Label done_lbl;Label body_lbl] []]
     (DROP s.vs_inst_idx bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  drule_all tuple_runtime_loop_test >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` strip_assume_tac)))) >>
  `~r.vs_halted` by
    (qpat_assum `store_copy_normalize s r = s`
       (strip_assume_tac o SIMP_RULE (srw_ss())
          [stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality]) >> simp[]) >>
  qexistsl_tac [`r`,`Gr`,`tr`] >> simp[Excl "isPREFIX"]
QED

Resume tuple_runtime_loop_suffix[round]:
  `lookup_block r.vs_current_bb fn.fn_blocks = SOME bbb /\
   lo <= r.vs_alloca_next /\ allocas_from lo r /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    (`allocas_from lo r = allocas_from lo s /\
      allocas_below_fmp r = allocas_below_fmp s` by (simp[allocas_from_def, allocas_below_fmp_def] >> (gvs[allocas_from_def, allocas_below_fmp_def])) >>
     simp[Excl "isPREFIX"]) >>
  `eval_operand (Var cv) r = SOME (n2w i) /\ op_prov Gr (Var cv) = NONE /\
   op_taint tr (Var cv) = {} /\
   eval_operand dst r = SOME bw /\ op_prov Gr dst = NONE /\ op_taint tr dst = {} /\
   lookup_var src r = SOME a /\ ptr_covers Gr tr src r capacity` by
    (`lookup_var src r = lookup_var src s /\ FLOOKUP Gr src = FLOOKUP G src /\
      op_taint tr (Var src) = op_taint tn (Var src)` by
       (qpat_assum `!p. p <> tv ==> _` (qspec_then `src` mp_tac) >>
        fs[Excl "isPREFIX"]) >>
     qpat_assum `!op. _ ==> eval_operand op r = _ /\ _` (qspec_then `dst` mp_tac) >>
     qpat_assum `!op. _ ==> eval_operand op r = _ /\ _` (qspec_then `Var cv` mp_tac) >>
     fs[ptr_covers_def, Excl "isPREFIX"] >> gvs[Excl "isPREFIX"]) >>
  `case extra of
     NONE => arg = Var dv /\ bw = n2w dest /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ rwrd+bw = n2w dest /\
       extra_code = [mk_inst (idb+5) ADD [region;Var dv] [av]] /\ outs = [av] /\
       eval_operand region r = SOME rwrd /\ op_prov Gr region = NONE /\
       op_taint tr region = {} /\ ~MEM region (MAP Var [mv;sv;vv;dm;dv])` by
    (Cases_on `extra` >- fs[Excl "isPREFIX"] >> PairCases_on `x` >>
     qpat_assum `!op. _ ==> eval_operand op r = _ /\ _` (qspec_then `x0` mp_tac) >>
     fs[Excl "isPREFIX"]) >>
  `32*i+32 <= capacity /\ w2n a+32*i < dimword (:256) /\
   w2n a+32*i+32 <= r.vs_alloca_next /\ dest+32*i+32 <= lo /\
   dest+32*i < dimword (:256)` by decide_tac >>
  `ALL_DISTINCT (src::cv::mv::sv::vv::dm::dv::nv::outs) /\
   ~MEM dst (MAP Var [mv;sv;vv;dm])` by fs[Excl "isPREFIX"] >>
  mp_tac (tuple_runtime_loop_round |> Q.INST [`s` |-> `r`, `G` |-> `Gr`,
    `tn` |-> `tr`, `id` |-> `idb`, `bb` |-> `bbb`]) >>
  (impl_tac >-
     (qpat_assum `isPREFIX (mk_inst idb MUL _ _ :: _) bbb.bb_instructions` mp_tac >>
      simp[Excl "isPREFIX"] >> gvs[Excl "isPREFIX"])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))) >>
  suspend "recur"
QED

Resume tuple_runtime_loop_suffix[recur]:
  `u.vs_labels = s.vs_labels /\ u.vs_allocas = s.vs_allocas /\
   u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_fmp = s.vs_fmp /\
   u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted` by
    (qpat_assum `store_copy_normalize r u = istore _ _ r`
       (strip_assume_tac o SIMP_RULE (srw_ss())
          [stmtSimStoreCopyTheory.store_copy_normalize_def,
           istore_def, mstore_def, venom_state_component_equality]) >> simp[]) >>
  `!p. ~MEM p (tv::cv::mv::sv::vv::dm::dv::nv::outs) ==>
       lookup_var p u = lookup_var p s /\ FLOOKUP Gu p = FLOOKUP G p /\
       op_taint tu (Var p) = op_taint tn (Var p)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!p. _ ==> lookup_var p u = _ /\ _` (qspec_then `p` mp_tac) >>
     qpat_assum `!p. p <> tv ==> _` (qspec_then `p` mp_tac) >>
     fs[Excl "isPREFIX"]) >>
  `!op. ~MEM op (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs)) ==>
       eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
       op_taint tu op = op_taint tn op` by
    (gen_tac >> disch_tac >> match_mp_tac tuple_runtime_live_operand >> simp[Excl "isPREFIX"] >>
     rpt strip_tac >> gvs[Excl "isPREFIX", MEM_MAP] >>
     qpat_assum `!p. _ ==> lookup_var p u = lookup_var p s /\ _`
       (qspec_then `p` mp_tac) >> simp[Excl "isPREFIX"]) >>
  `allocas_from lo u = allocas_from lo s /\ allocas_below_fmp u = allocas_below_fmp s` by
    (rewrite_tac[allocas_from_def, allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  `lookup_var src u = SOME a /\ ptr_covers Gu tu src u capacity` by
    (qpat_assum `!p. _ ==> lookup_var p u = lookup_var p s /\ _`
       (qspec_then `src` mp_tac) >>
     (impl_tac >-
       qpat_assum `ALL_DISTINCT (src::_)`
         (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [listTheory.ALL_DISTINCT])) >>
     strip_tac >>
     conj_tac >- simp[] >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i s G tn. _ ==> ?t Gf tf. _`
    (qspecl_then [`SUC i`,`u`,`Gu`,`tu`] mp_tac) >>
  (impl_tac >-
     (`SUC i + remaining = n` by decide_tac >>
      qpat_assum `!op. _ ==> eval_operand op u = _ /\ _` (qspec_then `cnt` mp_tac) >>
      qpat_assum `!op. _ ==> eval_operand op u = _ /\ _` (qspec_then `dst` mp_tac) >>
      fs[Excl "isPREFIX"] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!r w v. extra = SOME (r,w,v) ==> eval_operand r s = _ /\ _`
        (qspecl_then [`region`,`rwrd`,`av`] mp_tac) >>
      qpat_assum `!op. _ ==> eval_operand op u = _ /\ _` (qspec_then `region` mp_tac) >>
      gvs[])) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  (conj_tac >-
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gr`,`r`,`tr`] >> simp[Excl "isPREFIX"] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> simp[Excl "isPREFIX"])) >>
  `!base mid finish. store_copy_normalize base (store_copy_normalize mid finish) =
                    store_copy_normalize base finish` by
    simp[stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  `store_copy_normalize s u = istore (dest+32*i) (mload (w2n a+32*i) s) s` by
    (qpat_assum `store_copy_normalize r u = istore _ _ r`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     `!p w x. store_copy_normalize s (istore p w x) =
                istore p w (store_copy_normalize s x)` by
       simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def, istore_def, mstore_def] >>
     simp[mload_def, Excl "isPREFIX"]) >>
  `dest + 32*i < dimword (:256) /\ w2n a+32*i < dimword (:256) /\
   32*SUC i = 32*i+32` by decide_tac >>
  `store_copy_normalize s t = immutable_transfers T T a (n2w dest) (SUC remaining) (32*i) s` by
    (qpat_assum `store_copy_normalize u t = immutable_transfers T T a _ _ _ u`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     simp[immutable_transfers_normalize, immutable_transfers_def, immutable_word_transfer_def,
          immutable_copy_read_def, wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
          wordsTheory.w2n_n2w, LESS_MOD, abiDecodeStaticPropsTheory.w2n_add_n2w_lt,
          Excl "isPREFIX"]) >>
  `!p. ~MEM p (tv::cv::mv::sv::vv::dm::dv::nv::outs) ==>
       lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tf (Var p) = op_taint tn (Var p)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!p. _ ==> lookup_var p t = _ /\ _` (qspec_then `p` mp_tac) >>
     qpat_assum `!p. _ ==> lookup_var p u = lookup_var p s /\ _` (qspec_then `p` mp_tac) >>
     simp[]) >>
  rpt (conj_tac >- simp[Excl "isPREFIX"]) >>
  match_mp_tac (Q.INST [`M1` |-> `tu.t_mem`] tuple_runtime_taint_round) >>
  simp[Excl "isPREFIX"] >> decide_tac
QED

Finalise tuple_runtime_loop_suffix[local]

(* Consume the entry prefix at the count endpoint, then stay on the same
   annotated run throughout the loop. *)
Theorem tuple_runtime_loop_from_entry[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb0 /\
  isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv];
            mk_inst (id0+1) JMP [Label hdr] []]
    (DROP s.vs_inst_idx bb0.bb_instructions) /\
  lookup_block hdr fn.fn_blocks = SOME bbh /\
  isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv];
            mk_inst (idh+1) JNZ [Var tv;Label done_lbl;Label body_lbl] []]
    bbh.bb_instructions /\
  lookup_block body_lbl fn.fn_blocks = SOME bbb /\
  isPREFIX (mk_inst idb MUL [Var cv;Lit 32w] [mv]::
            mk_inst (idb+1) ADD [Var src;Var mv] [sv]::
            mk_inst (idb+2) MLOAD [Var sv] [vv]::
            mk_inst (idb+3) MUL [Var cv;Lit 32w] [dm]::
            mk_inst (idb+4) ADD [dst;Var dm] [dv]::
            (extra_code ++ [mk_inst (idb+5+LENGTH extra_code) ISTORE [arg;Var vv] [];
                            mk_inst (idb+6+LENGTH extra_code) ADD [Var cv;Lit 1w] [nv];
                            mk_inst (idb+7+LENGTH extra_code) ASSIGN [Var nv] [cv];
                            mk_inst (idb+8+LENGTH extra_code) JMP [Label hdr] []]))
    bbb.bb_instructions /\
  (case extra of
     NONE => arg = Var dv /\ bw = n2w dest /\ extra_code = [] /\ outs = []
   | SOME (region,rwrd,av) =>
       arg = Var av /\ rwrd+bw = n2w dest /\
       extra_code = [mk_inst (idb+5) ADD [region;Var dv] [av]] /\ outs = [av] /\
       ~MEM region (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs))) /\
  ALL_DISTINCT (src::tv::cv::mv::sv::vv::dm::dv::nv::outs) /\
  ~MEM dst (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs)) /\
  ~MEM cnt (MAP Var (tv::cv::mv::sv::vv::dm::dv::nv::outs)) /\
  32*n <= capacity /\ dest+32*n <= lo /\ lo <= w2n a /\
  w2n a+32*n < dimword (:256) /\ ~s.vs_halted /\
  eval_operand cnt s = SOME (n2w n) /\ op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  eval_operand dst s = SOME bw /\ op_prov G dst = NONE /\ op_taint tn dst = {} /\
  (!region rwrd av. extra = SOME (region,rwrd,av) ==>
     eval_operand region s = SOME rwrd /\ op_prov G region = NONE /\ op_taint tn region = {}) /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  w2n a+32*n <= s.vs_alloca_next /\ lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    t.vs_current_bb = done_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    store_copy_normalize s t = immutable_transfers T T a (n2w dest) n 0 s /\
    (!p. ~MEM p (tv::cv::mv::sv::vv::dm::dv::nv::outs) ==>
         lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. x IN tf.t_mem <=> if dest <= x /\ x < dest+32*n
                           then w2n a+(x-dest) IN tn.t_mem else x IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Lit 0w) s = SOME 0w /\
   op_prov G (Lit 0w) = NONE /\ op_taint tn (Lit 0w) = {}` by
    simp[eval_operand_def,op_prov_def,op_taint_def] >>
  drule_all tuple_runtime_loop_assign_jump >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr`
      (map_every assume_tac o CONJUNCTS))))) >>
  `r.vs_memory = s.vs_memory /\ r.vs_labels = s.vs_labels /\
   r.vs_allocas = s.vs_allocas /\ r.vs_initial_fmp = s.vs_initial_fmp /\
   r.vs_fmp = s.vs_fmp /\ r.vs_alloca_next = s.vs_alloca_next /\ ~r.vs_halted` by
    (qpat_assum `store_copy_normalize s r = s`
       (strip_assume_tac o SIMP_RULE (srw_ss())
          [stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality]) >> simp[]) >>
  `!op. op <> Var cv ==>
     eval_operand op r = eval_operand op s /\ op_prov Gr op = op_prov G op /\
     op_taint tr op = op_taint tn op` by
    (gen_tac >> disch_tac >> irule tuple_runtime_live_operand >> simp[] >> metis_tac[]) >>
  `allocas_from lo r = allocas_from lo s /\ allocas_below_fmp r = allocas_below_fmp s` by
    (rewrite_tac[allocas_from_def,allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  `lookup_var src r = SOME a /\ ptr_covers Gr tr src r capacity` by
    (qpat_assum `!p. p <> cv ==> _` (qspec_then `src` mp_tac) >>
     gvs[ptr_covers_def, Excl "isPREFIX"]) >>
  drule_at (Pat `isPREFIX (mk_inst _ MUL _ _ :: _) _`) tuple_runtime_loop_suffix >>
  suspend "apply_suffix"
QED

Resume tuple_runtime_loop_from_entry[apply_suffix]:
  disch_then (qspecl_then [`tv`,`outs`,`n`,`lo`,`idh`,`fn`,`extra`,`explicit`,
    `done_lbl`,`dest`,`ctx`,`cnt`,`capacity`,`bw`,`body_lbl`,`bbh`,`a`,`PG`,
    `n`,`0`,`r`,`Gr`,`tr`] mp_tac) >>
  (impl_tac >- suspend "header") >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> conj_tac
  >- (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  suspend "exit"
QED

Resume tuple_runtime_loop_from_entry[header]:
  `cnt <> Var cv /\ dst <> Var cv` by fs[Excl "isPREFIX"] >>
  qpat_assum `!op. op <> Var cv ==> _` (qspec_then `cnt` mp_tac) >>
  qpat_assum `!op. op <> Var cv ==> _` (qspec_then `dst` mp_tac) >>
  simp[Excl "isPREFIX"] >> rpt strip_tac >>
  qpat_assum `!ro w av. extra = SOME (ro,w,av) ==> _`
    (qspecl_then [`region`,`rwrd`,`av`] mp_tac) >>
  qpat_assum `!op. op <> Var cv ==> _` (qspec_then `region` mp_tac) >>
  gvs[Excl "isPREFIX"]
QED

Resume tuple_runtime_loop_from_entry[exit]:
  `store_copy_normalize s t = immutable_transfers T T a (n2w dest) n 0 s` by
    (`!u. store_copy_normalize s (store_copy_normalize r u) = store_copy_normalize s u` by
       simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     qpat_assum `store_copy_normalize r t = _`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     asm_rewrite_tac[immutable_transfers_normalize, arithmeticTheory.MULT_0]) >>
  simp[Excl "isPREFIX"] >> gen_tac >> strip_tac >>
  qpat_assum `!p. ~MEM p _ ==> lookup_var p t = _ /\ _` (qspec_then `p` mp_tac) >>
  qpat_assum `!p. p <> cv ==> _` (qspec_then `p` mp_tac) >>
  fs[Excl "isPREFIX"]
QED

Finalise tuple_runtime_loop_from_entry[local]

(* The two compiler packets differ only in how they form the ISTORE address. *)
Theorem tuple_runtime_compiled_loop[local]:
  compile_word_copy_loop_base (Var src) (Lit (n2w off)) cnt LocMemory LocCode T imm sa = (u,sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa src /\ copy_old_operand sa cnt /\
  (!region. imm = SOME region ==> copy_old_operand sa region /\
     eval_operand region s = SOME 0w /\ op_prov G region = NONE /\ op_taint tn region = {}) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ eval_operand cnt s = SOME (n2w n) /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s capacity /\
  32*n <= capacity /\ off+32*n <= lo /\ lo <= w2n a /\
  w2n a+32*n < dimword (:256) /\ w2n a+32*n <= s.vs_alloca_next /\
  lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    store_copy_normalize s t = immutable_transfers T T a (n2w off) n 0 s /\
    (!p. not_fresh_at sa p ==>
         lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. x IN tf.t_mem <=> if off <= x /\ x < off+32*n
                           then w2n a+(x-off) IN tn.t_mem else x IN tn.t_mem)
Proof
  Cases_on `imm` >> disch_then (map_every assume_tac o CONJUNCTS)
  >- (drule_all immutableBytestringRuntimeTheory.compile_imm_store_loop_none_code >>
      strip_tac >> suspend "none") >>
  drule_all immutableCopyExecutionTheory.immutable_loop_code >>
  strip_tac >> suspend "some"
QED

Resume tuple_runtime_compiled_loop[none]:
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb0 /\
   isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv];mk_inst (id0+1) JMP [Label hdr] []]
     (DROP s.vs_inst_idx bb0.bb_instructions)` by simp[Excl "isPREFIX"] >>
  `ALL_DISTINCT [src;tv;cv;mv;sv;vv;dm;dv;nv] /\
   ~MEM cnt (MAP Var [tv;cv;mv;sv;vv;dm;dv;nv])` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
     fs[copy_old_operand_def,MEM_MAP,Excl "isPREFIX"] >> metis_tac[]) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_prov G (Lit (n2w off)) = NONE /\ op_taint tn (Lit (n2w off)) = {}` by
    simp[eval_operand_def,op_prov_def,op_taint_def] >>
  `?t Gf tf.
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       store_copy_normalize s t = immutable_transfers T T a (n2w off) n 0 s /\
       (!p. ~MEM p [tv;cv;mv;sv;vv;dm;dv;nv] ==>
          lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tf (Var p) = op_taint tn (Var p)) /\
       tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
       (!x. x IN tf.t_mem <=> if off <= x /\ x < off+32*n
                              then w2n a+(x-off) IN tn.t_mem else x IN tn.t_mem)` by
    (irule (tuple_runtime_loop_from_entry |>
      Q.INST [`extra` |-> `NONE`, `extra_code` |-> `[]`, `outs` |-> `[]`,
              `arg` |-> `Var dv`, `dst` |-> `Lit (n2w off)`, `bw` |-> `n2w off`,
              `dest` |-> `off`] |>
      SIMP_RULE bool_ss [APPEND,LENGTH,arithmeticTheory.ADD_0,MAP,operand_distinct]) >>
     suspend "none_inputs") >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[Excl "isPREFIX"] >>
  metis_tac[MEM]
QED

Resume tuple_runtime_compiled_loop[none_inputs]:
  simp[Excl "isPREFIX"] >>
  qexistsl_tac [`bbb`,`bbh`,`body_lbl`,`capacity`,`cnt`,`hdr`,`id0`,`idb`,`idh`,`src`] >>
  gvs[Excl "isPREFIX"]
QED

Resume tuple_runtime_compiled_loop[some]:
  rename1 `compile_word_copy_loop_base _ _ _ _ _ _ (SOME region) _ = _` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb0 /\
   isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv];mk_inst (id0+1) JMP [Label hdr] []]
     (DROP s.vs_inst_idx bb0.bb_instructions)` by simp[Excl "isPREFIX"] >>
  `copy_old_operand sa region /\ eval_operand region s = SOME 0w /\
   op_prov G region = NONE /\ op_taint tn region = {}` by metis_tac[] >>
  `ALL_DISTINCT [src;tv;cv;mv;sv;vv;dm;dv;nv;av] /\
   ~MEM cnt (MAP Var [tv;cv;mv;sv;vv;dm;dv;nv;av]) /\
   ~MEM region (MAP Var [tv;cv;mv;sv;vv;dm;dv;nv;av])` by
    (qpat_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
     fs[copy_old_operand_def,MEM_MAP,Excl "isPREFIX"] >> metis_tac[]) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_prov G (Lit (n2w off)) = NONE /\ op_taint tn (Lit (n2w off)) = {}` by
    simp[eval_operand_def,op_prov_def,op_taint_def] >>
  `?t Gf tf.
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
       t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       store_copy_normalize s t = immutable_transfers T T a (n2w off) n 0 s /\
       (!p. ~MEM p [tv;cv;mv;sv;vv;dm;dv;nv;av] ==>
          lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
          op_taint tf (Var p) = op_taint tn (Var p)) /\
       tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
       (!x. x IN tf.t_mem <=> if off <= x /\ x < off+32*n
                              then w2n a+(x-off) IN tn.t_mem else x IN tn.t_mem)` by
    (irule (tuple_runtime_loop_from_entry |>
      Q.INST [`extra` |-> `SOME (region,0w,av)`,
              `extra_code` |-> `[mk_inst (idb+5) ADD [region;Var dv] [av]]`,
              `outs` |-> `[av]`, `arg` |-> `Var av`, `dst` |-> `Lit (n2w off)`,
              `bw` |-> `n2w off`, `dest` |-> `off`] |>
      SIMP_RULE bool_ss [APPEND,LENGTH,MAP,operand_distinct]) >>
     suspend "some_inputs") >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[Excl "isPREFIX"] >>
  metis_tac[MEM]
QED

Resume tuple_runtime_compiled_loop[some_inputs]:
  simp[Excl "isPREFIX"] >>
  qexistsl_tac [`bbb`,`bbh`,`body_lbl`,`capacity`,`cnt`,`hdr`,`id0`,`idb`,`idh`,`region`,`src`] >>
  gvs[Excl "isPREFIX", GSYM arithmeticTheory.ADD_ASSOC]
QED

Finalise tuple_runtime_compiled_loop[local]

(* Run the count and the store using one chain of annotated endpoints. *)
Theorem tuple_runtime_compiled_store[local]:
  compile_store_immutable_bytestring imm (Var src) (Lit (n2w off)) sa = ((),sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa src /\
  (!region. imm = SOME region ==> copy_old_operand sa region /\
     eval_operand region s = SOME 0w /\ op_prov G region = NONE /\ op_taint tn region = {}) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ lookup_var src s = SOME a /\ mload (w2n a) s = n2w len /\
  len + 63 < dimword (:256) /\ ptr_covers G tn src s capacity /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  32*(1+word_size len) <= capacity /\ off+32*(1+word_size len) <= lo /\ lo <= w2n a /\
  w2n a+32*(1+word_size len) < dimword (:256) /\
  w2n a+32*(1+word_size len) <= s.vs_alloca_next /\
  lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    store_copy_normalize s t = immutable_transfers T T a (n2w off) (1+word_size len) 0 s /\
    (!p. not_fresh_at sa p ==>
         lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. x IN tf.t_mem <=> if off <= x /\ x < off+32*(1+word_size len)
                           then w2n a+(x-off) IN tn.t_mem else x IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_bytestring_word_count (Var src) sa` >>
  rename1 `compile_bytestring_word_count _ _ = (cnt,sm)` >>
  Cases_on `compile_word_copy_loop_base (Var src) (Lit (n2w off)) cnt LocMemory LocCode T imm sm` >>
  rename1 `compile_word_copy_loop_base _ _ _ _ _ _ _ _ = (u,sn)` >>
  `sn = sb` by fs[compile_store_immutable_bytestring_def, comp_bind_def,
                  comp_ignore_bind_def, comp_return_def] >>
  qpat_x_assum `sn = sb` SUBST_ALL_TAC >>
  drule bytestringCopyExecutionTheory.bytestring_word_count_shape >> strip_tac >>
  `cs_extends sa sm` by (irule cs_extends_same_block >> fs[same_blocks_def]) >>
  `cs_extends sm sb` by
    (mp_tac (Q.SPECL [`Var src`,`Lit (n2w off)`,`cnt`,`LocMemory`,`LocCode`,`T`,
                      `imm`,`sm`] ci_mono_word_copy) >> simp[ci_mono_def]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by (irule fn_has_code_split >> simp[]) >>
  `ptr_covers G tn src s 32 /\ w2n a + 32 <= s.vs_alloca_next` by
    (fs[ptr_covers_def] >> decide_tac) >>
  drule_all tuple_runtime_word_count >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `r` (qx_choose_then `Gr` (qx_choose_then `tr` (qx_choose_then `wc`
      (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "after_count"
QED

Resume tuple_runtime_compiled_store[after_count]:
  `store_copy_normalize s r = s /\ r.vs_allocas = s.vs_allocas /\
   r.vs_alloca_next = s.vs_alloca_next /\ r.vs_fmp = s.vs_fmp /\
   r.vs_initial_fmp = s.vs_initial_fmp /\ r.vs_labels = s.vs_labels` by
    (qpat_assum `(r with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,venom_state_component_equality]) >>
  `allocas_from lo r = allocas_from lo s /\ allocas_below_fmp r = allocas_below_fmp s` by
    (rewrite_tac[allocas_from_def,allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (simp[not_fresh_at_def] >> decide_tac) >>
  `not_fresh_at sm src /\ copy_old_operand sm cnt /\
   lookup_var src r = SOME a /\ ptr_covers Gr tr src r capacity` by
    (qpat_assum `!p. not_fresh_at sa p ==> lookup_var p r = _ /\ _`
       (qspec_then `src` (drule_then strip_assume_tac)) >>
     `ptr_covers Gr tr src r capacity = ptr_covers G tn src s capacity` by
       (rewrite_tac[ptr_covers_def] >> asm_rewrite_tac[]) >>
     simp[copy_old_operand_def]) >>
  `!region. imm = SOME region ==> copy_old_operand sm region /\
     eval_operand region r = SOME 0w /\ op_prov Gr region = NONE /\ op_taint tr region = {}` by
    (gen_tac >> disch_tac >>
     qpat_assum `!region. imm = SOME region ==> _` (drule_then strip_assume_tac) >>
     Cases_on `region` >> gvs[eval_operand_def,copy_old_operand_def,op_prov_def,op_taint_def]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `r`, `G` |-> `Gr`, `tn` |-> `tr`,
                  `n` |-> `1+word_size len`] tuple_runtime_compiled_loop) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> conj_tac
  >- (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gr`,`r`,`tr`] >> simp[]) >>
  `store_copy_normalize s t = immutable_transfers T T a (n2w off) (1+word_size len) 0 s` by
    (`!u. store_copy_normalize s (store_copy_normalize r u) = store_copy_normalize s u` by
       simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     qpat_assum `store_copy_normalize r t = _`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     asm_rewrite_tac[immutable_transfers_normalize]) >>
  simp[] >> metis_tac[]
QED

Finalise tuple_runtime_compiled_store[local]

(* The runtime count reads only the length word, which is never dead. *)
Theorem tuple_runtime_header_clean[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  32 <= type_memory_size tv /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) ==>
  !i. a <= i /\ i < a+32 ==> i NOTIN dirty
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_formed_type_value tv /\ val_wf tv v` by
    metis_tac[evaluate_type_well_formed_type_value,valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!j. j < type_memory_size tv /\ a+j IN dirty ==> mem_dead_bytes mem a tv (a+j)` by
    (mp_tac (Q.SPECL [`tv`,`v`,`a`,`mem`,`dirty`]
       immutableRepSensitivityTheory.body_assign_immutable_rep_sensitivity) >> simp[]) >>
  rpt strip_tac >>
  `i-a < type_memory_size tv /\ a+(i-a) = i` by decide_tac >>
  `mem_dead_bytes mem a tv i` by metis_tac[] >>
  drule_all valueCopyBytesTheory.bytestring_type_value >>
  metis_tac[ctorDeployDeadSectionTheory.mem_dead_bytes_header_live]
QED

(* The runtime loop copies the meaningful prefix, possibly rounding it up
   to a word, but it need not initialize the rest of the reserved slot. *)
Theorem tuple_runtime_bytes_robust[local]:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_footprint stv v <= n /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory stv v a m) /\
  mem_bytes_at off n mem' = mem_bytes_at a n mem /\
  (!i. i < n ==> (off+i IN dirty' <=> a+i IN dirty)) ==>
  !m. mem_agree_outside dirty' mem' m ==> val_in_memory dtv v off m
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `val_in_memory stv v off m` by
    (irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
     simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
     qexistsl_tac [`mem`,`mem'`,`n`,`a`,`dirty`,`dirty'`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_in_memory dtv v off m /\
   immutable_value_bytes_rel dtv v (mem_bytes_at off (type_memory_size dtv) m)` suffices_by simp[] >>
  irule immutableDeployMeaningfulTransferTheory.immutable_direct_meaningful_transfer >> simp[] >>
  qexistsl_tac [`dty`,`m`,`val_footprint stv v`,`off`,`stv`,`sty`,`tenv`] >> simp[]
QED

(* The runtime physical representation and both posts refer to the exit of
   the annotated store, not to an independently run ordinary loop. *)
Theorem tuple_immutable_runtime_bytes_joint[local]:
  compile_assign_value ce (Lit (n2w off)) LocCode (Var root) F loc dty sty
    (type_memory_bytes ce dty) sa = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env st /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME dty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv vi /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv vi /\
  write_place cx (ImmutablePlace ce.ce_module id []) vi st = (INL (),fin) /\
  not_fresh_at sa root /\ lookup_var root s = SOME (n2w a) /\
  (!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
    copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  off + type_memory_size dtv <= lo /\ lo <= a /\ lo <= s.vs_alloca_next /\
  ptr_covers G tn root s (type_memory_size stv) /\
  a + type_memory_size stv < dimword (:256) /\
  a + type_memory_size stv <= s.vs_alloca_next /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory stv vi a mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~block_is_terminated sb /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gf,tf)) /\
    (!H : (bool # 'b word # type_value) list # num list.
      stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
      stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!(H : (bool # 'b word # type_value) list # num list) D.
      stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
      ghost_inv_at D lo d ce cx st G tn s ==> ghost_inv_at D lo d ce cx fin Gf tf q) /\
    (!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==> val_in_memory dtv vi off mem) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_fmp = s.vs_fmp /\ q.vs_call_ctx = s.vs_call_ctx /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p q n) /\
    (!p n. regions_disjoint p n off (type_memory_size dtv) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!x. ~(off <= x /\ x < off + type_memory_size dtv) ==>
      (x IN tf.t_mem <=> x IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_in_memory stv vi a s.vs_memory` by metis_tac[mem_agree_outside_def] >>
  `val_footprint stv vi <= type_memory_size stv` by
    metis_tac[exprSimPropsTheory.val_footprint_le,valueEncodingTypingTheory.value_has_type_val_wf] >>
  `a + val_footprint stv vi < dimword (:256) /\
   off + type_memory_size dtv < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`b` |-> `off`, `v` |-> `vi`, `tenv` |-> `get_tenv cx`]
    immutableBytestringFootprintTheory.immutable_bytestring_runtime_transfer) >>
  (impl_tac >- (simp[] >> disj2_tac >> decide_tac)) >>
  disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
  `32 <= type_memory_size stv` by decide_tac >>
  `!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem` by
    metis_tac[tuple_runtime_header_clean] >>
  `compile_store_immutable_bytestring ce.ce_imm_alloca (Var root) (Lit (n2w off)) sa = ((),sb)` by
    fs[stmtLoweringTheory.compile_assign_value_def,comp_bind_def,comp_return_def] >>
  `w2n (n2w a : bytes32) = a` by simp[wordsTheory.w2n_n2w_compute] >>
  (* Give the word-valued formal a different name from the numeric address. *)
  mp_tac (Q.INST [`imm` |-> `ce.ce_imm_alloca`, `src` |-> `root`,
                  `capacity` |-> `type_memory_size stv`, `a` |-> `n2w addr`]
    tuple_runtime_compiled_store |> Q.INST [`addr` |-> `a`]) >>
  (impl_tac >- suspend "compiled_inputs") >>
  disch_then (qx_choose_then `q` (qx_choose_then `Gf` (qx_choose_then `tf`
    (map_every assume_tac o CONJUNCTS)))) >>
  suspend "physical_post"
QED

Resume tuple_immutable_runtime_bytes_joint[compiled_inputs]:
  `!region. ce.ce_imm_alloca = SOME region ==> copy_old_operand sa region /\
     eval_operand region s = SOME 0w /\ op_prov G region = NONE /\ op_taint tn region = {}` by
    metis_tac[] >>
  `off + 32*(1+word_size len) <= lo /\ a + 32*(1+word_size len) < dimword (:256) /\
   a + 32*(1+word_size len) <= s.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac[]
QED

Resume tuple_immutable_runtime_bytes_joint[physical_post]:
  `q.vs_memory = (immutable_transfers T T (n2w a) (n2w off) (1+word_size len) 0 s).vs_memory` by
    (qpat_assum `store_copy_normalize s q = _`
      (mp_tac o Q.AP_TERM `\r. r.vs_memory`) >>
     simp_tac (srw_ss()) [stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
  `((store_copy_normalize s q) with
      <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>) = s` by
    asm_rewrite_tac[immutableAssignStoreTheory.immutable_transfers_record_restore] >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory /\
   val_in_memory dtv vi off q.vs_memory /\
   immutable_value_bytes_rel dtv vi (mem_bytes_at off (type_memory_size dtv) q.vs_memory)` by
    asm_rewrite_tac[] >>
  `!p n. regions_disjoint p n off (type_memory_size dtv) ==>
    mem_bytes_at p n q.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt gen_tac >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_assum `!p len. _ \/ _ ==> mem_bytes_at p len _ = _`
       (qspecl_then [`p`,`n`] mp_tac) >> simp[]) >>
  `mem_bytes_at off (32 * (1+word_size len)) q.vs_memory =
   mem_bytes_at a (32 * (1+word_size len)) s.vs_memory` by
    (asm_rewrite_tac[] >> irule immutableDeployAssignTransferTheory.immutable_transfers_memory_prefix >>
     simp[] >> decide_tac) >>
  `!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==> val_in_memory dtv vi off mem` by
    (rpt strip_tac >> irule tuple_runtime_bytes_robust >> simp[] >>
     qexistsl_tac [`a`,`tn.t_mem`,`tf.t_mem`,`dty`,`s.vs_memory`,`q.vs_memory`,
                   `32*(1+word_size len)`,`stv`,`sty`,`get_tenv cx`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x. x IN tf.t_mem <=> _` (qspec_then `off+i` mp_tac) >>
     simp[] >> decide_tac) >>
  suspend "joint_post"
QED

Resume tuple_immutable_runtime_bytes_joint[joint_post]:
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_fmp = s.vs_fmp /\ q.vs_initial_fmp = s.vs_initial_fmp /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient` by
    (qpat_assum `(store_copy_normalize s q with <|vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp_tac (srw_ss()) [stmtSimStoreCopyTheory.store_copy_normalize_def,venom_state_component_equality]) >>
  `allocas_from lo q = allocas_from lo s /\ allocas_below_fmp q = allocas_below_fmp s` by
    (rewrite_tac[allocas_from_def,allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  `allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    asm_rewrite_tac[] >>
  `!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==> ptr_covers Gf tf p q n` by
    (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  `!x. ~(off <= x /\ x < off + type_memory_size dtv) ==>
       (x IN tf.t_mem <=> x IN tn.t_mem)` by
    (rpt strip_tac >> qpat_assum `!x. x IN tf.t_mem <=> _` (qspec_then `x` mp_tac) >>
     `~(off <= x /\ x < off + 32*(1+word_size len))` by decide_tac >> simp[]) >>
  qexistsl_tac [`q`,`Gf`,`tf`] >> asm_rewrite_tac[] >> conj_tac
  >- suspend "stmt_post" >>
  suspend "ghost_post"
QED

Resume tuple_immutable_runtime_bytes_joint[stmt_post]:
  rpt strip_tac >>
  `(q with vs_inst_idx := LENGTH sb.cs_current_insts) = q` by
    simp[venom_state_component_equality] >>
  `stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin
     (q with vs_inst_idx := LENGTH sb.cs_current_insts)` suffices_by
    simp[] >>
  `immutable_value_admissible dtv vi` by metis_tac[evaluated_immutable_admissible] >>
  `(q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `(store_copy_normalize s q with <|vs_memory := _; vs_immutables := _|>) = s` mp_tac >>
     simp_tac (srw_ss()) [stmtSimStoreCopyTheory.store_copy_normalize_def,
                         venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `q.vs_memory = _` kall_tac >>
  irule immutable_assign_suffix_stmt_post >> asm_rewrite_tac[] >>
  qexistsl_tac [`env`,`id`,`dtv`,`dty`,`off`,`vi`] >> asm_rewrite_tac[]
QED

Resume tuple_immutable_runtime_bytes_joint[ghost_post]:
  `ce.ce_module = NONE` by fs[body_inv_def,cenv_module_pins_def] >>
  `fin.scopes = st.scopes` by metis_tac[vyperPlaceFramesTheory.write_immutable_place_scopes] >>
  `!i. ~(off <= i /\ i < off + type_memory_size dtv) ==>
      mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> first_x_assum (irule o SIMP_RULE std_ss [regions_disjoint_def]) >> decide_tac) >>
  `!i. off <= i /\ i < off + type_memory_size dtv /\ i IN tf.t_mem ==>
      mem_dead_bytes (mem_bytes_at 0 lo q.vs_memory) off dtv i` by
    (`well_formed_type_value dtv` by metis_tac[evaluate_type_well_formed_type_value] >>
     rpt strip_tac >> irule tuple_immutable_prefix_interior_dead >>
     simp[] >> qexistsl_tac [`tf.t_mem`,`vi`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_state_rel H ctx fn ce cx st s`
    (mp_then Any mp_tac tuple_immutable_suffix_ghost_post) >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then irule >>
  qpat_x_assum `!x. x IN tf.t_mem <=> _` kall_tac >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`id`,`off`,`dtv`,`dty`] >> gs[] >> metis_tac[]) >>
  qexists_tac `sa` >> simp[]
QED

Finalise tuple_immutable_runtime_bytes_joint[local]

Theorem tuple_immutable_head_outside_old_alloca[local]:
  allocas_from lo s /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
  off+n <= lo /\ a <= i ==> ~(i < off+n)
Proof
  rw[allocas_from_def] >>
  res_tac >> decide_tac
QED

(* One immutable head, at the cursor where the whole tuple is already loaded.
   The window [p,p+k) is the original tuple snapshot, not the normalization
   buffer; it remains available at the returned cursor. *)
Theorem body_assign_tuple_immutable_head_joint:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env st /\
  cx.in_deploy /\ supported_immutable_type tops (src,id) = SOME dty /\
  ~cx_const_name cx (src,id) /\
  assignable_type (get_tenv cx) sty /\ type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv vi /\
  compile_tuple_store_all ce [sty] [BaseTarget (TopLevelNameTarget (src,id))] [op] sa = ((),sb) /\
  stmt_state_rel (H0 : (bool # 'a word # type_value) list # num list) ctx fn ce cx st s /\
  dead_lo_ok H0 D0 lo ce cx /\ ghost_inv_at D0 lo d ce cx st G tn s /\
  local_ptrs_reserved ce sa /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lo <= p /\ lo <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (if is_word_type sty then
     copy_old_operand sa op /\ eval_operand op s = SOME (typed_val_to_w256 stv vi) /\
     op_taint tn op = {}
   else ?root w. op = Var root /\ not_fresh_at sa root /\ lookup_var root s = SOME w /\
     ptr_covers G tn root s (type_memory_size stv) /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory stv vi (w2n w) mem) /\
     w2n w + type_memory_size stv <= s.vs_alloca_next /\
     p <= w2n w /\ w2n w + type_memory_size stv <= p+k /\
     (sty <> dty /\ ~is_bytestring_type dty ==>
       ?a len. a <= p /\ p+k <= a+len /\
         ((?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len)) \/
          (?name. local_region ce st.scopes s name a len)))) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?fin dtv off q Gq tq.
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    eval_target_place cx (TopLevelNameTarget (src,id)) st = (INL (ImmutablePlace src id []),st) /\
    write_place cx (ImmutablePlace src id []) vi st = (INL (),fin) /\
    (!tail. assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (src,id))) vi
      (st with gas_obs := tail) = (INL (),fin with gas_obs := tail)) /\
    fin.scopes = st.scopes /\ fin.gas_obs = st.gas_obs /\ fin.storage_trace = st.storage_trace /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK q,Gq,tq)) /\
    (!H : (bool # 'b word # type_value) list # num list.
      stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
      stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!(H : (bool # 'b word # type_value) list # num list) D.
      stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
      ghost_inv_at D lo d ce cx st G tn s ==> ghost_inv_at D lo d ce cx fin Gq tq q) /\
    (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==> val_in_memory dtv vi off mem) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s.vs_alloca_next <= q.vs_alloca_next /\ q.vs_call_ctx = s.vs_call_ctx /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP q.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s /\
      FLOOKUP Gq x = FLOOKUP G x /\ op_taint tq (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==> ptr_covers Gq tq x q cap) /\
    tq.t_stor = tn.t_stor /\ tq.t_trans = tn.t_trans /\
    mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory /\
    (!i. p <= i /\ i < p+k ==> (i IN tq.t_mem <=> i IN tn.t_mem)) /\
    (!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
      a <= i /\ i < a+sz /\ i IN tq.t_mem ==> i IN tn.t_mem) /\
    alloca_frame ce st sa s ce fin q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all immutableAssignMetadataTheory.immutable_target_place_state >> strip_tac >>
  drule_all immutableAssignMetadataTheory.immutable_assign_bare_global >> strip_tac >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_target_layout >>
  disch_then (qspec_then `compile_expr` strip_assume_tac) >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
  disch_then (qx_choose_then `dtv` strip_assume_tac) >>
  `off + type_memory_size dtv <= lo` by
    metis_tac[tuple_immutable_slot_span] >>
  drule_all immutableDeployAssignSourceFrameTheory.immutable_assign_source_lookup >> strip_tac >>
  drule_all bodyImmutableAugAssignStoreTheory.immutable_augassign_write_source >>
  disch_then (qspec_then `vi` assume_tac) >>
  qmatch_asmsub_abbrev_tac `write_place _ _ _ _ = (INL (),fin)` >>
  `fin.scopes = st.scopes /\ fin.gas_obs = st.gas_obs /\ fin.storage_trace = st.storage_trace` by
    (drule vyperPlaceFramesTheory.write_immutable_place_frame >> strip_tac >> simp[]) >>
  `!tail. assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (src,id))) vi
      (st with gas_obs := tail) = (INL (),fin with gas_obs := tail)` by
    (gen_tac >>
     `eval_target_place cx (TopLevelNameTarget (src,id)) (st with gas_obs := tail) =
       (INL (ImmutablePlace src id []),st with gas_obs := tail)` by
       (irule immutableAssignMetadataTheory.immutable_target_place_state >> simp[] >> metis_tac[]) >>
     drule_then (qspec_then `tail` assume_tac)
       bodyImmutableAugAssignExecTheory.immutable_write_place_gas_obs >>
     simp[Once evaluate_def, bind_def] >> gvs[]) >>
  Cases_on `is_word_type sty`
  >- ( `sty = dty` by metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
       `compile_store_at_loc ce.ce_imm_alloca (Lit (n2w off)) op (SOME LocCode) sa = ((),sb)` by
         (qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
          simp[compile_tuple_store_all_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
          Cases_on `compile_store_at_loc ce.ce_imm_alloca (Lit (n2w off)) op (SOME LocCode) sa` >>
          Cases_on `q` >> fs[]) >>
       suspend "word") >>
  `~is_word_type dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `compile_assign_value ce (Lit (n2w off)) LocCode op F NONE dty sty
      (type_memory_bytes ce dty) sa = ((),sb)` by
    (qpat_x_assum `compile_tuple_store_all _ _ _ _ _ = _` mp_tac >>
     simp[compile_tuple_store_all_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     Cases_on `compile_assign_value ce (Lit (n2w off)) LocCode op F NONE dty sty
       (type_memory_bytes ce dty) sa` >> Cases_on `q` >> simp[]) >>
  suspend "complex"
QED

Resume body_assign_tuple_immutable_head_joint[word]:
  gvs[] >>
  drule_all tuple_immutable_word_head_joint >>
  disch_then (qspecl_then [`lctx`,`explicit`,`PG`]
    (qx_choose_then `end_src` (qx_choose_then `q` (qx_choose_then `Gq`
      (qx_choose_then `tq` (map_every assume_tac o CONJUNCTS)))))) >>
  `end_src = fin` by
    (qpat_x_assum `write_place _ _ _ _ = (INL (),end_src)` mp_tac >> simp[]) >>
  qpat_x_assum `end_src = fin` SUBST_ALL_TAC >>
  `type_memory_size dtv = 32` by metis_tac[stmtSimDeclStoreTheory.typed_word_store] >>
  `off + 32 <= lo` by fs[] >>
  `regions_disjoint p k off 32` by
    (simp[regions_disjoint_def] >> decide_tac) >>
  `!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
     a <= i /\ i < a+sz /\ i IN tq.t_mem ==> i IN tn.t_mem` by simp[] >>
  qexistsl_tac [`q`,`Gq`,`tq`] >>
  asm_rewrite_tac[] >> simp[] >>
  irule immutableAssignComposeTheory.immutable_assign_suffix_alloca_frame >>
  simp[] >> qexistsl_tac [`H0`,`ctx`,`cx`,`fn`,`id`,`dtv`,`dty`,`off`] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume body_assign_tuple_immutable_head_joint[complex]:
  gvs[] >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room,alloca_room_next_lt] >>
  `0 < type_memory_size dtv` by
    metis_tac[immutableAssignRepresentationTheory.immutable_assign_widened_memory_positive] >>
  `0 < type_slot_size dtv` by fs[type_memory_size_slots] >>
  `0 < lo` by decide_tac >>
  `!base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
       copy_old_operand sa base /\ op_taint tn base = {} /\ op_prov G base = NONE` by
    (rpt strip_tac >> drule_all tuple_immutable_word_base >> simp[]) >>
  `type_memory_bytes ce dty = type_memory_size dtv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `w2n w + type_memory_size stv < dimword (:256) /\ lo <= w2n w /\
   type_memory_size dtv < dimword (:256) /\ lo <= s.vs_alloca_next /\
   w2n w + type_memory_size stv <= s.vs_alloca_next /\
   w2n w + type_memory_size stv <= p+k` by decide_tac >>
  `lookup_var root s = SOME (n2w (w2n w))` by simp[wordsTheory.n2w_w2n] >>
  `regions_disjoint p k off (type_memory_size dtv)` by
    (simp[regions_disjoint_def] >> decide_tac) >>
  Cases_on `is_bytestring_type dty`
  >- suspend "runtime" >>
  Cases_on `sty = dty`
  >- suspend "fixed" >>
  suspend "normalized"
QED

Resume body_assign_tuple_immutable_head_joint[runtime]:
  `is_bytestring_type sty` by metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  qpat_assum `ce.ce_module = NONE` (fn eq =>
    drule_all (REWRITE_RULE [eq] tuple_immutable_runtime_bytes_joint)) >>
  disch_then (qspecl_then [`lctx`,`explicit`,`d`,`PG`]
    (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tq`
      (map_every assume_tac o CONJUNCTS))))) >>
  `!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
     a <= i /\ i < a+sz /\ i IN tq.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `~(i < off + type_memory_size dtv)` by
       metis_tac[tuple_immutable_head_outside_old_alloca] >>
     qpat_assum `!x. ~(off <= x /\ x < off + type_memory_size dtv) ==> (x IN tq.t_mem <=> x IN tn.t_mem)`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `!i. p <= i /\ i < p+k ==> (i IN tq.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `~(i < off + type_memory_size dtv)` by decide_tac >>
     qpat_assum `!x. ~(off <= x /\ x < off + type_memory_size dtv) ==> (x IN tq.t_mem <=> x IN tn.t_mem)`
       (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_x_assum `!x. ~(off <= x /\ x < off + type_memory_size dtv) ==> (x IN tq.t_mem <=> x IN tn.t_mem)` kall_tac >>
  qexistsl_tac [`q`,`Gq`,`tq`] >>
  asm_rewrite_tac[] >> simp[] >>
  irule immutableAssignComposeTheory.immutable_assign_suffix_alloca_frame >>
  simp[] >> qexistsl_tac [`H0`,`ctx`,`cx`,`fn`,`id`,`dtv`,`dty`,`off`] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume body_assign_tuple_immutable_head_joint[fixed]:
  gvs[] >>
  `lookup_var root s = SOME (n2w (w2n w))` by simp[wordsTheory.n2w_w2n] >>
  `lo <= w2n w /\ lo <= s.vs_alloca_next /\
   w2n w + type_memory_size dtv < dimword (:256) /\
   w2n w + type_memory_size dtv <= s.vs_alloca_next` by decide_tac >>
  (* Keep the compiler capacity in the form expected by the fixed path. *)
  `compile_assign_value ce (Lit (n2w off)) LocCode (Var root) F NONE dty dty
       (type_memory_bytes ce dty) sa = ((),sb)` by simp[] >>
  qpat_assum `ce.ce_module = NONE` (fn eq =>
    drule_all (REWRITE_RULE [eq] tuple_immutable_fixed_stmt_path)) >>
  suspend "fixed_post"
QED

Resume body_assign_tuple_immutable_head_joint[normalized]:
  drule_all immutableDeployAssignRangesTheory.immutable_assign_copy_metadata >> strip_tac >>
  `dty <> sty` by metis_tac[] >>
  Q_TAC (C SUBGOAL_THEN assume_tac) `?a len. a <= p /\ p+k <= a+len /\
    ((?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len)) \/
     (?name. local_region ce st.scopes s name a len))`
  >- (qpat_assum `sty <> dty /\ ~is_bytestring_type dty ==> _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `ce.ce_module = NONE` (fn eq =>
    drule_all (REWRITE_RULE [eq] tuple_immutable_normalized_fixed_joint)) >>
  suspend "normalized_post"
QED

Resume body_assign_tuple_immutable_head_joint[fixed_post]:
  disch_then (qspecl_then [`lctx`,`explicit`,`d`,`PG`]
    (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tq`
      (map_every assume_tac o CONJUNCTS))))) >>
  `!aid a sz i. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,sz) /\
     a <= i /\ i < a+sz /\ i IN tq.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `~(i < off + type_memory_size dtv)` by
       metis_tac[tuple_immutable_head_outside_old_alloca] >>
     qpat_assum `!x. x IN tq.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `!i. p <= i /\ i < p+k ==> (i IN tq.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `~(i < off + type_memory_size dtv)` by decide_tac >>
     qpat_assum `!x. x IN tq.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_x_assum `!x. x IN tq.t_mem <=> _` kall_tac >>
  qexistsl_tac [`q`,`Gq`,`tq`] >>
  asm_rewrite_tac[] >> simp[] >>
  irule immutableAssignComposeTheory.immutable_assign_suffix_alloca_frame >>
  simp[] >> qexistsl_tac [`H0`,`ctx`,`cx`,`fn`,`id`,`dtv`,`dty`,`off`] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Resume body_assign_tuple_immutable_head_joint[normalized_post]:
  disch_then (qspecl_then [`lctx`,`explicit`,`d`,`PG`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Finalise body_assign_tuple_immutable_head_joint

Theorem tuple_flat_targets_success_scopes[local]:
  !ats vals src fin.
    EVERY (\g. ?bt. g = BaseTarget bt) ats /\
    assign_tuple_target_list cx ats vals src = (INL (),fin) ==>
    MAP FDOM fin.scopes = MAP FDOM src.scopes
Proof
  Induct_on `ats` >> Cases_on `vals`
  >- simp[Once evaluate_def,return_def]
  >- simp[Once evaluate_def,raise_def]
  >- simp[Once evaluate_def,raise_def] >>
  simp[Once assign_tuple_target_list_cons] >>
  rpt strip_tac >> Cases_on `r` >> gvs[] >>
  qpat_x_assum `assign_tuple_targets cx (BaseTarget _) _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,AllCaseEqs()] >> strip_tac >>
  imp_res_tac vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >>
  imp_res_tac vyperScopePreservationTheory.write_place_scopes_dom >>
  metis_tac[]
QED

(* Any other target list. *)
Theorem body_assign_tuple_other_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) /\
    ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule tuple_targets_typing >> strip_tac >>
  `supported_assignment tops bindings (TupleTarget gs) e` by
    gvs[supported_stmt_assigntuple] >>
  `supported_expr tops e /\
   EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                      | TupleTarget ts => F) gs` by
    (qpat_assum `supported_assignment tops bindings (TupleTarget gs) e` mp_tac >>
     simp[NoAsms, Once supported_assignment_def]) >>
  `cenv.ce_target CapMcopy` by metis_tac[bodySimStmtFactsTheory.body_inv_mcopy] >>
  `(EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy)` by simp[] >>
  rw[stmt_frag_full_def] >>
  drule_all tupleAssignPartsTheory.assign_tuple_targets_code_parts >>
  strip_tac >>
  `!D sa' sb' s' G' tn' t' Gf tf dst n.
     gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s',G',tn') [] (OK t',Gf,tf) /\
     typed_copy_state_frame sa' dst n s' t' /\
     ~t'.vs_halted /\ t'.vs_current_bb = sb'.cs_current_bb /\
     t'.vs_inst_idx = LENGTH sb'.cs_current_insts ==>
     typed_copy_effect ctx func sa' sb' s' t' dst n` by
    (rpt strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >> strip_tac >>
     drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
     gvs[placeMemoryCopyEffectTheory.typed_copy_effect_def,
         fragGasModeTheory.gas_marked_path_def, typed_copy_state_frame_def,
         typed_copy_frame_def, venom_state_component_equality] >> gvs[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `~supported_expr_exists (const_name_root cx) e` by
       (irule supported_expr_no_name_root >>
        metis_tac[body_inv_const_name_root]) >>
     `supported_program tops /\ get_module_code cx NONE = SOME tops /\
      (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target))` by
       gvs[body_inv_def] >>
     `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     irule stmt_expr_body_pre_alloc >>
     simp[] >> conj_tac
     >- gvs[supported_stmt_expr_exists_def] >>
     conj_tac >- gvs[stmt_exprs_ok_def,supported_stmt_expr_exists_def] >>
     conj_tac >- gvs[stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def] >>
     qexists_tac `[]` >> simp[] >>
     qpat_x_assum `call_evaluation_safe _ _` mp_tac >>
     simp[int_calls_stmt_def] >>
     metis_tac[call_evaluation_safe_append_right]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,su)` by
    simp[lower_value_def,comp_bind_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) _ = (shadow_op,shadow_su)` >>
  `shadow_op = op /\ gas_shadow_state su shadow_su` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
       gas_shadow_stmt_lower_value) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split] >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[NoAsms,gas_shadow_stmt_def,gas_shadow_assignment_def,stmt_env_def,
       declare_stmt_local_def,Once compile_stmt_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) _ = (shadow_vv,shadow_sc)` >>
  Cases_on `unwrap_value cenv shadow_vv shadow_sc` >>
  rename1 `unwrap_value _ shadow_vv _ = (op',su')` >>
  simp[] >> strip_tac >>
  `op' = op /\ su' = shadow_su` by
    gvs[lower_value_def,comp_bind_def] >>
  gvs[] >>
  Cases_on `compile_tuple_unpack cenv (lowered_value_type cenv e)
    (is_memory_view e /\ vv_location shadow_vv = SOME LocMemory)
    (MAP gas_shadow_assignment gs) op shadow_su` >>
  gvs[] >>
  rename1 `compile_tuple_unpack _ _ _ (MAP gas_shadow_assignment gs) _ _ = ((),shadow_sb)` >>
  `cs_extends shadow_su shadow_sb` by
    metis_tac[cj 4 ci_mono_return_helpers,ci_mono_def,pairTheory.SND] >>
  `cs_extends shadow_sa shadow_su` by
    metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code shadow_sa shadow_su shadow_func` by
    metis_tac[fn_has_code_split] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>>
  HEADGOAL (sg `?shadow_ss. gas_shadow_state ss shadow_ss /\
    compile_tuple_store_all cenv tys (MAP gas_shadow_assignment gs) elems shadow_ss =
      ((),shadow_sb) /\ fn_has_code shadow_ss shadow_sb shadow_func`) >>>
  HEADGOAL (
    `expr_type (gas_shadow_expr e) = TupleT tys /\
     lowered_value_type cenv (gas_shadow_expr e) = expr_type (gas_shadow_expr e)` by
      simp[gasShadowCompilePureTheory.gas_shadow_lowered_value_type]) >>>
  HEADGOAL (
    qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
      (assume_tac o PURE_REWRITE_RULE [gas_shadow_stmt_def,gas_shadow_assignment_def]) >>
    mp_tac (Q.SPECL [`cenv`,`lctx`,`ret_ty`,`MAP gas_shadow_assignment gs`,
      `gas_shadow_expr e`,`tys`,`shadow_sa`,`shadow_sb`,`cenv`,`shadow_func`]
      tupleAssignPartsTheory.assign_tuple_targets_code_parts) >>
    (impl_tac >- simp[]) >>
    simp[NoAsms] >>
    disch_then (qx_choosel_then [`svv`,`ssc`,`sop`,`ssu`,`sstaged`,`ssl`,`selems`,`sss`]
      (map_every assume_tac o CONJUNCTS))) >>>
  HEADGOAL (
    `svv = shadow_vv /\ ssc = shadow_sc` by
      (qpat_assum `compile_expr cenv _ (gas_shadow_expr e) shadow_sa = (shadow_vv,shadow_sc)` mp_tac >>
       qpat_assum `compile_expr cenv _ (gas_shadow_expr e) shadow_sa = (svv,ssc)`
         (fn eq => simp[NoAsms,eq]))) >>>
  HEADGOAL (
    `shadow_vv = vv` by
      (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `TupleT tys`, `e` |-> `e`]
         gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr) >>
       rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
       disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[])) >>>
  HEADGOAL (
    `sop = op /\ ssu = shadow_su` by
      (qpat_assum `svv = shadow_vv` (fn vv_eq =>
       qpat_assum `ssc = shadow_sc` (fn sc_eq =>
       qpat_assum `unwrap_value cenv shadow_vv shadow_sc = (op,shadow_su)` (fn code =>
       qpat_assum `unwrap_value cenv svv ssc = (sop,ssu)` mp_tac >>
       simp[NoAsms,vv_eq,sc_eq,code]))))) >>>
  HEADGOAL (
    qpat_assum `svv = shadow_vv` (fn v1 =>
    qpat_assum `shadow_vv = vv` (fn v2 =>
    qpat_assum `sop = op` (fn ptr =>
    qpat_assum `ssu = shadow_su` (fn st =>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [v1,v2,ptr,st])))))) >>>
  HEADGOAL (
    qpat_assum `(if _ then _ else _) su = (staged,sl)` (fn stage =>
      let val f = rator (lhs (concl stage)) in
        Q.SUBGOAL_THEN `gas_shadow_compiles ^f ^f` assume_tac
      end)
    >- (IF_CASES_TAC >> simp[comp_ignore_bind_def,
           gasShadowStateTheory.gas_shadow_compiles_bind,
           gasShadowStateTheory.gas_shadow_compiles_return,
           gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
           gasShadowStateTheory.gas_shadow_compiles_emit_void])) >>>
  HEADGOAL (
    `sstaged = staged /\ gas_shadow_state sl ssl` by
      (qpat_assum `gas_shadow_compiles _ _`
         (qspecl_then [`su`,`shadow_su`] mp_tac o
          REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[])) >>>
  HEADGOAL (
    `selems = elems /\ gas_shadow_state ss sss` by
      (mp_tac (Q.SPECL [`tys`,`staged`,`0`]
         (Q.INST [`cenv` |-> `cenv`] gasShadowCompileStmtOpsTheory.gas_shadow_compiles_tuple_load_all)) >>
       rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
       disch_then (qspecl_then [`sl`,`ssl`] mp_tac) >>
       qpat_assum `sstaged = staged` (fn op_eq =>
       qpat_assum `compile_tuple_load_all cenv sstaged tys 0 ssl = (selems,sss)` (fn shadow =>
       qpat_assum `compile_tuple_load_all cenv staged tys 0 sl = (elems,ss)` (fn real =>
       qpat_assum `gas_shadow_state sl ssl` (fn rel =>
         simp[NoAsms,PURE_REWRITE_RULE [op_eq] shadow,real,rel])))))) >>>
  HEADGOAL (
    qexists_tac `sss` >>
    qpat_assum `selems = elems` (fn elems =>
      qpat_assum `compile_tuple_store_all cenv tys (MAP gas_shadow_assignment gs) selems sss = _`
        (assume_tac o PURE_REWRITE_RULE [elems])) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_x_assum `expr_sim_full _ _ _ _ _ _`
      (drule_all_then strip_assume_tac o REWRITE_RULE [expr_sim_full_def]) >>
    qpat_x_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ _ _`
      (strip_assume_tac o REWRITE_RULE [gasOutcomeFullTheory.gas_outcome_full_def])) >>>
  ROTATE_LT 1 >>>
  HEADGOAL (Cases_on `r` >> fs[fragExecTheory.exit_result_def]) >>>
  HEADGOAL (
    `post_value_type cenv e = TupleT tys` by
      metis_tac[loweringPostsTheory.post_value_type_lowered] >>
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
       ee.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    rename1 `res = INL source_v`) >>>
  HEADGOAL (
    qpat_assum `!tail. _ = (res,ee with gas_obs := tail)`
      (qspec_then `[]` assume_tac) >>
    drule_at (Pat `bind _ _ _ = _`)
      (REWRITE_RULE [ETA_THM] bodySimStmtFactsTheory.expr_body_pre_eval) >>
    disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac) >>>
  HEADGOAL (`?obs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
       (INL source_v,ee with gas_obs := [])` by
       (qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
        qpat_x_assum `!tail. _ = (res,ee with gas_obs := tail)` kall_tac >> gvs[])) >>>
  HEADGOAL (drule bodyPtrBopTypedSourceTheory.bop_typed_source_witness >>
    disch_then (qspecl_then [`source_v`,`ee with gas_obs := []`] mp_tac) >>
    (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
    qpat_assum `expr_type e = TupleT tys` SUBST_ALL_TAC >>
    drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
    `?vs. source_v = ArrayV (TupleV vs) /\ values_have_types tvs vs` by
      (Cases_on `source_v` >> gvs[vyperTypingTheory.value_has_type_def] >>
       rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
       Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def]) >>
    gvs[]) >>>
  HEADGOAL (
    `LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs` by
      (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
       irule exprSimHypsTheory.expr_sim_inv_memory_size >> metis_tac[]) >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def])) >>>
  HEADGOAL (
    qpat_assum `post_value_type cenv e = TupleT tys`
      (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
    qpat_assum `expr_val_rel _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
    `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
      (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
         (mp_tac o Q.SPEC `TupleTV tvs` o REWRITE_RULE [expr_val_at_def]) >>
       simp[is_word_type_def]) >>
    `!mem. mem_agree_outside tn'.t_mem v.vs_memory mem ==>
       val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) mem` by
      (qpat_assum `ptr_val_ok _ _ _ _ _ _ _`
         (strip_assume_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def,is_word_type_def]) >>
       qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
         (mp_tac o Q.SPECL [`TupleTV tvs`,`w`] o REWRITE_RULE [ptr_mem_ok_def]) >>
       simp[])) >>>
  HEADGOAL (
    `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
    `SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs` by
      (drule tupleTypedLoadTheory.tuple_prefix_sizes >>
       disch_then (qspec_then `LENGTH tys` mp_tac) >>
       simp[valueEncodingProofsTheory.type_memory_size_list_sum])) >>>
  HEADGOAL (
    Q.SUBGOAL_THEN `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP v.vs_allocas aid = SOME (b,sz) /\ aid < su.cs_next_id /\
        b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
        (!n lb lsz. local_region cenv ee.scopes v n lb lsz ==>
          b + sz <= lb \/ lb + lsz <= b)) \/
      (?n b sz. local_region cenv ee.scopes v n b sz /\ b <= w2n w /\
        w2n w + type_memory_size_list tvs <= b + sz /\
        local_path_at cenv cx n (w2n w - b) (TupleTV tvs))` (mk_asm "rhs_window")) >>>
  HEADGOAL (
    qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
      (qspec_then `TupleTV tvs` mp_tac o PURE_REWRITE_RULE [expr_val_at_def]) >>
    simp[is_word_type_def,val_footprint_def,valueEncodingTheory.type_memory_size_def,
      local_val_at_def] >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>>
  HEADGOAL (sg `!todo tys1 tvs1 vs1 ops1 k p cur shadow_cur src u Gu tu.
    LIST_REL (\g ty. well_typed_atarget env g ty) todo tys1 /\
    LENGTH ops1 = LENGTH tys1 /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys1 tvs1 /\
    values_have_types tvs1 vs1 /\ tys1 = DROP k tys /\
    tvs1 = DROP k tvs /\ vs1 = DROP k vs /\
    EVERY (assignable_type (get_tenv cx)) tys1 /\
    EVERY (\g. case g of BaseTarget bt =>
      supported_target tops bindings bt /\ target_indices_pre cenv cx env bt
      | TupleTarget ts => F) todo /\
    body_tuple_targets_full_ok cx todo vs1 /\
    expr_sim_inv cenv cx env src /\ src with gas_obs := [] = src /\
    gas_admissible (assign_tuple_target_list cx todo vs1) (stmt_res_ok lctx) src /\
    call_evaluation_safe cx (int_calls_atargets todo) /\
    compile_tuple_store_all cenv tys1 todo ops1 cur = ((),sb) /\
    compile_tuple_store_all cenv tys1 (MAP gas_shadow_assignment todo) ops1 shadow_cur =
      ((),shadow_sb) /\ gas_shadow_state cur shadow_cur /\
    fn_has_code cur sb func /\ fn_has_code shadow_cur shadow_sb shadow_func /\
    sa.cs_next_id <= cur.cs_next_id /\ sa.cs_next_var <= cur.cs_next_var /\
    local_ptrs_reserved cenv cur /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x) /\
    ~block_is_terminated cur /\ ~u.vs_halted /\
    u.vs_current_bb = cur.cs_current_bb /\ u.vs_inst_idx = LENGTH cur.cs_current_insts /\
    return_buf_frame d cenv cur u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_no_wrap inst z) /\
    storage_trace_domain cx st0 src.storage_trace /\
    (!H. valid_horizon cx st0 H src.storage_trace ==>
      stmt_state_rel H ctx func cenv cx src u /\ storage_well_formed_on cx src (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx src Gu tu u) /\
    lo <= p /\ p + type_memory_size_list tvs <= u.vs_alloca_next /\
    (type_memory_size_list tvs = 0 \/
     (?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ aid < cur.cs_next_id /\
       b <= p /\ p + type_memory_size_list tvs <= b + sz /\
       (!n a len. local_region cenv src.scopes u n a len ==>
         b + sz <= a \/ a + len <= b)) \/
     (?n b sz. local_region cenv src.scopes u n b sz /\ b <= p /\
       p + type_memory_size_list tvs <= b + sz /\
       local_path_at cenv cx n (p-b) (TupleTV tvs))) /\
    (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem) /\
    (!i. i < LENGTH tys1 ==>
      ?x. EL i ops1 = Var x /\ not_fresh_at cur x /\ op_taint tu (Var x) = {} /\
          if is_word_type (EL i tys1) then
            lookup_var x u = SOME (typed_val_to_w256 (EL i tvs1) (EL i vs1)) /\
            op_prov Gu (Var x) = NONE
          else lookup_var x u =
                 SOME (n2w (p + SUM (MAP type_memory_size (TAKE (k+i) tvs)))) /\
               ptr_covers Gu tu x u (type_memory_size (EL i tvs1))) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gu x = FLOOKUP G0 x /\ op_taint tu (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv src u /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tu.t_mem ==> i IN tn0.t_mem) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (assign_tuple_target_list cx todo vs1) (src,u,Gu,tu)
      (\H res ee G tn t. ?cenv''.
        stmt_lands lctx sb res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
        cenv_top_ext cenv cenv'' ee.scopes /\ stmt_state_rel H ctx func cenv'' cx ee t /\
        storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv'' sb t /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 cenv'' ee t /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
          off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
      (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s \/ (?ir. r = IntRet ir s) ==> allocas_below_fmp s))`) >>>
  HEADGOAL (Induct_on `todo`) >>>
  HEADGOAL (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
    qpat_x_assum `type_memory_size_list tvs = 0 \/ _` kall_tac >>
    qpat_x_assum `tys1 = DROP k tys` kall_tac >>
    qpat_x_assum `tvs1 = DROP k tvs` kall_tac >>
    qpat_x_assum `vs1 = DROP k vs` kall_tac) >>>
  HEADGOAL (gvs[vyperTypeDefaultsTheory.values_have_types_LIST_REL,
    compile_tuple_store_all_def,comp_return_def]) >>>
  HEADGOAL (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure) >>>
  HEADGOAL (reverse conj_tac >- simp[]) >>>
  HEADGOAL (qexistsl [`Gu`,`src`,`INL ()`,`u`,`tu`]) >>>
  HEADGOAL (conj_tac >- simp[Once evaluate_def,return_def]) >>>
  HEADGOAL (rpt strip_tac >- simp[gas_origin_ptr_path_rules]) >>>
  HEADGOAL (BETA_TAC >> qexists `cenv` >>
    simp[loweringPostsTheory.stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_x_assum `!tys1 tvs1 vs1 ops1 k p cur shadow_cur src u Gu tu.
      _ ==> gas_outcome_full _ _ _ _ (assign_tuple_target_list _ todo vs1) _ _ _`
      (mk_asm "suffix_ih") >>
    rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    Cases_on `h` >> qpat_x_assum `EVERY _ (_ :: todo)` mp_tac >>
    simp[NoAsms] >> strip_tac) >>>
  HEADGOAL (
    Cases_on `tys1` >>
    qpat_x_assum `LIST_REL (\g ty. well_typed_atarget env g ty) (_ :: todo) _` mp_tac >>
    simp[NoAsms,listTheory.LIST_REL_def] >> strip_tac) >>>
  HEADGOAL (
    Cases_on `tvs1` >> qpat_x_assum `LIST_REL (\ty tv. evaluate_type _ ty = SOME tv) (_ :: _) _` mp_tac >>
    simp[NoAsms,listTheory.LIST_REL_def] >> strip_tac) >>>
  HEADGOAL (
    Cases_on `vs1` >> qpat_x_assum `values_have_types (_ :: _) _` mp_tac >>
    simp[NoAsms,vyperTypeDefaultsTheory.values_have_types_LIST_REL,listTheory.LIST_REL_def] >> strip_tac) >>>
  HEADGOAL (
    Cases_on `ops1` >> qpat_x_assum `LENGTH _ = LENGTH (_ :: _)` mp_tac >>
    simp[NoAsms] >> strip_tac) >>>
  HEADGOAL (
    rename1 `compile_tuple_store_all cenv (sty::tys_tail) (BaseTarget bt::todo) (op0::ops_tail) cur = ((),sb)` >>
    rename1 `LIST_REL value_has_type tvs_tail vs_tail` >>
    rename1 `value_has_type stv vi`) >>>
  HEADGOAL (
    qpat_assum `sty :: tys_tail = DROP k tys`
      (mp_then Any strip_assume_tac fragExecTheory.DROP_EQ_CONS o SYM)) >>>
  HEADGOAL (
    qpat_x_assum `call_evaluation_safe cx (int_calls_atargets (_ :: todo))`
      (mp_tac o REWRITE_RULE [int_calls_atarget_def]) >>
    disch_then (fn th =>
      mp_then Any assume_tac call_evaluation_safe_append_left th >>
      mp_then Any assume_tac call_evaluation_safe_append_right th)) >>>
  HEADGOAL (
    qpat_assum `compile_tuple_store_all cenv (sty::_) (BaseTarget bt::todo) _ cur = _`
      (mp_then Any (qx_choose_then `sm` strip_assume_tac) tuple_store_base_cons)) >>>
  HEADGOAL (
    qpat_x_assum `compile_tuple_store_all _ _ (MAP gas_shadow_assignment (_ :: todo)) _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [listTheory.MAP,gasShadowTheory.gas_shadow_assignment_def]) >>
    qpat_assum `compile_tuple_store_all _ (sty::_) (BaseTarget _ :: MAP gas_shadow_assignment todo) _ shadow_cur = _`
      (mp_then Any (qx_choose_then `shadow_sm` strip_assume_tac) tuple_store_base_cons)) >>>
  HEADGOAL (
    `gas_shadow_state sm shadow_sm` by
      (qspecl_then [`[sty]`,`[BaseTarget bt]`,`[op0]`] mp_tac
         (Q.INST [`cenv` |-> `cenv`] gasShadowCompileStmtHelpersTheory.gas_shadow_compile_tuple_store_all) >>
       rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
       disch_then (qspecl_then [`cur`,`shadow_cur`] mp_tac) >>
       simp[gasShadowTheory.gas_shadow_assignment_def])) >>>
  HEADGOAL (
    qpat_assum `compile_tuple_store_all cenv [_] [_] [_] cur = ((),sm)`
      (mp_then Any strip_assume_tac tupleAssignPartsTheory.tuple_target_stores_growth) >>
    qpat_assum `compile_tuple_store_all cenv tys_tail todo ops_tail sm = ((),sb)`
      (mp_then Any strip_assume_tac tupleAssignPartsTheory.tuple_target_stores_growth) >>
    `fn_has_code cur sm func /\ fn_has_code sm sb func` by
      (irule fn_has_code_split >> simp[])) >>>
  HEADGOAL (
    qpat_assum `compile_tuple_store_all cenv [_] [_] [_] shadow_cur = ((),shadow_sm)`
      (mp_then Any strip_assume_tac tupleAssignPartsTheory.tuple_target_stores_growth) >>
    qpat_assum `compile_tuple_store_all cenv tys_tail (MAP gas_shadow_assignment todo) ops_tail shadow_sm = ((),shadow_sb)`
      (mp_then Any strip_assume_tac tupleAssignPartsTheory.tuple_target_stores_growth) >>
    `fn_has_code shadow_cur shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
      (irule fn_has_code_split >> simp[])) >>>
  HEADGOAL (
    qpat_assum `!i. i < LENGTH (sty::tys_tail) ==> ?x. _ /\ not_fresh_at cur x /\ _`
      (qspec_then `0` (strip_assume_tac o SRULE [])) >>
    rename1 `op0 = Var xmem` >>
    qpat_assum `body_tuple_targets_full_ok cx (BaseTarget bt::todo) (vi::vs_tail)`
      (strip_assume_tac o REWRITE_RULE [body_tuple_target_full_ok_def])) >>>
  HEADGOAL (Cases_on `immutable_root cx bt`) >>>
  HEADGOAL (sg `?ns id. bt = TopLevelNameTarget (ns,id) /\
                         IS_SOME (supported_immutable_type tops (ns,id))`) >>>
  HEADGOAL (
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
      (qpat_assum `body_inv tops ctx cenv cx` mp_tac >> simp[NoAsms,body_inv_def]) >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`ALL_DISTINCT (FLAT _)`, `body_inv tops ctx cenv cx`,
       `immutable_root cx bt`, `supported_target tops bindings bt`] >>
    POP_ASSUM_LIST kall_tac >>
    namedCases_on `bt` ["name", "nsid", "b key", "b fld"] >>
    simp[supportedStmtsTheory.supported_target_def]) >>>
  HEADGOAL (simp[targetPlaceSimTheory.immutable_root_def,targetPlaceSimTheory.target_root_def]) >>>
  HEADGOAL (PairCases_on `nsid` >> simp[] >> rpt strip_tac >>
    metis_tac[augAssignFullTargetRoutesTheory.augassign_scalar_target_route]) >>>
  HEADGOAL (Cases_on `b` >> simp[] >> rpt strip_tac >>
    metis_tac[bodyAugPlaceTargetTheory.aug_place_legacy_subscript_info,
      bodyAugPlaceTargetTheory.aug_place_supported_root_not_immutable, optionTheory.IS_SOME_EXISTS]) >>>
  HEADGOAL (Cases_on `b` >> simp[] >> rpt strip_tac >>
    metis_tac[bodyAugPlaceTargetTheory.aug_place_legacy_field_info,
      bodyAugPlaceTargetTheory.aug_place_supported_root_not_immutable, optionTheory.IS_SOME_EXISTS]) >>>
  HEADGOAL (
    qpat_x_assum `bt = TopLevelNameTarget _` SUBST_ALL_TAC >>
    qpat_x_assum `IS_SOME (supported_immutable_type tops (ns,id))`
      (qx_choose_then `dty` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS])) >>>
  HEADGOAL (
    `type_place_target env (TopLevelNameTarget (ns,id)) = SOME (Type sty)` by
      (qpat_assum `well_typed_atarget env _ sty` mp_tac >>
       simp[NoAsms,well_typed_atarget_def,well_typed_target_def]) >>
    `supported_variable_decl tops (ns,id) = SOME (Private,Immutable,dty,NONE)` by
      (qpat_assum `supported_immutable_type _ _ = SOME _` mp_tac >>
       simp[NoAsms,supportedDeclsTheory.supported_immutable_type_def,AllCaseEqs()] >>
       strip_tac >> gvs[])) >>>
  HEADGOAL (
    drule_then strip_assume_tac bodyStorageMetadataTheory.supported_variable_decl_mem >>
    `get_module_code cx NONE = SOME tops` by
      (qpat_assum `body_inv tops ctx cenv cx` mp_tac >> simp[NoAsms,body_inv_def]) >>
    `env_context_consistent env cx` by
      (qpat_assum `expr_sim_inv cenv cx env src` mp_tac >>
       simp[NoAsms,expr_sim_inv_def,vyperTypeInvariantsTheory.env_consistent_def]) >>
    qpat_assum `env_context_consistent env cx`
      (strip_assume_tac o REWRITE_RULE [vyperTypeInvariantsTheory.env_context_consistent_def])) >>>
  HEADGOAL (
    `FLOOKUP env.bare_globals (ns,id) = SOME dty` by
      (qpat_assum `bare_globals_complete _ _`
        (mp_tac o REWRITE_RULE [vyperTypeInvariantsTheory.bare_globals_complete_def]) >>
       disch_then (qspecl_then [`ns`,`tops`,`Private`,`Immutable`,`id`,`dty`,`NONE`] mp_tac) >>
       simp[]) >>
    `FLOOKUP env.bare_global_assignable (ns,id) = SOME sty` by
      (qpat_assum `type_place_target env _ = SOME (Type sty)` mp_tac >>
       simp[NoAsms,vyperTypeEnvTheory.type_place_target_TopLevelNameTarget] >> simp[])) >>>
  HEADGOAL (
    `cx.in_deploy /\ dty = sty` by
      (qpat_assum `bare_global_assignable_complete _ _`
        (mp_tac o REWRITE_RULE [vyperTypeInvariantsTheory.bare_global_assignable_complete_def]) >>
       Cases_on `cx.in_deploy` >> simp[]
       >- (disch_then (qspecl_then [`ns`,`tops`,`Private`,`id`,`dty`,`NONE`] mp_tac) >>
           simp[] >> metis_tac[]) >>
       strip_tac >> gvs[])) >>>
  HEADGOAL (qpat_x_assum `dty = sty` SUBST_ALL_TAC) >>>
  HEADGOAL (
    `~cx_const_name cx (ns,id)` by
      (strip_tac >> drule_all bodySimTheory.body_inv_const_name_decl >> strip_tac >> gvs[]) >>
    `assignable_type (get_tenv cx) sty` by
      (qpat_assum `EVERY (assignable_type _) (sty::_)` mp_tac >> simp[NoAsms])) >>>
  HEADGOAL (
    `~block_is_terminated sm` by
      (drule_all immutableDeployAssignFactsTheory.immutable_assign_target_layout >>
       disch_then (qspec_then `compile_expr` strip_assume_tac) >>
       rename1 `compile_get_target_ptr _ _ _ = return (Lit (n2w off),_,_)` >>
       `compile_assign_value cenv (Lit (n2w off)) LocCode op0 (is_word_type sty)
          NONE sty sty (type_memory_bytes cenv sty) cur = ((),sm)` suffices_by
          (disch_then (mp_then Any ACCEPT_TAC immutableAssignOpenTheory.immutable_assign_loccode_open)) >>
       qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] cur = ((),sm)` mp_tac >>
       qpat_x_assum `compile_tuple_store_all _ (_::_) (_::_) (_::_) cur = _` kall_tac >>
       Cases_on `is_word_type sty` >>
       simp[compile_tuple_store_all_def,comp_ignore_bind_def,comp_return_def,
         immutableCopyExecutionTheory.immutable_comp_bind_cases,
         compile_assign_value_def,compile_store_at_loc_def])) >>>
  HEADGOAL (
    qpat_assum `!H. valid_horizon cx st0 H src.storage_trace ==> _`
      (qspec_then `storage_trace_horizon src.storage_trace` mp_tac) >>
    (impl_tac >- simp[GSYM vyperStorageFootprintTheory.storage_trace_domain_def]) >>
    strip_tac) >>>
  HEADGOAL (
    `allocas_from lo u /\ lo <= u.vs_alloca_next` by
      (qpat_assum `ghost_inv_at _ _ _ _ _ src Gu tu u`
        (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
    `u.vs_alloca_next < dimword (:256)` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx src u`
        (mp_then Any assume_tac stateRelProjTheory.stmt_state_rel_alloca_room) >>
       drule_then ACCEPT_TAC alloca_room_next_lt)) >>>
  HEADGOAL (
    qpat_assum `CONS stv tvs_tail = DROP k tvs`
      (strip_assume_tac o MATCH_MP fragExecTheory.DROP_EQ_CONS o SYM) >>
    qpat_assum `CONS vi vs_tail = DROP k vs`
      (strip_assume_tac o MATCH_MP fragExecTheory.DROP_EQ_CONS o SYM)) >>>
  HEADGOAL (
    `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size stv <=
       type_memory_size_list tvs` by
      (qpat_assum `EL k tvs = stv` (SUBST1_TAC o SYM) >>
       pure_rewrite_tac [valueEncodingProofsTheory.type_memory_size_list_sum] >>
       irule abiEncoderInputTheory.abi_encoder_prefix_sum_bound >> simp[]) >>
    `p + SUM (MAP type_memory_size (TAKE k tvs)) < dimword (:256)` by decide_tac) >>>
  HEADGOAL (
    qpat_assum `values_have_types tvs vs`
      (assume_tac o MATCH_MP vyperTypingTheory.values_have_types_length) >>
    sg `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
       val_in_memory stv vi (p + SUM (MAP type_memory_size (TAKE k tvs))) mem`) >>>
  HEADGOAL (qx_gen_tac `mm` >> disch_tac) >>>
  HEADGOAL (
    `tuple_in_memory vs tvs p mm` by
      (rewrite_tac [GSYM valueEncodingPropsTheory.val_in_memory_tuple] >>
       qpat_assum `!m. mem_agree_outside tu.t_mem u.vs_memory m ==> _`
         irule >> simp[])) >>>
  HEADGOAL (
    map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
      [`EL k tvs = stv`, `EL k vs = vi`]) >>>
  HEADGOAL (irule tupleMemoryLayoutTheory.tuple_in_memory_element >> simp[]) >>>
  HEADGOAL (
    drule_at (Pat `compile_tuple_store_all _ [_] [_] [_] cur = ((),sm)`)
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
        body_assign_tuple_immutable_head_joint)) >>>
  HEADGOAL (disch_then (drule_at (Pat `stmt_state_rel _ ctx func cenv cx src u`))) >>>
  HEADGOAL (disch_then (drule_at (Pat `ghost_inv_at _ lo d cenv cx src Gu tu u`))) >>>
  HEADGOAL (disch_then (drule_at (Pat `fn_has_code cur sm func`))) >>>
  HEADGOAL (disch_then (qspecl_then [`vi`, `tops`, `stv`, `p`, `lctx`,
      `type_memory_size_list tvs`, `gas_explicit_sites ctx shadow_ctx`,
      `env`, `sty`, `PG`] mp_tac)) >>>
  HEADGOAL (impl_tac) >>>
  HEADGOAL (simp[]) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type sty then lookup_var xmem u = _ /\ _ else _`
      mp_tac >> ASM_CASES_TAC ``is_word_type sty`` >>
    simp[exprSimCopyTheory.copy_old_operand_def,eval_operand_def]) >>>
  HEADGOAL (
    disch_then (qx_choose_then `fin` (qx_choose_then `dtv`
      (qx_choose_then `imm_off` (qx_choose_then `q`
        (qx_choose_then `Gq` (qx_choose_then `tq` strip_assume_tac))))))) >>>
  HEADGOAL (
    `fin with gas_obs := [] = fin` by
      (qpat_assum `src with gas_obs := [] = src`
         (mp_tac o ONCE_REWRITE_RULE [vyperStateTheory.evaluation_state_component_equality]) >>
       simp[vyperStateTheory.evaluation_state_component_equality]) >>
    `assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (ns,id))) vi src = (INL (),fin)` by
      (qpat_assum `!tail. assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (ns,id))) vi
          (src with gas_obs := tail) = _`
         (qspec_then `[]` mp_tac) >>
       qpat_assum `src with gas_obs := [] = src` (fn th => rewrite_tac[th]) >>
       qpat_assum `fin with gas_obs := [] = fin` (fn th => rewrite_tac[th])) >>
    `body_tuple_targets_full_ok cx todo vs_tail` by
      (first_x_assum irule >> qexistsl_tac [`src`,`()`,`fin`] >> simp[]) >>
    asm "suffix_ih" (qspecl_then
      [`tys_tail`,`tvs_tail`,`vs_tail`,`ops_tail`,`SUC k`,`p`,`sm`,`shadow_sm`,`fin`,`q`,`Gq`,`tq`] mp_tac) >>
    impl_tac) >>>
  HEADGOAL (
    `cur.cs_next_id <= sm.cs_next_id` by
      (qspecl_then [`cenv`,`[sty]`,`[BaseTarget (TopLevelNameTarget (ns,id))]`,`[op0]`,`cur`] mp_tac
        (cj 5 stmtLoweringMonoTheory.ci_mono_list_helpers) >> simp[ci_mono_def]) >>
    `sa.cs_next_id <= sm.cs_next_id` by decide_tac >>
    `sa.cs_next_var <= sm.cs_next_var` by
      (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `cur.cs_next_var` >> simp[])) >>>
  HEADGOAL (
    `local_ptrs_reserved cenv sm` by
      (irule local_ptrs_reserved_next_var >> qexists `cur` >> simp[])) >>>
  HEADGOAL (
    `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
      (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists `cur` >> conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x`
         (drule_then ACCEPT_TAC))) >>>
  HEADGOAL (
    `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
      (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists `cur` >> conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cur x`
         (drule_then ACCEPT_TAC))) >>>
  HEADGOAL (
    `return_buf_frame d cenv sm q` by
      (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl_tac [`cenv`,`u`,`cur`] >>
       simp[] >> rpt strip_tac >>
       qpat_assum `!x. not_fresh_at cur x ==> lookup_var x q = lookup_var x u /\ _`
         drule >> simp[])) >>>
  HEADGOAL (
    qpat_assum `stmt_state_rel _ ctx func cenv cx src u`
      (assume_tac o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv) >>
    qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (u,Gu,tu) [] (OK q,Gq,tq)`
      (qspec_then `DF (storage_trace_horizon src.storage_trace)` assume_tac) >>
    `alloca_history func q` by
      (qpat_assum `gas_origin_ptr_path _ (u,Gu,tu) [] (OK q,Gq,tq)`
        (mp_then Any irule bodyFullPathHistoryTheory.body_full_path_alloca_history) >> simp[])) >>>
  HEADGOAL (sg `!fn inst z. frag_reachable ctx func q fn inst z ==> dalloca_no_wrap inst z`) >>>
  HEADGOAL (
    qpat_assum `body_inv tops ctx cenv cx`
      (mp_then Any mp_tac bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap)) >>>
  HEADGOAL (
    disch_then (qspecl_then [`func`,`q`] assume_tac) >> rpt strip_tac >>
    rename1 `frag_reachable ctx func q rf ri rz` >>
    qpat_assum `!fn inst u. MEM func ctx.ctx_functions /\ frag_reachable ctx func q fn inst u ==> _`
      (qspecl_then [`rf`,`ri`,`rz`] mp_tac) >>
    impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then ACCEPT_TAC) >>>
  HEADGOAL (sg `!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
       val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`) >>>
  HEADGOAL (rpt strip_tac >>
    irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
    simp[exprSimPropsTheory.val_footprint_le] >>
    qexistsl_tac [`u.vs_memory`,`q.vs_memory`,`type_memory_size_list tvs`,
                  `p`,`tu.t_mem`,`tq.t_mem`] >>
    simp[valueEncodingTheory.type_memory_size_def]) >>>
  HEADGOAL (
    qpat_assum `val_wf (TupleTV tvs) (ArrayV (TupleV vs))`
      (mp_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
    simp[valueEncodingTheory.type_memory_size_def]) >>>
  HEADGOAL (simp[vyperTypeDefaultsTheory.values_have_types_LIST_REL]) >>>
  HEADGOAL (
    qpat_assum `!fn inst z. frag_reachable ctx func q fn inst z ==> dalloca_no_wrap inst z`
      (fn th => rewrite_tac[th])) >>>
  HEADGOAL (sg `!i. i < LENGTH tys_tail ==>
      ?x. EL i ops_tail = Var x /\ not_fresh_at sm x /\ op_taint tq (Var x) = {} /\
          if is_word_type (EL i tys_tail) then
            lookup_var x q = SOME (typed_val_to_w256 (EL i tvs_tail) (EL i vs_tail)) /\
            op_prov Gq (Var x) = NONE
          else lookup_var x q =
                 SOME (n2w (p + SUM (MAP type_memory_size (TAKE (SUC k+i) tvs)))) /\
               ptr_covers Gq tq x q (type_memory_size (EL i tvs_tail))`) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!i. i < LENGTH (sty::tys_tail) ==> ?x. _ /\ not_fresh_at cur x /\ _`
      (qspec_then `SUC i` mp_tac) >>
    (impl_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
    disch_then (qx_choose_then `xp` strip_assume_tac o SRULE [listTheory.EL])) >>>
  HEADGOAL (
    `not_fresh_at sm xp` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists `cur` >> simp[]) >>
    qpat_assum `!x. not_fresh_at cur x ==> lookup_var x q = _ /\ _`
      (qspec_then `xp` mp_tac) >> (impl_tac >- simp[]) >> strip_tac) >>>
  HEADGOAL (
    `k + SUC i = SUC k + i` by decide_tac >>
    qexists `xp` >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- asm_rewrite_tac[])) >>>
  HEADGOAL (Cases_on `is_word_type (EL i tys_tail)`) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i tys_tail) then _ else _` mp_tac >>
    simp[ptrDisciplineTheory.op_prov_def]) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i tys_tail) then _ else _` mp_tac >>
    asm_rewrite_tac[] >> strip_tac >>
    asm_rewrite_tac[] >>
    qpat_assum `!x cap. not_fresh_at cur x /\ ptr_covers Gu tu x u cap ==> _`
      irule >> asm_rewrite_tac[]) >>>
  HEADGOAL (sg `!aid b cap i. FLOOKUP s0.vs_allocas aid = SOME (b,cap) /\
      aid < sa.cs_next_id /\
      (!n c len. local_region cenv es.scopes s0 n c len ==> b + cap <= c \/ c + len <= b) /\
      b <= i /\ i < b + cap /\ i IN tq.t_mem ==> i IN tn0.t_mem`) >>>
  HEADGOAL (
    rpt strip_tac >>
    `FLOOKUP u.vs_allocas aid = SOME (b,cap)` by
      (qpat_assum `!a entry. FLOOKUP s0.vs_allocas a = SOME entry ==> _` irule >> simp[]) >>
    qpat_assum `!a off sz j. FLOOKUP s0.vs_allocas a = SOME (off,sz) /\
        a < sa.cs_next_id /\
        (!n c L. local_region cenv es.scopes s0 n c L ==> off + sz <= c \/ c + L <= off) /\
        off <= j /\ j < off + sz /\ j IN tu.t_mem ==> j IN tn0.t_mem`
      (qspecl_then [`aid`,`b`,`cap`,`i`] irule) >>
    (conj_tac >- (qexistsl_tac [`aid`,`b`,`cap`] >> asm_rewrite_tac[]))) >>>
  HEADGOAL (
    `aid < cur.cs_next_id` by decide_tac >>
    qpat_assum `!a b sz j. a < cur.cs_next_id /\ FLOOKUP u.vs_allocas a = SOME (b,sz) /\
      b <= j /\ j < b+sz /\ j IN tq.t_mem ==> j IN tu.t_mem`
      (qspecl_then [`aid`,`b`,`cap`,`i`] mp_tac) >> simp[]) >>>
  HEADGOAL (
    `EVERY (assignable_type (get_tenv cx)) tys_tail` by
      (qpat_assum `EVERY (assignable_type _) (sty::_)` mp_tac >> simp[NoAsms]) >>
    `assign_tuple_target_list cx (BaseTarget (TopLevelNameTarget (ns,id))::todo) (vi::vs_tail) =
     bind (assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (ns,id))) vi)
       (\u. assign_tuple_target_list cx todo vs_tail)` by
      simp[Once evaluate_def,ignore_bind_def] >>
    `gas_admissible (assign_tuple_target_list cx todo vs_tail) (stmt_res_ok lctx) fin` by
      (qpat_assum `gas_admissible (assign_tuple_target_list _ (_::_) _) _ src`
         mp_tac >>
       qpat_assum `assign_tuple_target_list _ (_::_) _ = bind _ _`
         (fn th => rewrite_tac[th]) >> disch_tac >>
       drule stmtSimForRoundsTheory.gas_admissible_bind_tail >>
       disch_then (qspecl_then [`[]`,`()`,`fin`] mp_tac) >> simp[])) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
        stmt_state_rel H ctx func cenv cx fin q /\ storage_well_formed_on cx fin (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx fin Gq tq q`) >>>
  HEADGOAL (
    qx_gen_tac `H` >>
    qpat_assum `fin.storage_trace = src.storage_trace` (fn th => rewrite_tac[th]) >> disch_tac >>
    qpat_assum `!H. valid_horizon cx st0 H src.storage_trace ==> _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!H. _ ==> stmt_post H ctx func cx lctx cenv cenv cur sm src u (INL ()) fin q`
      (qspec_then `H` mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (strip_assume_tac o REWRITE_RULE [stmt_post_def, boolTheory.TRUTH])) >>>
  HEADGOAL (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>>
  HEADGOAL conj_tac >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL conj_tac >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `!H D. _ ==> ghost_inv_at D lo d cenv cx fin Gq tq q`
      (qspecl_then [`H`,`DF H`] irule)) >>>
  HEADGOAL (
    conj_tac >- (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
      (qspec_then `H` ACCEPT_TAC)) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!n b sz. local_region cenv fin.scopes q n b sz <=>
                              local_region cenv src.scopes u n b sz`) >>>
  HEADGOAL (
    `!x v. not_fresh_at cur x /\ lookup_var x u = SOME v ==> lookup_var x q = SOME v` by
      (rpt strip_tac >>
       qpat_assum `!x. not_fresh_at cur x ==> lookup_var x q = lookup_var x u /\ _`
         drule >> simp[]) >>
    `MAP FDOM src.scopes = MAP FDOM fin.scopes` by simp[] >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`stmt_state_rel _ ctx func cenv cx src u`,
       `!x v. not_fresh_at cur x /\ lookup_var x u = SOME v ==> lookup_var x q = SOME v`,
       `MAP FDOM src.scopes = MAP FDOM fin.scopes`, `local_ptrs_reserved cenv cur`] >>
    POP_ASSUM_LIST kall_tac >>
    metis_tac[tuplePlaceStepTheory.tuple_place_endpoint_local_regions_some]) >>>
  HEADGOAL (Q.SUBGOAL_THEN `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP q.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
        b <= p /\ p + type_memory_size_list tvs <= b + sz /\
        (!n a len. local_region cenv fin.scopes q n a len ==> b + sz <= a \/ a + len <= b)) \/
      (?n b sz. local_region cenv fin.scopes q n b sz /\ b <= p /\
        p + type_memory_size_list tvs <= b + sz /\ local_path_at cenv cx n (p-b) (TupleTV tvs))`
    (mk_asm "immutable_container")) >>>
  HEADGOAL (
    qpat_assum `!n b sz. local_region cenv fin.scopes q n b sz <=> _`
      (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `type_memory_size_list tvs = 0 \/ _` DISJ_CASES_TAC
    >- (disj1_tac >> first_assum ACCEPT_TAC) >>
    disj2_tac >>
    qpat_assum `(?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      DISJ_CASES_TAC) >>>
  HEADGOAL (
    disj1_tac >>
    qpat_x_assum `?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ _`
      (qx_choose_then `rid` (qx_choose_then `rb` (qx_choose_then `rsz` strip_assume_tac))) >>
    qexistsl_tac [`rid`,`rb`,`rsz`] >> conj_tac) >>>
  HEADGOAL (
    qpat_assum `!aid entry. FLOOKUP u.vs_allocas aid = SOME entry ==>
                              FLOOKUP q.vs_allocas aid = SOME entry`
      (qspecl_then [`rid`,`(rb,rsz)`] irule)) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (conj_tac >- decide_tac >> asm_rewrite_tac[]) >>>
  HEADGOAL (disj2_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `fin.scopes = src.scopes` (fn sc =>
      asm "immutable_container" (fn th => rewrite_tac[th, REWRITE_RULE [sc] th]))) >>>
  HEADGOAL (
    `alloca_frame cenv es sa s0 cenv fin q` by
      (irule stmtSimDefsTheory.alloca_frame_trans >>
       qexistsl_tac [`cenv`,`src`,`u`,`cur`] >> asm_rewrite_tac[])) >>>
  HEADGOAL (
    `runtime_place_typed cx src (ImmutablePlace ns id []) stv` by
      (`?mods old. ALOOKUP src.immutables cx.txn.target = SOME mods /\
         FLOOKUP (get_source_immutables ns mods) id = SOME (stv,old)` by
         (irule immutableDeployAssignSourceFrameTheory.immutable_assign_source_lookup >>
          qexistsl_tac [`cenv`,`env`,`sty`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
       rewrite_tac[vyperPlaceTypingTheory.runtime_place_typed_immutable] >>
       (conj_tac >-
         (irule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
          qexistsl_tac [`get_tenv cx`,`sty`] >> first_assum ACCEPT_TAC)) >>
       qexistsl_tac [`get_source_immutables ns mods`,`stv`,`old`] >>
       simp[vyperStateTheory.get_immutables_def,
         vyperStateTheory.get_address_immutables_def,bind_def,lift_option_type_def,
         return_def,vyperStateTheory.subscripts_type_def])) >>>
  HEADGOAL (sg `expr_sim_inv cenv cx env fin`) >>>
  HEADGOAL (
    qpat_assum `expr_sim_inv cenv cx env src`
      (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def])) >>>
  HEADGOAL (sg `state_well_typed fin`) >>>
  HEADGOAL (
    qpat_assum `write_place cx (ImmutablePlace ns id []) vi src = (INL (),fin)`
      (mp_then Any irule vyperPlaceTypingTheory.write_immutable_place_preserves_state_well_typed)) >>>
  HEADGOAL (conj_tac >- asm_rewrite_tac[]) >>>
  HEADGOAL (qexists_tac `stv` >>
    (conj_tac >- asm_rewrite_tac[]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `env_consistent env cx fin`) >>>
  HEADGOAL (
    qpat_assum `write_place cx (ImmutablePlace ns id []) vi src = (INL (),fin)`
      (mp_then Any irule vyperPlaceWriteSoundnessTheory.write_immutable_place_preserves_env_consistent)) >>>
  HEADGOAL (asm_rewrite_tac[]) >>>
  HEADGOAL (
    qpat_assum `write_place cx (ImmutablePlace ns id []) vi src = (INL (),fin)`
      (mp_then Any strip_assume_tac vyperPlaceFramesTheory.write_immutable_place_frame) >>
    simp[expr_sim_inv_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    `!x. not_fresh_at sa x ==> not_fresh_at cur x` by
      (gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> asm_rewrite_tac[]) >>
    `!i:num. i + SUC k = SUC k + i` by decide_tac >>
    qpat_assum `!i:num. i + SUC k = SUC k + i` (fn th => rewrite_tac[th]) >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>>
  HEADGOAL (
    qpat_assum `fin.storage_trace = src.storage_trace` (fn tr =>
      qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _`
        (fn th => rewrite_tac[th, REWRITE_RULE [tr] th]))) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cur x`
      drule >> disch_tac >>
    qpat_assum `!x. not_fresh_at cur x ==> lookup_var x q = _ /\ _`
      drule >> strip_tac >>
    qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w`
      (qspecl_then [`x`,`w`] mp_tac) >> simp[]) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cur x`
      drule >> disch_tac >>
    qpat_assum `!x. not_fresh_at cur x ==> lookup_var x q = _ /\ _`
      drule >> strip_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gu x = _ /\ _`
      drule >> simp[]) >>>
  HEADGOAL (
    disch_tac >>
    `assign_tuple_target_list cx (BaseTarget (TopLevelNameTarget (ns,id))::todo) (vi::vs_tail) =
       bind (assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (ns,id))) vi)
         (\u. assign_tuple_target_list cx todo vs_tail)` by
      simp[Once evaluate_def,ignore_bind_def] >>
    qpat_assum `assign_tuple_target_list _ (_::_) _ = bind _ _`
      (fn th => rewrite_tac[th]) >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_bind >> BETA_TAC >>
    rpt conj_tac
    >~ [`storage_trace_frame (assign_tuple_targets _ _ _)`]
    >- simp[cj 9 vyperStorageTraceTheory.evaluate_storage_trace_frame]
    >~ [`storage_trace_frame (assign_tuple_target_list _ _ _)`]
    >- simp[cj 10 vyperStorageTraceTheory.evaluate_storage_trace_frame]
    >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]) >>>
  HEADGOAL (
    map_every qx_gen_tac [`left_marks`,`unit_res`,`src_after`,`vm_after`] >>
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_unit >>
    qexistsl_tac [`src_after`,`vm_after`,`unit_res`] >> BETA_TAC >> asm_rewrite_tac[]) >>>
  HEADGOAL (
    rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_execution >>
    disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >>
    rewrite_tac[ignore_bind_def,bind_def,return_def] >>
    qpat_assum `!tail. assign_tuple_targets cx (BaseTarget (TopLevelNameTarget (ns,id))) vi
        (src with gas_obs := tail) = _` (fn th => rewrite_tac[th]) >> simp[]) >>>
  HEADGOAL (
    irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`Gq`,`fin`,`INL ()`,`q`,`tq`] >>
    BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
    gen_tac >> disch_tac >> conj_tac >- simp[] >>
    qexists_tac `()` >>
    qpat_assum `fin with gas_obs := [] = fin` (fn th => rewrite_tac[th]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    `target_pre cenv cx env bt src` by simp[targetPlaceSimTheory.target_pre_def] >>
    `well_typed_target env bt sty` by
      (qpat_assum `well_typed_atarget env (BaseTarget bt) sty` mp_tac >>
       simp[NoAsms,well_typed_atarget_def])) >>>
  HEADGOAL (
    `type_place_target env bt = SOME (Type sty)` by
      (qpat_assum `well_typed_target env bt sty` mp_tac >> simp[NoAsms,well_typed_target_def])) >>>
  HEADGOAL (
    `?target_r target_cs. compile_get_target_ptr compile_expr cenv bt cur = (target_r,target_cs)` by
      (Cases_on `compile_get_target_ptr compile_expr cenv bt cur` >> simp[])) >>>
  HEADGOAL (
    `compile_get_target_ptr compile_expr cenv (gas_shadow_target bt) shadow_cur =
       (target_r,SND (compile_get_target_ptr compile_expr cenv (gas_shadow_target bt) shadow_cur)) /\
     gas_shadow_state target_cs
       (SND (compile_get_target_ptr compile_expr cenv (gas_shadow_target bt) shadow_cur))` by
      (mp_tac (Q.INST [`cenv` |-> `cenv`, `bt` |-> `bt`]
         gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_get_target_ptr) >>
       simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
       disch_then (qspecl_then [`cur`,`shadow_cur`] mp_tac) >> simp[] >>
       Cases_on `compile_get_target_ptr compile_expr cenv (gas_shadow_target bt) shadow_cur` >>
       simp[]) >>
    qmatch_asmsub_abbrev_tac `gas_shadow_state target_cs shadow_target_cs`) >>>
  HEADGOAL (
    qabbrev_tac `dest_loc = (case FST (SND target_r) of SOME l => l | NONE => LocMemory)` >>
    qabbrev_tac `dest_ty = (case SND (SND target_r) of SOME (ValPT t) => t | _ => sty)` >>
    qabbrev_tac `head_store =
      if is_word_type sty then
        if is_word_type dest_ty then
          compile_store_at_loc cenv.ce_imm_alloca (FST target_r) op0 (FST (SND target_r))
        else emit_void INVALID []
      else compile_assign_value cenv (FST target_r) dest_loc op0 (is_word_type dest_ty)
               NONE dest_ty sty (type_memory_bytes cenv dest_ty)`) >>>
  HEADGOAL (
    sg `head_store target_cs = ((),sm) /\ head_store shadow_target_cs = ((),shadow_sm)`) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (
    qpat_assum `compile_get_target_ptr _ _ bt cur = _` (fn target_eq =>
      qpat_assum `compile_tuple_store_all _ [_] [BaseTarget bt] [_] cur = _`
        (mp_tac o SIMP_RULE (srw_ss()) [compile_tuple_store_all_def,target_eq,
          comp_bind_def,comp_ignore_bind_def,comp_return_def])) >>
    simp[NoAsms,Abbr `head_store`,Abbr `dest_loc`,Abbr `dest_ty`]) >>>
  HEADGOAL (POP_ASSUM_LIST kall_tac >> pairarg_tac >> gvs[]) >>>
  HEADGOAL (
    qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_cur = _` (fn target_eq =>
      qpat_assum `compile_tuple_store_all _ [_] [BaseTarget (gas_shadow_target bt)] [_] shadow_cur = _`
        (mp_tac o SIMP_RULE (srw_ss()) [compile_tuple_store_all_def,target_eq,
          comp_bind_def,comp_ignore_bind_def,comp_return_def])) >>
    simp[NoAsms,Abbr `head_store`,Abbr `dest_loc`,Abbr `dest_ty`]) >>>
  HEADGOAL (POP_ASSUM_LIST kall_tac >> pairarg_tac >> gvs[]) >>>
  HEADGOAL (
    `ci_mono cur target_cs /\ ci_mono shadow_cur shadow_target_cs` by
      (conj_tac
       >- (qspec_then `cur` mp_tac
            (Q.SPECL [`bt`,`cenv`] ci_mono_compile_get_target_ptr) >> simp[]) >>
       qspec_then `shadow_cur` mp_tac
         (Q.SPECL [`gas_shadow_target bt`,`cenv`] ci_mono_compile_get_target_ptr) >> simp[])) >>>
  HEADGOAL (
    `!c. ci_mono c (SND (head_store c))` by
      (simp[Abbr `head_store`] >> gen_tac >> rpt IF_CASES_TAC >>
       simp[cj 1 ci_mono_stmt_helpers, cj 2 ci_mono_stmt_helpers, ci_mono_emit_void])) >>>
  HEADGOAL (
    sg `ci_mono target_cs sm /\ ci_mono shadow_target_cs shadow_sm`) >>>
  HEADGOAL (
    pop_assum (fn th =>
      map_every (fn c => qspec_then c mp_tac th) [`target_cs`,`shadow_target_cs`])) >>>
  HEADGOAL (simp[]) >>>
  HEADGOAL (
    map_every (fn pat => qpat_assum pat
      (strip_assume_tac o REWRITE_RULE [ci_mono_def]))
      [`ci_mono cur target_cs`, `ci_mono target_cs sm`,
       `ci_mono shadow_cur shadow_target_cs`, `ci_mono shadow_target_cs shadow_sm`] >>
    `fn_has_code cur target_cs func /\ fn_has_code target_cs sm func` by
      (irule fn_has_code_split >> asm_rewrite_tac[])) >>>
  HEADGOAL (
    `fn_has_code shadow_cur shadow_target_cs shadow_func /\
     fn_has_code shadow_target_cs shadow_sm shadow_func` by
      (irule fn_has_code_split >> asm_rewrite_tac[])) >>>
  HEADGOAL (sg `gas_admissible (eval_target_place cx bt) target_place_res_ok src`) >>>
  HEADGOAL (irule tuplePlaceTargetGasTheory.tuple_place_target_gas_admissible) >>>
  HEADGOAL (conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`cenv`,`env`,`sty`] >> asm_rewrite_tac[]) >>>
  HEADGOAL (
    `bodyFullTargetDefs$target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx env bt src` by
      (irule bodyFullTargetTheory.body_target_place_sim_full >> simp[] >>
       qexists_tac `tops` >> first_assum ACCEPT_TAC)) >>>
  HEADGOAL (
    qpat_x_assum `bodyFullTargetDefs$target_place_sim_full _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [bodyFullTargetDefsTheory.target_place_sim_full_def]) >>
    disch_then (qspecl_then [`st0`,`sty`,`cur`,`target_cs`,`shadow_cur`,
      `shadow_target_cs`,`target_r`,`u`,`Gu`,`tu`] mp_tac)) >>>
  HEADGOAL ((impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac) >>>
  HEADGOAL (
    qmatch_asmsub_abbrev_tac
      `gas_outcome_full _ _ _ _ (eval_target_place cx bt) _ targetQ targetR` >>
    qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ suffixQ suffixR` >>
    `assign_tuple_target_list cx (BaseTarget bt::todo) (vi::vs_tail) =
       bind (eval_target_place cx bt) (\p. bind (write_place cx p vi)
         (\u. assign_tuple_target_list cx todo vs_tail))` by
      simp[Once evaluate_def, Once evaluate_def,ignore_bind_def,bind_assoc] >>
    qpat_assum `assign_tuple_target_list _ (_::_) _ = bind _ _`
      (fn th => rewrite_tac[th]) >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> BETA_TAC) >>>
  HEADGOAL (conj_tac
    >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_write_place,
             cj 10 vyperStorageTraceTheory.evaluate_storage_trace_frame])) >>>
  HEADGOAL (conj_tac
    >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_place >>
        goal_assum (drule_at Any) >> simp[])) >>>
  HEADGOAL (conj_tac
    >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_place >> simp[])) >>>
  HEADGOAL (conj_tac >- simp[NoAsms,cj 8 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>>
  HEADGOAL (
    qexists_tac `\H res mid G tnt v. targetQ H res mid G tnt v /\
      mid.gas_obs = [] /\ ~v.vs_halted` >> BETA_TAC >> reverse conj_tac) >>>
  HEADGOAL (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
    simp[NoAsms,Abbr `targetR`,Abbr `suffixR`]) >>>
  HEADGOAL (rpt gen_tac >> strip_tac >> Cases_on `res`
    >- (qpat_x_assum `expr_exit _ _` mp_tac >> simp[NoAsms,exprSimDefsTheory.expr_exit_def])) >>>
  HEADGOAL (qexists_tac `y` >> simp[NoAsms]) >>>
  HEADGOAL (qpat_assum `expr_exit _ r` (mk_asm "target_abort_exit")) >>>
  HEADGOAL (qpat_assum `halt_exit H cx ee' _ r` (mk_asm "target_abort_halt")) >>>
  HEADGOAL (
    asm "target_abort_exit" (fn exit => asm "target_abort_halt" (fn halt =>
      let
        val rule = REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]
          augAssignFullRhsSavedTheory.augassign_expr_exit_to_stmt_exit
        val fmp_rule = MATCH_MP (MATCH_MP rule exit) halt
      in
        first_assum (mp_tac o MATCH_MP fmp_rule)
      end))) >>>
  HEADGOAL (disch_then ACCEPT_TAC) >>>
  HEADGOAL (
    map_every qx_gen_tac [`target_marks`,`target_res`,`mid`,`Gmid`,`tmid`,`m`] >>
    rpt strip_tac >>
    `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `Abbrev (targetQ = _)` (fn th =>
      CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
    BETA_TAC >>
    disch_then (CONJUNCTS_THEN2
      (qx_choose_then `place` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
      STRIP_ASSUME_TAC) >>
    disj1_tac >> qexists_tac `place` >> simp[]) >>>
  HEADGOAL (
    qpat_assum `!tail. eval_target_place cx bt _ = _`
      (qspec_then `[]` mp_tac) >>
    simp[NoAsms] >>
    `mid with gas_obs := [] = mid` by fs[evaluation_state_component_equality] >>
    qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th]) >>
    strip_tac) >>>
  HEADGOAL (
    `target_pre cenv cx env bt
       (src with gas_obs := gas_explicit target_marks u.vs_gas_readings)` by
      simp[targetSubscriptSplitTheory.target_subscript_pre_gas_obs] >>
    drule_all tuplePlaceSourceHeadTheory.tuple_place_source_target_endpoint >>
    strip_tac) >>>
  HEADGOAL (
    `eval_base_place cx bt (src with gas_obs := gas_explicit target_marks u.vs_gas_readings) =
      (INL (PlaceR place),mid)` by
      (qpat_assum `eval_target_place cx bt _ = (INL place,mid)` mp_tac >>
       simp[NoAsms,bodyPtrPopTargetFragTransportTheory.eval_target_place_as_bind,bind_def] >>
       Cases_on `eval_base_place cx bt (src with gas_obs := gas_explicit target_marks u.vs_gas_readings)` >>
       rename1 `eval_base_place _ _ _ = (res,st)` >> Cases_on `res` >>
       simp[NoAsms] >> rename1 `get_place pv st = _ ==> _` >>
       Cases_on `pv` >> simp[NoAsms,get_place_def,return_def,raise_def])) >>>
  HEADGOAL (
    `EVERY (supported_expr tops) (target_indices bt)` by
      (simp[NoAsms,EVERY_MEM] >> rpt strip_tac >>
       drule_all entryStatementTargetSupportTheory.supported_target_index >> simp[]) >>
    drule_all tuplePlaceBorrowTheory.tuple_place_supported_target_scopes >>
    simp[NoAsms] >> disch_tac) >>>
  HEADGOAL (
    qpat_assum `target_post _ ctx func cenv cx src cur target_cs u mid _ _ _ m`
      (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
    qpat_assum `ghost_kept_at lo cenv src cur Gu tu u Gmid tmid`
      (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def])) >>>
  HEADGOAL (
    `valid_horizon cx st0 (storage_trace_horizon src.storage_trace) src.storage_trace` by
      (qpat_assum `storage_trace_domain cx st0 src.storage_trace` mp_tac >>
       simp[NoAsms,vyperStorageFootprintTheory.storage_trace_domain_def]) >>
    qpat_assum `!H. valid_horizon cx st0 H src.storage_trace ==> _`
      (drule_then strip_assume_tac)) >>>
  HEADGOAL (
    `!n b sz. local_region cenv mid.scopes m n b sz <=> local_region cenv src.scopes u n b sz` by
      (`MAP FDOM src.scopes = MAP FDOM mid.scopes` by asm_rewrite_tac[] >>
       map_every (fn pat => qpat_assum pat mp_tac)
         [`stmt_state_rel _ ctx func cenv cx src u`,
          `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==> lookup_var x m = SOME w`,
          `MAP FDOM src.scopes = MAP FDOM mid.scopes`, `local_ptrs_reserved cenv cur`] >>
       POP_ASSUM_LIST kall_tac >>
       metis_tac[tuplePlaceStepTheory.tuple_place_endpoint_local_regions_some])) >>>
  HEADGOAL (sg `!b sz. b <= p /\ p + type_memory_size_list tvs <= b + sz /\
              mem_bytes_at b sz m.vs_memory = mem_bytes_at b sz u.vs_memory /\
              (!i. b <= i /\ i < b + sz /\ i IN tmid.t_mem ==> i IN tu.t_mem) ==>
            mem_bytes_at p (type_memory_size_list tvs) m.vs_memory =
              mem_bytes_at p (type_memory_size_list tvs) u.vs_memory /\
            (!i. p <= i /\ i < p + type_memory_size_list tvs /\ i IN tmid.t_mem ==>
                 i IN tu.t_mem)`) >>>
  HEADGOAL (POP_ASSUM_LIST kall_tac >> rpt gen_tac >> strip_tac >> conj_tac) >>>
  HEADGOAL (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> rpt strip_tac >>
    irule representationCleanPtrTheory.mem_bytes_at_eq_byte >>
    qpat_assum `mem_bytes_at b sz _ = mem_bytes_at b sz _` (irule_at Any) >>
    decide_tac) >>>
  HEADGOAL (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>>
  HEADGOAL (sg `mem_bytes_at p (type_memory_size_list tvs) m.vs_memory =
       mem_bytes_at p (type_memory_size_list tvs) u.vs_memory /\
     (!i. p <= i /\ i < p + type_memory_size_list tvs /\ i IN tmid.t_mem ==>
          i IN tu.t_mem)`) >>>
  HEADGOAL (qpat_x_assum `type_memory_size_list tvs = 0 \/ _` strip_assume_tac) >>>
  HEADGOAL (
    qpat_x_assum `type_memory_size_list tvs = 0` SUBST1_TAC >>
    simp[NoAsms,valueEncodingDefsTheory.mem_bytes_at_def] >> decide_tac) >>>
  HEADGOAL (
    qpat_assum `!b sz. b <= p /\ _ ==> _` (qspecl_then [`b`,`sz`] MATCH_MP_TAC) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac) >>>
  HEADGOAL (
    qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz m.vs_memory = _`
      (qspecl_then [`aid`,`b`,`sz`] MATCH_MP_TAC) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = _ /\ _ ==> i IN tu.t_mem`
      (qspecl_then [`aid`,`b`,`sz`,`i`] MATCH_MP_TAC) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `!b sz. b <= p /\ _ ==> _` (qspecl_then [`b`,`sz`] MATCH_MP_TAC) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac) >>>
  HEADGOAL (
    `lookup_scopes n mid.scopes = lookup_scopes n src.scopes` by
      (qpat_assum `mid.scopes = src.scopes` SUBST1_TAC >> REFL_TAC) >>
    drule_all tuplePlaceSnapshotTheory.tuple_place_target_unchanged_local >> disch_then ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> i IN tu.t_mem`
      (qspecl_then [`n`,`b`,`sz`,`i`] MATCH_MP_TAC) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
       val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`) >>>
  HEADGOAL (
    qspecl_then [`TupleTV tvs`,`ArrayV (TupleV vs)`,`p`,`p`,
      `type_memory_size_list tvs`,`tu.t_mem`,`tmid.t_mem`,`u.vs_memory`,`m.vs_memory`]
      MATCH_MP_TAC robustCopyTransportPtrTheory.robust_val_in_memory_decreasing_taint_transport) >>>
  HEADGOAL (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- (irule (REWRITE_RULE [valueEncodingTheory.type_memory_size_def]
      (Q.ISPEC `TupleTV tvs` exprSimPropsTheory.val_footprint_le)) >> first_assum ACCEPT_TAC) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    reverse conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!i. p <= i /\ i < p + type_memory_size_list tvs /\ _ ==> i IN tu.t_mem`
      (qspec_then `p+i` MATCH_MP_TAC) >>
    conj_tac >- decide_tac >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (Q.SUBGOAL_THEN `type_memory_size_list tvs = 0 \/
       (?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ aid < target_cs.cs_next_id /\
                   b <= p /\ p + type_memory_size_list tvs <= b + sz /\
                   (!n a len. local_region cenv mid.scopes m n a len ==>
                              b + sz <= a \/ a + len <= b)) \/
       (?n b sz. local_region cenv mid.scopes m n b sz /\ b <= p /\
                 p + type_memory_size_list tvs <= b + sz /\
                 local_path_at cenv cx n (p-b) (TupleTV tvs))` ASSUME_TAC) >>>
  HEADGOAL (qpat_x_assum `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
    strip_assume_tac) >>>
  HEADGOAL (disj1_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (disj2_tac >> disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >>
    conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
    conj_tac >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `cur.cs_next_id` >> conj_tac >> first_assum ACCEPT_TAC) >>
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!n b sz. local_region cenv mid.scopes m n b sz <=> _`
      (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (disj2_tac >> disj2_tac >> qexistsl_tac [`n`,`b`,`sz`] >>
    qpat_assum `!n b sz. local_region cenv mid.scopes m n b sz <=> _`
      (fn th => rewrite_tac[th]) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!x cap. not_fresh_at cur x /\ ptr_covers Gu tu x u cap ==>
       ptr_covers Gmid tmid x m cap`) >>>
  HEADGOAL (
    rpt strip_tac >> irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
    qpat_assum `ptr_covers Gu tu x u cap` (irule_at Any) >>
    qpat_assum `!x. not_fresh_at cur x ==> FLOOKUP Gmid x = _ /\ _`
      (qspec_then `x` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_assum `ptr_covers Gu tu x u cap`
      (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==> _`
      (drule_all_then assume_tac) >> asm_rewrite_tac[]) >>>
  HEADGOAL (sg `!i. i < LENGTH (sty::tys_tail) ==>
       ?x. EL i (op0::ops_tail) = Var x /\ not_fresh_at target_cs x /\
           op_taint tmid (Var x) = {} /\
           if is_word_type (EL i (sty::tys_tail)) then
             lookup_var x m = SOME (typed_val_to_w256 (EL i (stv::tvs_tail)) (EL i (vi::vs_tail))) /\
             op_prov Gmid (Var x) = NONE
           else lookup_var x m = SOME (n2w (p + SUM (MAP type_memory_size (TAKE (k+i) tvs)))) /\
                ptr_covers Gmid tmid x m (type_memory_size (EL i (stv::tvs_tail)))`) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!i. i < LENGTH (sty::tys_tail) ==> ?x. _ /\ not_fresh_at cur x /\ _`
      (drule_then (qx_choose_then `xp` strip_assume_tac)) >>
    `not_fresh_at target_cs xp` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `cur` >>
       conj_tac >> first_assum ACCEPT_TAC) >>
    qpat_assum `!x. not_fresh_at cur x ==> FLOOKUP Gmid x = _ /\ _`
      (qspec_then `xp` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qexists_tac `xp` >> conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- asm_rewrite_tac[]) >>>
  HEADGOAL (Cases_on `is_word_type (EL i (sty::tys_tail))`) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i (sty::tys_tail)) then _ else _` mp_tac >>
    asm_rewrite_tac[] >> strip_tac >>
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==> _`
      (drule_all_then assume_tac) >>
    qpat_x_assum `op_prov Gu (Var xp) = NONE`
      (assume_tac o SRULE [ptrDisciplineTheory.op_prov_def]) >>
    simp[ptrDisciplineTheory.op_prov_def]) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i (sty::tys_tail)) then _ else _` mp_tac >>
    asm_rewrite_tac[] >> strip_tac >>
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==> _`
      (drule_all_then assume_tac) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!x cap. not_fresh_at cur x /\ ptr_covers Gu tu x u cap ==> _` irule >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    map_every (fn q => qpat_assum q
      (strip_assume_tac o MATCH_MP fragExecTheory.DROP_EQ_CONS o SYM))
      [`sty::tys_tail = DROP k tys`, `stv::tvs_tail = DROP k tvs`,
       `vi::vs_tail = DROP k vs`] >>
    `writable_place_result cx mid (PlaceR place)` by
      simp[vyperTargetPlaceWriteTheory.writable_place_result_def]) >>>
  HEADGOAL (Q.SUBGOAL_THEN `FST (SND target_r) = SOME LocMemory ==>
    type_memory_size_list tvs = 0 \/
    p + type_memory_size_list tvs <= w2n w' \/
    w2n w' + type_memory_size stv <= p` ASSUME_TAC) >>>
  HEADGOAL (disch_tac >>
    qpat_x_assum `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      strip_assume_tac) >>>
  HEADGOAL (disj1_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `?id path. place = MemoryPlace id path`) >>>
  HEADGOAL (
    qpat_assum `place_ptr_rel cenv cx m (PlaceR place) _ _ _` mp_tac >>
    qpat_assum `FST (SND target_r) = SOME LocMemory` mp_tac >>
    Cases_on `place` >> simp[NoAsms,place_ptr_rel_def,slot_loc_def]) >>>
  HEADGOAL (
    rename1 `place_ptr_rel _ _ _ (PlaceR (StoragePlace tr slot tv)) _ _ _` >>
    Cases_on `tr` >> simp[NoAsms]) >>>
  HEADGOAL (
    qpat_assum `!id path. place = MemoryPlace id path ==> _`
      (qspecl_then [`id`,`path`] mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>>
  HEADGOAL (
    qpat_assum `place = MemoryPlace id path` (fn pl =>
      qpat_assum `FST (SND target_r) = SOME LocMemory` (fn loc =>
        qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' _ (Type sty)`
          (assume_tac o REWRITE_RULE [pl,loc])))) >>>
  HEADGOAL (
    qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
      qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m` (fn rel =>
        qpat_assum `lookup_scopes id mid.scopes = SOME _` (fn lookup =>
          qpat_assum `place_ptr_rel cenv cx m (PlaceR (MemoryPlace id path)) w' (SOME LocMemory) (Type sty)`
            (strip_assume_tac o
              (fn ptr => MATCH_MP tuplePlaceReachableTheory.tuple_place_memory_coordinates
                (LIST_CONJ [inv,rel,lookup,ptr]))))))) >>>
  HEADGOAL (
    `tv = stv` by metis_tac[optionTheory.SOME_11] >>
    qpat_assum `!n a len. local_region cenv mid.scopes m n a len ==> _`
      (drule_then mp_tac) >>
    qpat_assum `b <= p` mp_tac >>
    qpat_assum `p + type_memory_size_list tvs <= b + sz` mp_tac >>
    qpat_assum `off + type_memory_size tv <= _` mp_tac >>
    qpat_assum `w2n w' = _` mp_tac >>
    qpat_assum `tv = stv` (fn th => rewrite_tac[th]) >> decide_tac) >>>
  HEADGOAL (
    `p-b + type_memory_size (TupleTV tvs) <= sz` by
      (qpat_assum `b <= p` mp_tac >>
       qpat_assum `p + type_memory_size_list tvs <= b + sz` mp_tac >>
       simp[NoAsms,valueEncodingTheory.type_memory_size_def] >> decide_tac)) >>>
  HEADGOAL (
    `place_ptr_rel cenv cx m (PlaceR place) w' (SOME LocMemory) (Type (EL k tys))` by
      (qpat_assum `FST (SND target_r) = SOME LocMemory` (fn loc =>
         qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' _ (Type sty)`
           (mp_tac o REWRITE_RULE [loc])) >>
       qpat_assum `EL k tys = sty` (fn ty => simp[NoAsms,ty]))) >>>
  HEADGOAL (Q.SUBGOAL_THEN `b + (p-b) + type_memory_size (TupleTV tvs) <= w2n w' \/
                  w2n w' + type_memory_size (EL k tvs) <= b + (p-b)` ASSUME_TAC) >>>
  HEADGOAL (irule (INST_TYPE [alpha |-> ``:256``]
    tuplePlacePointerReadyTheory.tuple_place_writable_borrow_destination_apart)) >>>
  HEADGOAL (
    qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`cenv`,`ctx`,`cx`,`mid`,
                 `env`,`func`,`n`,`place`,`m`,`sz`,`tys`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    `b + (p-b) = p` by (qpat_assum `b <= p` mp_tac >> decide_tac) >>
    disj2_tac >>
    qpat_assum `b + (p-b) = p` (fn base =>
      qpat_assum `EL k tvs = stv` (fn ty =>
        qpat_assum `b + (p-b) + _ <= _ \/ _`
          (ACCEPT_TAC o REWRITE_RULE [base,ty,valueEncodingTheory.type_memory_size_def])))) >>>
  HEADGOAL (
    `dest_ty = sty` by
      (qpat_assum `SND (SND target_r) = SOME (value_type_place (Type sty))`
         (fn th => simp[NoAsms,Abbr `dest_ty`,th,value_type_place_def])) >>
    qpat_x_assum `dest_ty = sty` SUBST_ALL_TAC) >>>
  HEADGOAL (
    qpat_assum `!i. i < LENGTH (sty::tys_tail) ==> ?x. _ /\ not_fresh_at target_cs x /\ _`
      (qspec_then `0` mp_tac) >>
    simp[NoAsms] >> disch_then (qx_choose_then `xs` strip_assume_tac)) >>>
  HEADGOAL (
    Cases_on `write_place cx place vi mid` >>
    rename1 `write_place cx place vi mid = (write_res,fin)` >>
    `fin.gas_obs = []` by
      (drule tuplePlaceSourceGasTheory.tuple_place_write_preserves_gas_obs >> simp[]) >>
    `!tail. write_place cx place vi (mid with gas_obs := tail) =
      (write_res,fin with gas_obs := tail)` by
      (drule tuplePlaceSourceGasTheory.tuple_place_write_gas_obs >> simp[])) >>>
  HEADGOAL (
    qpat_assum `write_place cx place vi mid = _`
      (mp_then (Pat `f st = _`) mp_tac vyperStorageTraceTheory.storage_trace_frame_prefix) >>
    simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_write_place] >> strip_tac) >>>
  HEADGOAL (
    sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
             valid_horizon cx st0 H mid.storage_trace`) >>>
  HEADGOAL (
    qpat_assum `fin.storage_trace = mid.storage_trace ++ _` SUBST1_TAC >>
    gen_tac >> strip_tac >>
    drule_then ACCEPT_TAC gasOutcomeFullTheory.valid_horizon_append) >>>
  HEADGOAL (
    irule gasOutcomeFullComposeTheory.gas_outcome_full_bind >> BETA_TAC >>
    simp[NoAsms,vyperStorageTraceTheory.storage_trace_frame_write_place,
         cj 10 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>>
  HEADGOAL (conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_unit >>
    goal_assum (drule_at Any) >> simp[])) >>>
  HEADGOAL (conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_unit >> simp[])) >>>
  HEADGOAL (Cases_on `write_res`) >>>
  HEADGOAL (rename1 `write_place cx place vi mid = (INL unit_value,fin)`) >>>
  HEADGOAL (Cases_on `unit_value`) >>>
  HEADGOAL (irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >> BETA_TAC >>
    reverse conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (qrefinel [`_`,`fin`,`INL ()`,`_`,`_`] >>
    qpat_assum `!tail. write_place cx place vi (mid with gas_obs := tail) = _`
      (fn eq => simp[NoAsms,eq]) >>
    qpat_assum `fin.gas_obs = []`
      (fn obs => simp[NoAsms,GSYM obs])) >>>
  HEADGOAL (Cases_on `FST (SND target_r) = SOME LocMemory`) >>>
  HEADGOAL (
    `?id path. place = MemoryPlace id path` by
      (qpat_assum `place_ptr_rel cenv cx m (PlaceR place) _ _ _` mp_tac >>
       qpat_assum `FST (SND target_r) = SOME LocMemory` mp_tac >>
       Cases_on `place` >> simp[NoAsms,place_ptr_rel_def,slot_loc_def] >>
       rename1 `place_ptr_rel _ _ _ (PlaceR (StoragePlace tr slot tv)) _ _ _` >>
       Cases_on `tr` >> simp[NoAsms])) >>>
  HEADGOAL (
    qpat_assum `!id path. place = MemoryPlace id path ==> _`
      (qspecl_then [`id`,`path`] mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    qpat_assum `place = MemoryPlace id path` (fn pl =>
      qpat_assum `FST (SND target_r) = SOME LocMemory` (fn loc =>
        qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' _ (Type sty)`
          (assume_tac o REWRITE_RULE [pl,loc]))) >>
    drule_all tuplePlaceReachableTheory.tuple_place_memory_coordinates >> strip_tac) >>>
  HEADGOAL (
    rename1 `local_region cenv mid.scopes m id db dcap` >>
    qpat_assum `local_region cenv mid.scopes m id db dcap`
      (strip_assume_tac o REWRITE_RULE [local_region_def]) >>
    `ptr_covers Gmid tmid p' m dcap` by
      (qpat_assum `ghost_inv_at _ _ _ _ _ mid Gmid tmid m`
         (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >>
       disch_then (drule_all_then strip_assume_tac o CONJUNCT1) >> first_assum ACCEPT_TAC)) >>>
  HEADGOAL (`dest_loc = LocMemory` by simp[Abbr `dest_loc`]) >>>
  HEADGOAL (sg `op_prov Gmid (FST target_r) = FLOOKUP Gmid p'`) >>>
  HEADGOAL (
    qpat_assum `bodyFullTargetDefs$target_ptr_ok cenv (PlaceR place) target_r Gmid tmid m`
      (mp_tac o cj 2 o REWRITE_RULE [bodyFullTargetDefsTheory.target_ptr_ok_def]) >>
    disch_then (qspecl_then [`id`,`path`,`p'`,`dcap`] mp_tac) >> simp[]) >>>
  HEADGOAL (sg `?xd. FST target_r = Var xd`) >>>
  HEADGOAL (
    `FLOOKUP Gmid p' <> NONE` by
      (qpat_assum `ptr_covers Gmid tmid p' m dcap` mp_tac >>
       simp[NoAsms,ptr_covers_def] >> strip_tac >> simp[]) >>
    qpat_assum `op_prov Gmid (FST target_r) = FLOOKUP Gmid p'` mp_tac >>
    qpat_assum `FLOOKUP Gmid p' <> NONE` mp_tac >>
    Cases_on `FST target_r` >> simp[NoAsms,ptrDisciplineTheory.op_prov_def]) >>>
  HEADGOAL (sg `not_fresh_at target_cs xd`) >>>
  HEADGOAL (
    qpat_assum `!x. FST target_r = Var x ==> not_fresh_at target_cs x`
      (qspec_then `xd` irule) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `lookup_var xd m = SOME w'`) >>>
  HEADGOAL (
    qpat_assum `eval_operand (FST target_r) m = SOME w'` mp_tac >>
    qpat_assum `FST target_r = Var xd` (fn eq =>
      simp[NoAsms,eq,venomStateTheory.eval_operand_def])) >>>
  HEADGOAL (sg `db + dcap <= m.vs_alloca_next`) >>>
  HEADGOAL (
    irule (INST_TYPE [alpha |-> ``:256``] bodyMemoryDefsTheory.body_local_region_frontier) >>
    goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
    qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`ctx`,`cx`,`func`] >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rename1 `w2n w' = db + off` >>
    rename1 `off + type_memory_size dest_tv <= dcap` >>
    `dest_tv = stv` by
      (qpat_assum `evaluate_type (get_tenv cx) sty = SOME dest_tv` mp_tac >>
       qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
         (fn eq => simp[NoAsms,eq,EQ_SYM_EQ])) >>
    qpat_x_assum `dest_tv = stv` SUBST_ALL_TAC >>
    `w2n w' + type_memory_size stv <= m.vs_alloca_next` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`w2n w' = db + off`,`db + dcap <= m.vs_alloca_next`,
         `off + type_memory_size stv <= dcap`] >> decide_tac)) >>>
  HEADGOAL (sg `op_taint tmid (Var xd) = {}`) >>>
  HEADGOAL (
    qpat_assum `bodyFullTargetDefs$target_ptr_ok cenv (PlaceR place) target_r Gmid tmid m`
      (mp_tac o cj 1 o REWRITE_RULE [bodyFullTargetDefsTheory.target_ptr_ok_def]) >>
    qpat_assum `FST target_r = Var xd` (fn eq => simp[NoAsms,eq])) >>>
  HEADGOAL (sg `FLOOKUP Gmid xd = FLOOKUP Gmid p'`) >>>
  HEADGOAL (
    qpat_assum `op_prov Gmid (FST target_r) = FLOOKUP Gmid p'` mp_tac >>
    qpat_assum `FST target_r = Var xd` (fn eq =>
      simp[NoAsms,eq,ptrDisciplineTheory.op_prov_def])) >>>
  HEADGOAL (sg `ptr_covers Gmid tmid xd m (type_memory_size stv)`) >>>
  HEADGOAL (
    rename1 `lookup_var p' m = SOME base_word` >>
    qpat_assum `ptr_covers Gmid tmid p' m dcap`
      (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
    qpat_assum `lookup_var p' m = SOME base_word` (fn eq => simp[NoAsms,eq]) >>
    strip_tac >> rename1 `FLOOKUP Gmid p' = SOME (site,site_cap)`) >>>
  HEADGOAL (
    rewrite_tac[ptr_covers_def] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl [`w'`,`site`,`site_cap`] >>
    asm_rewrite_tac[]) >>>
  HEADGOAL (
    map_every (fn pat => qpat_assum pat mp_tac)
      [`site <= w2n base_word`,`dcap + w2n base_word <= site + site_cap`,
       `off + type_memory_size stv <= dcap`] >>
    decide_tac) >>>
  HEADGOAL (
    `allocas_from lo m /\ lo <= m.vs_alloca_next` by
      (qpat_assum `ghost_inv_at _ lo d cenv cx mid Gmid tmid m`
        (fn th => let val post = REWRITE_RULE [ghost_inv_at_def] th
                  in ACCEPT_TAC (CONJ (cj 7 post) (cj 8 post)) end))) >>>
  HEADGOAL (
    `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size stv <=
     type_memory_size_list tvs` by
      (drule tupleMemoryLayoutTheory.tuple_element_interval >>
       simp[valueEncodingProofsTheory.type_memory_size_list_sum])) >>>
  HEADGOAL (sg `?q Gq tq.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (m,Gmid,tmid) [] (OK q,Gq,tq)) /\
    val_in_memory stv vi (w2n w') q.vs_memory /\
    (!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
      val_in_memory stv vi (w2n w') mem) /\
    typed_copy_state_frame target_cs (w2n w') (type_memory_size stv) m q /\
    ~q.vs_halted /\ q.vs_current_bb = sm.cs_current_bb /\
    q.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~block_is_terminated sm /\
    tq.t_stor = tmid.t_stor /\ tq.t_trans = tmid.t_trans /\ tq.t_imm = tmid.t_imm /\
    (!j. ~(w2n w' <= j /\ j < w2n w' + type_memory_size stv) ==>
      (j IN tq.t_mem <=> j IN tmid.t_mem)) /\
    (!x. not_fresh_at target_cs x ==>
      lookup_var x q = lookup_var x m /\ FLOOKUP Gq x = FLOOKUP Gmid x /\
      op_taint tq (Var x) = op_taint tmid (Var x))`) >>>
  HEADGOAL (reverse (Cases_on `is_word_type sty`)) >>>
  HEADGOAL (
    `compile_store_memory cenv (Var xs) (FST target_r) sty sty target_cs = ((),sm)` by
      (qpat_x_assum `head_store target_cs = _` mp_tac >>
       simp[Abbr `head_store`,compile_assign_value_def])) >>>
  HEADGOAL (
    `LENGTH vs = LENGTH tvs` by
      (irule vyperTypingTheory.values_have_types_length >> simp[]) >>
    `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
             tuple_in_memory vs tvs p mem` by
      (qpat_assum `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
                         val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [Once valueEncodingDefsTheory.val_in_memory_def])) >>
    `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
             val_in_memory stv vi (p + SUM (MAP type_memory_size (TAKE k tvs))) mem` by
      (qspecl_then [`vs`,`tvs`,`p`,`m.vs_memory`,`tmid`,`k`] mp_tac
         typedCopyLayoutPtrTheory.tuple_in_memory_robust_element >> simp[])) >>>
  HEADGOAL (
    `m.vs_alloca_next < dimword (:256)` by
      (qpat_assum `stmt_state_rel _ _ _ _ _ mid m`
         (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room) >>
       disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
    qabbrev_tac `addr = p + SUM (MAP type_memory_size (TAKE k tvs))` >>
    `addr + type_memory_size stv <= m.vs_alloca_next` by
      (qpat_assum `p + type_memory_size_list tvs <= u.vs_alloca_next` mp_tac >>
       qpat_assum `u.vs_alloca_next <= m.vs_alloca_next` mp_tac >>
       qpat_assum `SUM (MAP type_memory_size (TAKE k tvs)) + _ <= _` mp_tac >>
       simp[NoAsms,Abbr `addr`] >> decide_tac) >>
    `addr < dimword (:256)` by
      (qpat_assum `addr + _ <= m.vs_alloca_next` mp_tac >>
       qpat_assum `m.vs_alloca_next < dimword (:256)` mp_tac >> decide_tac) >>
    `w2n (n2w addr : 256 word) = addr` by
      simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>>
  HEADGOAL (sg `compile_store_memory cenv (Var xs) (Var xd) sty sty target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `FST target_r = Var xd` (fn eq =>
      qpat_assum `compile_store_memory _ _ (FST target_r) _ _ target_cs = _`
        (mp_tac o REWRITE_RULE [eq])) >>
    simp[NoAsms]) >>>
  HEADGOAL (
    qpat_assum `if is_word_type sty then _ else _` mp_tac >>
    qpat_assum `~is_word_type sty` (fn ty => simp[NoAsms,ty]) >>
    strip_tac) >>>
  HEADGOAL (Q.SUBGOAL_THEN `addr + type_memory_size stv <= w2n w' \/
                   w2n w' + type_memory_size stv <= addr` ASSUME_TAC) >>>
  HEADGOAL (
    qpat_assum `FST (SND target_r) = SOME LocMemory ==> _`
      (drule_then mp_tac) >>
    qpat_assum `SUM (MAP type_memory_size (TAKE k tvs)) + _ <= _` mp_tac >>
    simp[NoAsms,Abbr `addr`] >> decide_tac) >>>
  HEADGOAL (
    qpat_assum `body_inv tops ctx cenv cx`
      (mp_then Any mp_tac immutableDeployAssignRangesTheory.immutable_assign_copy_metadata) >>
    disch_then drule >> strip_tac) >>>
  HEADGOAL (
    `type_memory_bytes cenv sty = type_memory_size stv` by
      (qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
         (mp_then Any mp_tac exprSimHypsTheory.expr_sim_inv_memory_size) >>
       disch_then drule >> simp[]) >>
    `val_wf stv vi` by
      (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
       first_assum ACCEPT_TAC)) >>>
  HEADGOAL (
    `addr + type_memory_size stv < dimword (:256) /\
      w2n w' + type_memory_size stv < dimword (:256)` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`addr + type_memory_size stv <= m.vs_alloca_next`,
         `w2n w' + type_memory_size stv <= m.vs_alloca_next`,
         `m.vs_alloca_next < dimword (:256)`] >> decide_tac)) >>>
  HEADGOAL (sg `~block_is_terminated sm`) >>>
  HEADGOAL (
    qpat_assum `compile_store_memory cenv (Var xs) (Var xd) sty sty target_cs = ((),sm)`
      (mp_then Any irule exprOpenCopiesTheory.compile_store_memory_open) >>
    simp[] >>
    qpat_assum `compile_get_target_ptr compile_expr cenv bt cur = (target_r,target_cs)`
      (mp_then Any irule placeRelayoutOpenTheory.compile_get_target_ptr_endpoint_open) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    mp_tac (Q.INST
      [`cenv` |-> `cenv`,`xs` |-> `xs`,`xd` |-> `xd`,
       `dty` |-> `sty`,`sty` |-> `sty`,`dtv` |-> `stv`,`stv` |-> `stv`,
       `sa` |-> `target_cs`,`sb` |-> `sm`,`tenv` |-> `get_tenv cx`,`v` |-> `vi`,
       `s` |-> `m`,`sw` |-> `n2w addr : 256 word`,`dw` |-> `w' : 256 word`,
       `G` |-> `Gmid`,`tn` |-> `tmid`,`lo` |-> `lo`,
       `ctx` |-> `ctx`,`func` |-> `func`,`PG` |-> `PG`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
      bodyFullMemoryStoreTheory.body_full_memory_store_path) >>
    impl_tac) >>>
  HEADGOAL (
    simp[type_widens_to_refl] >>
    qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
      mp_tac >> simp[NoAsms]) >>>
  HEADGOAL (
    disch_then (qx_choose_then `copy_end` (qx_choose_then `copy_prov`
      (qx_choose_then `copy_taint` strip_assume_tac))) >>
    qexistsl_tac [`copy_end`,`copy_prov`,`copy_taint`] >>
    simp[arithmeticTheory.ADD_COMM]) >>>
  HEADGOAL (sg `emit_void MSTORE [Var xd;Var xs] target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `Abbrev (head_store = _)` (fn head =>
      qpat_assum `is_word_type sty` (fn word =>
        qpat_assum `FST (SND target_r) = SOME LocMemory` (fn loc =>
          qpat_assum `FST target_r = Var xd` (fn dst =>
            qpat_assum `op0 = Var xs` (fn src =>
              qpat_assum `head_store target_cs = ((),sm)`
                (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] head,
                  word,loc,dst,src,compile_store_at_loc_def])))))) >>
    simp[NoAsms]) >>>
  HEADGOAL (sg `~block_is_terminated sm`) >>>
  HEADGOAL (
    qpat_assum `emit_void MSTORE [Var xd;Var xs] target_cs = ((),sm)`
      (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
    simp[NoAsms,venomInstTheory.is_terminator_def]) >>>
  HEADGOAL (
    qpat_assum `if is_word_type sty then _ else _` mp_tac >>
    qpat_assum `is_word_type sty` (fn th => simp[NoAsms,th]) >>
    strip_tac) >>>
  HEADGOAL (
    `store_lays_out stv stv vi` by
      (match_mp_tac (Q.SPECL [`get_tenv cx`,`sty`,`stv`,`vi`]
        stmtSimDeclStoreTheory.store_lays_out_typed) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `type_memory_size stv = 32` by
      (qpat_assum `store_lays_out stv stv vi`
        (ACCEPT_TAC o cj 2 o REWRITE_RULE [store_lays_out_def]))) >>>
  HEADGOAL (
    drule emitted_insts_emit_void >> strip_tac >>
    `sm.cs_current_bb = target_cs.cs_current_bb` by
      (qpat_assum `emit_void MSTORE [Var xd;Var xs] target_cs = ((),sm)`
        (mp_tac o MATCH_MP emit_void_same_blocks) >> simp[NoAsms,same_blocks_def]) >>
    drule_all fn_has_code_same_block >> strip_tac >>
    `get_instruction bb m.vs_inst_idx =
      SOME (mk_inst target_cs.cs_next_id MSTORE [Var xd;Var xs] [])` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[])) >>>
  HEADGOAL (
    qabbrev_tac `written = mstore (w2n (w':256 word)) (typed_val_to_w256 stv vi) m` >>
    qabbrev_tac `store_ins = mk_inst target_cs.cs_next_id MSTORE [Var xd;Var xs] []` >>
    qabbrev_tac `word_store_ghost = step_taint store_ins m written tmid`) >>>
  HEADGOAL (sg `step_prov PG Gmid store_ins written = Gmid /\
     word_store_ghost.t_var = tmid.t_var /\
     word_store_ghost.t_stor = tmid.t_stor /\
     word_store_ghost.t_trans = tmid.t_trans /\
     word_store_ghost.t_mem = tmid.t_mem DIFF {i | w2n (w':256 word) <= i /\ i < w2n w' + 32}`) >>>
  HEADGOAL (
    mp_tac (Q.SPECL [`PG`,`Gmid`,`tmid`,`m`,`target_cs.cs_next_id`,
      `xd`,`Var xs`,`w' : 256 word`,`typed_val_to_w256 stv vi`]
      wordLoadStorePtrTheory.mstore_ghost_frame) >>
    impl_tac >- (rewrite_tac[eval_operand_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[Abbr `word_store_ghost`,Abbr `store_ins`,Abbr `written`]) >>>
  HEADGOAL (
    qexistsl_tac [`written with vs_inst_idx := SUC m.vs_inst_idx`,`Gmid`,`word_store_ghost`] >>
    conj_tac) >>>
  HEADGOAL (qx_gen_tac `store_dead`) >>>
  HEADGOAL (sg `step_inst_base store_ins m = OK written`) >>>
  HEADGOAL (
    mp_tac (Q.SPECL [`Var xd`,`Var xs`,`w' : 256 word`,
      `typed_val_to_w256 stv vi`,`target_cs.cs_next_id`,`m`]
      emitHelperPropsTheory.step_MSTORE) >>
    impl_tac >- (rewrite_tac[eval_operand_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
    simp[Abbr `store_ins`,Abbr `written`]) >>>
  HEADGOAL (sg `store_ins.inst_opcode <> GAS /\ store_ins.inst_opcode <> INVOKE /\
    ~is_terminator store_ins.inst_opcode /\ inst_dload_in_section store_ins m`) >>>
  HEADGOAL (
    simp[Abbr `store_ins`,mk_inst_def,is_terminator_def,inst_dload_in_section_def]) >>>
  HEADGOAL (sg `inst_mem_below_frontier store_ins m`) >>>
  HEADGOAL (simp[Abbr `store_ins`,below_frontier_MSTORE,eval_operand_def]) >>>
  HEADGOAL (sg `ptr_inst_ok store_dead lo 0 ctx func Gmid tmid store_ins m`) >>>
  HEADGOAL (
    qpat_assum `Abbrev (store_ins = _)`
      (fn inst => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] inst]) >>
    match_mp_tac (Q.INST
      [`D` |-> `store_dead`,`lo` |-> `lo`,`fuel` |-> `0`,`ctx` |-> `ctx`,
       `fn` |-> `func`,`G` |-> `Gmid`,`tn` |-> `tmid`,`s` |-> `m`,
       `id` |-> `target_cs.cs_next_id`,`p` |-> `xd`,`v` |-> `Var xs`]
      exprPtrUnwrapCopyEdgesTheory.ptr_inst_ok_mstore_tainted) >>
    conj_tac
    >- (qpat_assum `type_memory_size stv = 32` (fn size =>
          qpat_assum `ptr_covers Gmid tmid xd m (type_memory_size stv)`
            (ACCEPT_TAC o REWRITE_RULE [size]))) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `lookup_block m.vs_current_bb func.fn_blocks = SOME bb`) >>>
  HEADGOAL (
    qpat_assum `m.vs_current_bb = target_cs.cs_current_bb` (fn pc => PURE_REWRITE_TAC[pc]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `gas_origin_ptr_edge (store_dead,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (m,Gmid,tmid) [] (OK (written with vs_inst_idx := SUC m.vs_inst_idx),Gmid,word_store_ghost)`) >>>
  HEADGOAL (
    mp_tac (Q.INST [`D` |-> `store_dead`,`lo` |-> `lo`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`ctx` |-> `ctx`,
      `func` |-> `func`,`PG` |-> `PG`,`s` |-> `m`,`bb` |-> `bb`,
      `G` |-> `Gmid`,`tn` |-> `tmid`,`i` |-> `store_ins`,`u` |-> `written`]
      fragGasSeqPtrTheory.straight_line_origin_ptr_edge) >>
    impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_rewrite_tac[]]) >>
    qpat_assum `Abbrev (word_store_ghost = _)` (fn ghost =>
      pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ghost)]) >>
    asm_rewrite_tac[]) >>>
  HEADGOAL (
    `~written.vs_halted` by simp[Abbr `written`,mstore_def] >>
    qpat_assum `gas_origin_ptr_edge _ _ [] (OK _,Gmid,word_store_ghost)`
      (mp_then Any mp_tac (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)) >>
    disch_then (qspec_then `[]` (irule o SRULE [])) >>
    irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]) >>>
  HEADGOAL conj_tac >>>
  HEADGOAL (
    qpat_assum `store_lays_out stv stv vi`
      (mp_tac o Q.SPECL [`w2n (w':256 word)`,`m`] o cj 4 o REWRITE_RULE [store_lays_out_def]) >>
    simp[Abbr `written`]) >>>
  HEADGOAL conj_tac >>>
  HEADGOAL (
    mp_tac (Q.INST [`etv` |-> `stv`,`dtv` |-> `stv`,`v` |-> `vi`,
      `off` |-> `w2n (w':256 word)`,`dirty` |-> `tmid.t_mem`,`s` |-> `m`]
      assignTuplePtrStoreWordTheory.store_lays_out_robust_ptr) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    simp[Abbr `written`]) >>>
  HEADGOAL (sg `word_store_ghost.t_imm = tmid.t_imm`) >>>
  HEADGOAL (
    qpat_assum `Abbrev (word_store_ghost = _)`
      (fn eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
    irule (cj 3 decoderGhostFramePtrTheory.step_taint_nonmemory_frame) >>
    simp[Abbr `store_ins`,mk_inst_def]) >>>
  HEADGOAL conj_tac >>>
  HEADGOAL (simp[Abbr `written`,typed_copy_mstore_state_frame]) >>>
  HEADGOAL (conj_tac >- simp[Abbr `written`,mstore_def]) >>>
  HEADGOAL (conj_tac >- simp[Abbr `written`,mstore_def,write_memory_with_expansion_def]) >>>
  HEADGOAL (conj_tac >- simp[]) >>>
  HEADGOAL (conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    conj_tac
    >- simp[pred_setTheory.IN_DIFF,arithmeticTheory.ADD_COMM]) >>>
  HEADGOAL (
    simp[Abbr `written`,mstore_def,write_memory_with_expansion_def,lookup_var_def,op_taint_def]) >>>
  HEADGOAL (sg `typed_copy_effect ctx func target_cs sm m q
    (w2n w') (type_memory_size stv)`) >>>
  HEADGOAL (
    qpat_assum `!D. gas_origin_ptr_path _ (m,Gmid,tmid) [] (OK q,Gq,tq)`
      (qspec_then `DF (storage_trace_horizon mid.storage_trace)` assume_tac)) >>>
  HEADGOAL (
    qpat_assum `!D sa' sb' s' G' tn' t' Gf tf dst n. _ ==> typed_copy_effect ctx func sa' sb' s' t' dst n`
      (qspecl_then [`DF (storage_trace_horizon mid.storage_trace)`,`target_cs`,`sm`,`m`,
        `Gmid`,`tmid`,`q`,`Gq`,`tq`,`w2n w'`,`type_memory_size stv`] MATCH_MP_TAC)) >>>
  HEADGOAL (asm_rewrite_tac[]) >>>
  HEADGOAL (sg `assignable_type (get_tenv cx) sty`) >>>
  HEADGOAL (
    qpat_assum `EVERY (assignable_type (get_tenv cx)) (sty::tys_tail)` mp_tac >>
    simp[NoAsms]) >>>
  HEADGOAL (Q.SUBGOAL_THEN `0 < type_memory_size stv` ASSUME_TAC) >>>
  HEADGOAL (
    MATCH_MP_TAC (Q.SPEC `stv` (cj 1 valueEncodingPropsTheory.type_memory_size_pos)) >>
    MATCH_MP_TAC (Q.SPECL [`get_tenv cx`,`sty`,`stv`]
      vyperTypeSystemTheory.assignable_type_slot_size_pos) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `0 < dcap`) >>>
  HEADGOAL (
    map_every (fn pat => qpat_assum pat mp_tac)
      [`0 < type_memory_size stv`,`off + type_memory_size stv <= dcap`] >>
    decide_tac) >>>
  HEADGOAL (sg `lo <= w2n w'`) >>>
  HEADGOAL (
    `lo <= db` suffices_by decide_tac >>
    qpat_assum `local_region cenv mid.scopes m id db dcap`
      (mp_then Any irule (INST_TYPE [alpha |-> ``:256``]
        bodyFullMemoryFramesTheory.body_full_local_region_lower_bound)) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl [`DF (storage_trace_horizon mid.storage_trace)`,
      `storage_trace_horizon mid.storage_trace`,`ctx`,`cx`,`env`,`mid`,`func`,`tops`] >>
    simp[]) >>>
  HEADGOAL (sg `local_ptrs_reserved cenv target_cs /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x)`) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (
    match_mp_tac (Q.SPECL [`cenv`,`cur`,`target_cs`] local_ptrs_reserved_next_var) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (
    rpt strip_tac >>
    match_mp_tac (Q.SPECL [`cur`,`target_cs`,`x`] freshWritesTheory.not_fresh_at_mono) >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at cur x`
      (qspecl_then [`x`,`cap`] (fn th => match_mp_tac th)) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >>
    match_mp_tac (Q.SPECL [`cur`,`target_cs`,`x`] freshWritesTheory.not_fresh_at_mono) >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at cur x`
      (qspecl_then [`x`,`cap`] (fn th => match_mp_tac th)) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!n path' entry' ty. place = MemoryPlace n path' /\
    lookup_scopes n mid.scopes = SOME entry' /\ cenv.ce_var_type n = SOME ty ==>
    evaluate_type (get_tenv cx) ty = SOME entry'.type`) >>>
  HEADGOAL (
    rpt strip_tac >> irule bodySimAugPlaceLoadTheory.aug_place_entry_type_agrees >>
    qexistsl [`cenv`,`env`,`n`,`mid`,`mid`] >> simp[]) >>>
  HEADGOAL (sg `fin.storage_trace = mid.storage_trace /\
    MAP FDOM fin.scopes = MAP FDOM mid.scopes /\ expr_sim_inv cenv cx env fin`) >>>
  HEADGOAL (
    qpat_assum `write_place cx place vi mid = (INL (),fin)`
      (fn th => assume_tac (MATCH_MP tuplePlaceStepTheory.write_place_storage_trace th) >>
                assume_tac (MATCH_MP vyperScopePreservationTheory.write_place_scopes_dom th)) >>
    simp[EQ_SYM_EQ] >> irule tuplePlaceSourceTheory.tuple_place_write_inv >>
    qexistsl [`place`,`INL ()`,`mid`,`stv`,`vi`] >> simp[]) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin q /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin Gq tq q /\
    alloca_frame cenv mid target_cs m cenv fin q /\
    (!aid off sz i. FLOOKUP m.vs_allocas aid = SOME (off,sz) /\
      aid < target_cs.cs_next_id /\
      (!n b cap. local_region cenv mid.scopes m n b cap ==> off+sz <= b \/ b+cap <= off) /\
      off <= i /\ i < off+sz /\ i IN tq.t_mem ==> i IN tmid.t_mem)`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!K. valid_horizon cx st0 K fin.storage_trace ==>
                    valid_horizon cx st0 K mid.storage_trace`
      (drule_then assume_tac) >>
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==>
      targetQ K (INL place) mid Gmid tmid m /\ _` (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `Abbrev (targetQ = _)` (fn th =>
      CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
    BETA_TAC >> simp[NoAsms] >> strip_tac) >>>
  HEADGOAL (
    qpat_assum `target_post H ctx func cenv cx src cur target_cs u mid (PlaceR place) (Type sty) target_r m`
      (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
    qpat_assum `place = MemoryPlace id path` (fn eq =>
      qpat_assum `write_place cx place vi mid = (INL (),fin)`
        (mp_then Any (qx_choose_then `scopes_after` assume_tac)
          vyperPlaceFramesTheory.write_memory_place_frame o REWRITE_RULE [eq]))) >>>
  HEADGOAL (sg `storage_well_formed_on cx fin (FST H)`) >>>
  HEADGOAL (
    irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
    qexists_tac `mid` >>
    qpat_assum `fin = mid with scopes := scopes_after`
      (fn eq => simp[eq])) >>>
  HEADGOAL (
    qpat_assum `FST (SND target_r) = SOME LocMemory` (fn loc =>
      qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' (FST (SND target_r)) (Type sty)`
        (assume_tac o REWRITE_RULE [loc]))) >>>
  HEADGOAL (
    mp_tac (Q.INST
      [`H` |-> `H`,`ctx` |-> `ctx`,`func` |-> `func`,`cenv` |-> `cenv`,
       `cx` |-> `cx`,`env` |-> `env`,`lo` |-> `lo`,`d` |-> `d`,
       `sa` |-> `target_cs`,`sb` |-> `sm`,`s` |-> `m`,`t` |-> `q`,
       `dw` |-> `w'`,`dty` |-> `sty`,`dtv` |-> `stv`,`ee` |-> `mid`,
       `ff` |-> `fin`,`p` |-> `place`,`v` |-> `vi`,
       `G` |-> `Gmid`,`tn` |-> `tmid`,`Gf` |-> `Gq`,`tf` |-> `tq`,
       `D` |-> `DF H`]
      (INST_TYPE [alpha |-> ``:256``]
        memoryPlaceStorePostTheory.body_assign_memory_place_store_post)) >> impl_tac) >>>
  HEADGOAL (asm_rewrite_tac[] >> rpt conj_tac) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!x. not_fresh_at target_cs x ==>
       lookup_var x q = lookup_var x m /\ _` (drule_then strip_assume_tac) >> simp[]) >>>
  HEADGOAL (strip_tac >> asm_rewrite_tac[]) >>>
  HEADGOAL (sg `q.vs_allocas = m.vs_allocas /\ q.vs_alloca_next = m.vs_alloca_next`) >>>
  HEADGOAL (
    qpat_assum `typed_copy_state_frame target_cs _ _ m q` mp_tac >>
    simp[NoAsms,typed_copy_state_frame_def,venom_state_component_equality]) >>>
  HEADGOAL (sg `ctx_has_dalloca ctx ==> allocas_below_fmp q`) >>>
  HEADGOAL (
    qpat_assum `typed_copy_state_frame target_cs _ _ m q`
      (mp_tac o MATCH_MP typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp) >>
    strip_tac >> asm_rewrite_tac[]) >>>
  HEADGOAL (sg `!x. not_fresh_at cur x ==> not_fresh_at target_cs x`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists `cur` >> simp[ci_mono_def]) >>>
  HEADGOAL (sg `!x. not_fresh_at sa x ==> not_fresh_at cur x`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists `sa` >> simp[]) >>>
  HEADGOAL (sg `!x w. not_fresh_at target_cs x /\ lookup_var x m = SOME w ==>
                    lookup_var x q = SOME w`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`vx`,`vw`] >> strip_tac >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = lookup_var x m /\ _`
      (qspec_then `vx` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (fn th => pure_rewrite_tac[CONJUNCT1 th]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==>
                    lookup_var x q = SOME w`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`vx`,`vw`] >> strip_tac >>
    qpat_assum `!x w. not_fresh_at target_cs x /\ lookup_var x m = SOME w ==> _`
      (qspecl_then [`vx`,`vw`] match_mp_tac) >> conj_tac) >>>
  HEADGOAL (
    qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at target_cs x`
      (qspec_then `vx` match_mp_tac) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==>
                       lookup_var x m = SOME w`
      (qspecl_then [`vx`,`vw`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!n b sz. local_region cenv fin.scopes q n b sz <=>
                          local_region cenv mid.scopes m n b sz`) >>>
  HEADGOAL (
    `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by (irule EQ_SYM >> first_assum ACCEPT_TAC) >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`,
       `!x w. not_fresh_at target_cs x /\ lookup_var x m = SOME w ==> lookup_var x q = SOME w`,
       `MAP FDOM mid.scopes = MAP FDOM fin.scopes`,`local_ptrs_reserved cenv target_cs`] >>
    POP_ASSUM_LIST kall_tac >>
    metis_tac[tuplePlaceStepTheory.tuple_place_endpoint_local_regions_some]) >>>
  HEADGOAL (sg `return_buf_frame d cenv sm q`) >>>
  HEADGOAL (
    irule bodyMemoryDefsTheory.return_buf_frame_frame >>
    qexistsl [`cenv`,`u`,`cur`] >> simp[] >> decide_tac) >>>
  HEADGOAL (sg `alloca_history func q`) >>>
  HEADGOAL (
    qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`
      (assume_tac o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv) >>
    irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
    qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (m,Gmid,tmid) [] (OK q,Gq,tq)`
      (qspec_then `DF (storage_trace_horizon mid.storage_trace)` (irule_at Any)) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!fn inst z. frag_reachable ctx func q fn inst z ==> dalloca_no_wrap inst z`) >>>
  HEADGOAL (
    qpat_assum `body_inv tops ctx cenv cx`
      (mp_then Any mp_tac bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap) >>
    disch_then (qspecl_then [`func`,`q`] assume_tac) >> rpt strip_tac >>
    rename1 `frag_reachable ctx func q rf ri rz` >>
    qpat_assum `!fn inst u. MEM func ctx.ctx_functions /\ frag_reachable ctx func q fn inst u ==> _`
      (qspecl_then [`rf`,`ri`,`rz`] mp_tac) >>
    impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then ACCEPT_TAC) >>>
  HEADGOAL (sg `gas_admissible (bind (write_place cx place vi)
      (\u. assign_tuple_target_list cx todo vs_tail)) (stmt_res_ok lctx) mid`) >>>
  HEADGOAL (
    qpat_assum `mid with gas_obs := [] = mid` (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
    qpat_assum `assign_tuple_target_list cx (BaseTarget bt::todo) (vi::vs_tail) = _`
      (fn eq => qpat_assum `gas_admissible (assign_tuple_target_list cx
             (BaseTarget bt::todo) (vi::vs_tail)) _ src`
        (assume_tac o REWRITE_RULE [eq])) >>
    qpat_assum `gas_admissible (bind (eval_target_place cx bt) _) (stmt_res_ok lctx) src`
      (fn adm =>
        qpat_assum `!tail. eval_target_place cx bt
          (src with gas_obs := gas_explicit target_marks u.vs_gas_readings ++ tail) =
          (INL place,mid with gas_obs := tail)`
          (fn step => ACCEPT_TAC (BETA_RULE (MATCH_MP
            stmtSimForRoundsTheory.gas_admissible_bind_tail (CONJ adm step)))))) >>>
  HEADGOAL (sg `fin with gas_obs := [] = fin`) >>>
  HEADGOAL (
    qpat_assum `fin.gas_obs = []` mp_tac >>
    simp[vyperStateTheory.evaluation_state_component_equality]) >>>
  HEADGOAL (sg `gas_admissible (assign_tuple_target_list cx todo vs_tail) (stmt_res_ok lctx) fin`) >>>
  HEADGOAL (
    qpat_assum `fin with gas_obs := [] = fin` (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
    qpat_assum `gas_admissible (bind (write_place cx place vi) _) (stmt_res_ok lctx) mid`
      (fn adm =>
        qpat_assum `!tail. write_place cx place vi (mid with gas_obs := tail) =
          (INL (),fin with gas_obs := tail)`
          (fn step => ACCEPT_TAC (BETA_RULE (MATCH_MP
            (REWRITE_RULE [listTheory.APPEND] (Q.INST [`xs` |-> `[]`]
              stmtSimForRoundsTheory.gas_admissible_bind_tail)) (CONJ adm step)))))) >>>
  HEADGOAL (sg `assign_tuple_targets cx (BaseTarget bt) vi
      (src with gas_obs := gas_explicit target_marks u.vs_gas_readings) = (INL (),fin)`) >>>
  HEADGOAL (
    qpat_assum `eval_target_place cx bt (src with gas_obs := _) = (INL place,mid)` (fn target =>
      qpat_assum `write_place cx place vi mid = (INL (),fin)` (fn write =>
        simp[NoAsms,cj 56 vyperInterpreterTheory.evaluate_def,bind_def,target,write]))) >>>
  HEADGOAL (sg `body_tuple_targets_full_ok cx todo vs_tail`) >>>
  HEADGOAL (
    qpat_assum `(?(s:evaluation_state) x t.
      assign_tuple_targets cx (BaseTarget bt) vi s = (INL x,t)) ==>
      body_tuple_targets_full_ok cx todo vs_tail` match_mp_tac >>
    qexistsl [`src with gas_obs := gas_explicit target_marks u.vs_gas_readings`,`()`,`fin`] >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `storage_trace_domain cx st0 fin.storage_trace`) >>>
  HEADGOAL (asm_rewrite_tac[]) >>>
  HEADGOAL (Q.SUBGOAL_THEN `p + type_memory_size_list tvs <= w2n w' \/
    w2n w' + type_memory_size stv <= p` ASSUME_TAC) >>>
  HEADGOAL (
    qpat_assum `0 < type_memory_size stv` mp_tac >>
    qpat_assum `FST (SND target_r) = SOME LocMemory ==> _` (drule_then mp_tac) >>
    qpat_assum `SUM (MAP type_memory_size (TAKE k tvs)) + _ <= _` mp_tac >>
    decide_tac) >>>
  HEADGOAL (sg `!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`) >>>
  HEADGOAL (
    match_mp_tac (Q.SPECL [`tmid.t_mem`,`tq.t_mem`,`m.vs_memory`,`q.vs_memory`,
      `{i | w2n (w':256 word) <= i /\ i < w2n w' + type_memory_size stv}`,
      `TupleTV tvs`,`ArrayV (TupleV vs)`,`p`]
      robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame) >>
    rpt conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    simp[NoAsms, pred_setTheory.GSPECIFICATION] >>
    qpat_assum `val_wf (TupleTV tvs) (ArrayV (TupleV vs))`
      (mp_tac o MATCH_MP exprSimPropsTheory.val_footprint_le) >>
    simp[NoAsms,valueEncodingTheory.type_memory_size_def] >>
    qpat_assum `p + type_memory_size_list tvs <= _ \/ _` mp_tac >> decide_tac) >>>
  HEADGOAL (
    simp[NoAsms, pred_setTheory.GSPECIFICATION] >> rpt strip_tac >>
    irule placeMemoryCopyEffectTheory.typed_copy_effect_bytes >>
    qpat_assum `typed_copy_effect ctx func target_cs sm m q _ _` (irule_at Any) >>
    decide_tac) >>>
  HEADGOAL (
    qpat_assum `!j. ~(w2n (w':256 word) <= j /\ j < w2n w' + type_memory_size stv) ==>
      (j IN tq.t_mem <=> j IN tmid.t_mem)` mp_tac >>
    simp[NoAsms, pred_setTheory.GSPECIFICATION]) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (Q.SUBGOAL_THEN `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP q.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
        b <= p /\ p + type_memory_size_list tvs <= b + sz /\
        (!n a len. local_region cenv fin.scopes q n a len ==> b + sz <= a \/ a + len <= b)) \/
      (?n b sz. local_region cenv fin.scopes q n b sz /\ b <= p /\
        p + type_memory_size_list tvs <= b + sz /\ local_path_at cenv cx n (p-b) (TupleTV tvs))` ASSUME_TAC) >>>
  HEADGOAL (
    qpat_assum `!n b sz. local_region cenv fin.scopes q n b sz <=> _`
      (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `q.vs_allocas = m.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      DISJ_CASES_TAC >- (disj1_tac >> first_assum ACCEPT_TAC) >>
    disj2_tac >>
    qpat_assum `(?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      DISJ_CASES_TAC
    THENL [disj1_tac, disj2_tac >> first_assum ACCEPT_TAC]) >>>
  HEADGOAL (
    qpat_x_assum `?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _`
      (qx_choosel_then [`rid`,`rb`,`rsize`] strip_assume_tac) >>
    qexistsl [`rid`,`rb`,`rsize`] >> asm_rewrite_tac[] >> decide_tac) >>>
  HEADGOAL (sg `!i. i < LENGTH tys_tail ==>
      ?x. EL i ops_tail = Var x /\ not_fresh_at sm x /\ op_taint tq (Var x) = {} /\
          if is_word_type (EL i tys_tail) then
            lookup_var x q = SOME (typed_val_to_w256 (EL i tvs_tail) (EL i vs_tail)) /\
            op_prov Gq (Var x) = NONE
          else lookup_var x q =
                 SOME (n2w (p + SUM (MAP type_memory_size (TAKE (SUC k+i) tvs)))) /\
               ptr_covers Gq tq x q (type_memory_size (EL i tvs_tail))`) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!i. i < LENGTH (sty::tys_tail) ==> ?x. _ /\ not_fresh_at target_cs x /\ _`
      (qspec_then `SUC i` mp_tac) >>
    (impl_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
    disch_then (qx_choose_then `xp` strip_assume_tac o SRULE [listTheory.EL])) >>>
  HEADGOAL (
    `not_fresh_at sm xp` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists `target_cs` >> simp[]) >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = _ /\ _`
      (qspec_then `xp` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac) >>>
  HEADGOAL (
    `k + SUC i = SUC k + i` by decide_tac >>
    qexists `xp` >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- asm_rewrite_tac[])) >>>
  HEADGOAL (Cases_on `is_word_type (EL i tys_tail)`) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i tys_tail) then _ else _` mp_tac >>
    simp[ptrDisciplineTheory.op_prov_def]) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i tys_tail) then _ else _` mp_tac >>
    asm_rewrite_tac[] >> strip_tac >>
    asm_rewrite_tac[] >>
    irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
    qexistsl [`Gmid`,`m`,`tmid`] >> asm_rewrite_tac[]) >>>
  HEADGOAL (sg `alloca_frame cenv src cur u cenv mid m`) >>>
  HEADGOAL (
    match_mp_tac (Q.INST
      [`H` |-> `storage_trace_horizon src.storage_trace`,`ctx` |-> `ctx`,
       `cx` |-> `cx`,`func` |-> `func`]
      (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.alloca_frame_of_mem_frame)) >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      qpat_assum `mid.scopes = src.scopes` (fn eq => simp[NoAsms,eq])]) >>>
  HEADGOAL (
    qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_state_rel H ctx func cenv cx fin q /\ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    impl_tac >- asm_rewrite_tac[] >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (sg `alloca_frame cenv es sa s0 cenv mid m`) >>>
  HEADGOAL (
    irule stmtSimDefsTheory.alloca_frame_trans >>
    qexistsl [`cenv`,`src`,`u`,`cur`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP m.vs_allocas aid = SOME b`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`i`,`entry0`] >> disch_tac >>
    qpat_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP m.vs_allocas aid = SOME b`
      (qspecl_then [`i`,`entry0`] match_mp_tac) >>
    qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b`
      (qspecl_then [`i`,`entry0`] match_mp_tac) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `alloca_frame cenv es sa s0 cenv fin q`) >>>
  HEADGOAL (
    irule stmtSimDefsTheory.alloca_frame_trans >>
    qexistsl [`cenv`,`mid`,`m`,`target_cs`] >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>>
  HEADGOAL (
    `sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`sa.cs_next_id <= cur.cs_next_id`, `cur.cs_next_id <= target_cs.cs_next_id`,
         `target_cs.cs_next_id <= sm.cs_next_id`, `sa.cs_next_var <= cur.cs_next_var`,
         `cur.cs_next_var <= sm.cs_next_var`] >> decide_tac) >>
    `p + type_memory_size_list tvs <= q.vs_alloca_next /\
     s0.vs_alloca_next <= q.vs_alloca_next` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`q.vs_alloca_next = m.vs_alloca_next`, `u.vs_alloca_next <= m.vs_alloca_next`,
         `p + type_memory_size_list tvs <= u.vs_alloca_next`,
         `s0.vs_alloca_next <= u.vs_alloca_next`] >> decide_tac)) >>>
  HEADGOAL (
    `local_ptrs_reserved cenv sm` by
      (match_mp_tac (Q.SPECL [`cenv`,`target_cs`,`sm`] local_ptrs_reserved_next_var) >>
       conj_tac >> first_assum ACCEPT_TAC) >>
    `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x` by
      (rpt strip_tac >>
       match_mp_tac (Q.SPECL [`target_cs`,`sm`,`x`] freshWritesTheory.not_fresh_at_mono) >>
       reverse conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x`
         (qspecl_then [`x`,`cap`] match_mp_tac) >> first_assum ACCEPT_TAC) >>
    `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x` by
      (rpt strip_tac >>
       match_mp_tac (Q.SPECL [`target_cs`,`sm`,`x`] freshWritesTheory.not_fresh_at_mono) >>
       reverse conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x`
         (qspecl_then [`x`,`cap`] match_mp_tac) >> first_assum ACCEPT_TAC)) >>>
  HEADGOAL (sg `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w`) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==> lookup_var x q = SOME w`
      (qspecl_then [`x`,`w`] match_mp_tac) >>
    conj_tac
    >- (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cur x` match_mp_tac >>
        first_assum ACCEPT_TAC) >>
    qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w`
      (qspecl_then [`x`,`w`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!x. not_fresh_at sa x ==>
    FLOOKUP Gq x = FLOOKUP G0 x /\ op_taint tq (Var x) = op_taint tn0 (Var x)`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cur x` (drule_then assume_tac) >>
    qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at target_cs x` (drule_then assume_tac) >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!x. not_fresh_at cur x ==> FLOOKUP Gmid x = _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gu x = _ /\ _`
      (drule_then strip_assume_tac) >>
    asm_rewrite_tac[]) >>>
  HEADGOAL (sg `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b cap. local_region cenv es.scopes s0 n b cap ==> off+sz <= b \/ b+cap <= off) /\
    off <= i /\ i < off+sz /\ i IN tq.t_mem ==> i IN tn0.t_mem`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`old_id`,`old_base`,`old_size`,`byte`] >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
      (qspecl_then [`old_id`,`old_base`,`old_size`,`byte`] match_mp_tac) >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    `FLOOKUP u.vs_allocas old_id = SOME (old_base,old_size)` by
      (qpat_assum `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry`
         match_mp_tac >> first_assum ACCEPT_TAC) >>
    `FLOOKUP m.vs_allocas old_id = SOME (old_base,old_size)` by
      (qpat_assum `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP m.vs_allocas aid = SOME entry`
         match_mp_tac >> first_assum ACCEPT_TAC) >>
    `old_id < cur.cs_next_id /\ old_id < target_cs.cs_next_id` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`old_id < sa.cs_next_id`,`sa.cs_next_id <= cur.cs_next_id`,
         `cur.cs_next_id <= target_cs.cs_next_id`] >> decide_tac) >>
    qpat_assum `alloca_frame cenv es sa s0 cenv src u`
      (mp_tac o Q.SPECL [`old_id`,`old_base`,`old_size`] o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (assume_tac o CONJUNCT2) >>
    qpat_assum `alloca_frame cenv es sa s0 cenv mid m`
      (mp_tac o Q.SPECL [`old_id`,`old_base`,`old_size`] o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (assume_tac o CONJUNCT2)) >>>
  HEADGOAL (
    qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tu.t_mem`
      (qspecl_then [`old_id`,`old_base`,`old_size`,`byte`] match_mp_tac) >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    qpat_assum `!aid off sz i. FLOOKUP m.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tmid.t_mem`
      (qspecl_then [`old_id`,`old_base`,`old_size`,`byte`] match_mp_tac) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP q.vs_allocas aid = SOME entry` by
      (qpat_assum `q.vs_allocas = m.vs_allocas` (fn eq => rewrite_tac[eq]) >>
       first_assum ACCEPT_TAC) >>
    `EVERY (assignable_type (get_tenv cx)) tys_tail` by
      (qpat_assum `EVERY (assignable_type _) (sty::_)` mp_tac >> simp[NoAsms]) >>
    `values_have_types tvs_tail vs_tail` by simp[vyperTypeDefaultsTheory.values_have_types_LIST_REL]) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin q /\ storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin Gq tq q`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_state_rel H ctx func cenv cx fin q /\ _ /\ _ /\ alloca_frame cenv mid target_cs m cenv fin q /\ _`
      (drule_then strip_assume_tac) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qexistsl_tac [`Gq`,`q`,`tq`] >>
    gen_tac >> disch_tac >> conj_tac
    >- (qpat_assum `!D. gas_origin_ptr_path _ (m,Gmid,tmid) [] (OK q,Gq,tq)`
         (qspec_then `DF H` ACCEPT_TAC)) >>
    asm "suffix_ih" (qspecl_then
      [`tys_tail`,`tvs_tail`,`vs_tail`,`ops_tail`,`SUC k`,`p`,`sm`,`shadow_sm`,`fin`,`q`,`Gq`,`tq`]
      match_mp_tac) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, first_assum (ACCEPT_TAC o SYM)]) >>>
  HEADGOAL (
    sg `?tr slot tv. place = StoragePlace tr slot tv`) >>>
  HEADGOAL (
    qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' _ (Type sty)` mp_tac >>
    qpat_assum `FST (SND target_r) <> SOME LocMemory` mp_tac >>
    Cases_on `place` >> simp[NoAsms,place_ptr_rel_def]) >>>
  HEADGOAL (
    sg `w' = slot /\ FST (SND target_r) = SOME (slot_loc tr) /\ tv = stv`) >>>
  HEADGOAL (
    qpat_assum `place = StoragePlace tr slot tv` (fn eq =>
      qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' _ (Type sty)`
        (mp_tac o REWRITE_RULE [eq,place_ptr_rel_def])) >>
    qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
      (fn eq => simp[NoAsms,eq,EQ_SYM_EQ])) >>>
  HEADGOAL (
    `dest_loc = slot_loc tr` by simp[Abbr `dest_loc`] >>
    `write_storage_slot cx tr slot stv vi mid = (INL (),fin)` by
      (qpat_assum `write_place cx place vi mid = (INL (),fin)` mp_tac >>
       qpat_assum `place = StoragePlace tr slot tv` (fn eq =>
         qpat_assum `tv = stv` (fn ty => simp[NoAsms,eq,ty,write_place_def]))) >>
    `fin.storage_trace = mid.storage_trace` by
      (drule tuplePlaceStepTheory.write_place_storage_trace >> simp[]) >>
    `op_taint tmid (FST target_r) = {}` by
      (qpat_assum `bodyFullTargetDefs$target_ptr_ok cenv (PlaceR place) target_r Gmid tmid m`
        (ACCEPT_TAC o cj 1 o REWRITE_RULE [bodyFullTargetDefsTheory.target_ptr_ok_def]))) >>>
  HEADGOAL (sg `local_ptrs_reserved cenv target_cs /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x)`) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (
    match_mp_tac (Q.SPECL [`cenv`,`cur`,`target_cs`] local_ptrs_reserved_next_var) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (
    rpt strip_tac >>
    match_mp_tac (Q.SPECL [`cur`,`target_cs`,`x`] freshWritesTheory.not_fresh_at_mono) >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at cur x`
      (qspecl_then [`x`,`cap`] (fn th => match_mp_tac th)) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >>
    match_mp_tac (Q.SPECL [`cur`,`target_cs`,`x`] freshWritesTheory.not_fresh_at_mono) >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at cur x`
      (qspecl_then [`x`,`cap`] (fn th => match_mp_tac th)) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `gas_admissible (bind (write_place cx place vi)
      (\u. assign_tuple_target_list cx todo vs_tail)) (stmt_res_ok lctx) mid`) >>>
  HEADGOAL (
    qpat_assum `mid with gas_obs := [] = mid` (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
    qpat_assum `assign_tuple_target_list cx (BaseTarget bt::todo) (vi::vs_tail) = _`
      (fn eq => qpat_assum `gas_admissible (assign_tuple_target_list cx
             (BaseTarget bt::todo) (vi::vs_tail)) _ src`
        (assume_tac o REWRITE_RULE [eq])) >>
    qpat_assum `gas_admissible (bind (eval_target_place cx bt) _) (stmt_res_ok lctx) src`
      (fn adm =>
        qpat_assum `!tail. eval_target_place cx bt
          (src with gas_obs := gas_explicit target_marks u.vs_gas_readings ++ tail) =
          (INL place,mid with gas_obs := tail)`
          (fn step => ACCEPT_TAC (BETA_RULE (MATCH_MP
            stmtSimForRoundsTheory.gas_admissible_bind_tail (CONJ adm step)))))) >>>
  HEADGOAL (sg `fin with gas_obs := [] = fin`) >>>
  HEADGOAL (
    qpat_assum `fin.gas_obs = []` mp_tac >>
    simp[vyperStateTheory.evaluation_state_component_equality]) >>>
  HEADGOAL (sg `gas_admissible (assign_tuple_target_list cx todo vs_tail) (stmt_res_ok lctx) fin`) >>>
  HEADGOAL (
    qpat_assum `fin with gas_obs := [] = fin` (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
    qpat_assum `gas_admissible (bind (write_place cx place vi) _) (stmt_res_ok lctx) mid`
      (fn adm =>
        qpat_assum `!tail. write_place cx place vi (mid with gas_obs := tail) =
          (INL (),fin with gas_obs := tail)`
          (fn step => ACCEPT_TAC (BETA_RULE (MATCH_MP
            (REWRITE_RULE [listTheory.APPEND] (Q.INST [`xs` |-> `[]`]
              stmtSimForRoundsTheory.gas_admissible_bind_tail)) (CONJ adm step)))))) >>>
  HEADGOAL (sg `assign_tuple_targets cx (BaseTarget bt) vi
      (src with gas_obs := gas_explicit target_marks u.vs_gas_readings) = (INL (),fin)`) >>>
  HEADGOAL (
    qpat_assum `eval_target_place cx bt (src with gas_obs := _) = (INL place,mid)` (fn target =>
      qpat_assum `write_place cx place vi mid = (INL (),fin)` (fn write =>
        simp[NoAsms,cj 56 vyperInterpreterTheory.evaluate_def,bind_def,target,write]))) >>>
  HEADGOAL (sg `body_tuple_targets_full_ok cx todo vs_tail`) >>>
  HEADGOAL (
    qpat_assum `(?(s:evaluation_state) x t.
      assign_tuple_targets cx (BaseTarget bt) vi s = (INL x,t)) ==>
      body_tuple_targets_full_ok cx todo vs_tail` match_mp_tac >>
    qexistsl [`src with gas_obs := gas_explicit target_marks u.vs_gas_readings`,`()`,`fin`] >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (Q.SUBGOAL_THEN `?q Gq tq.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (m,Gmid,tmid) [] (OK q,Gq,tq)) /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_state_rel H ctx func cenv cx fin q /\ storage_well_formed_on cx fin (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx fin Gq tq q) /\
    (!x. not_fresh_at target_cs x ==>
      lookup_var x q = lookup_var x m /\ FLOOKUP Gq x = FLOOKUP Gmid x /\
      op_taint tq (Var x) = op_taint tmid (Var x)) /\
    fin.scopes = mid.scopes /\
    q.vs_memory = m.vs_memory /\ q.vs_allocas = m.vs_allocas /\
    q.vs_alloca_next = m.vs_alloca_next /\ tq.t_mem = tmid.t_mem /\
    ~block_is_terminated sm /\ ~q.vs_halted /\
    q.vs_current_bb = sm.cs_current_bb /\ q.vs_inst_idx = LENGTH sm.cs_current_insts /\
    return_buf_frame d cenv sm q /\ alloca_history func q /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp q)`
    (qx_choosel_then [`q`,`Gq`,`tq`] (map_every assume_tac o CONJUNCTS))) >>>
  HEADGOAL (Cases_on `is_word_type sty`) >>>
  HEADGOAL (
    sg `compile_store_at_loc cenv.ce_imm_alloca (FST target_r) op0
      (SOME (slot_loc tr)) target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `head_store target_cs = ((),sm)` mp_tac >>
    qpat_assum `FST (SND target_r) = SOME (slot_loc tr)` (fn loc =>
      qpat_assum `is_word_type sty` (fn word =>
        simp[NoAsms,Abbr `head_store`,loc,word]))) >>>
  HEADGOAL (
    `encode_value stv vi = SOME [(0,typed_val_to_w256 stv vi)]` by
      (mp_tac (Q.SPECL [`get_tenv cx`,`sty`,`stv`,`vi`]
         stmtSimAssignStorageFactsTheory.encode_value_word_typed) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
       disch_then ACCEPT_TAC)) >>>
  HEADGOAL (sg `~cx.txn.is_static`) >>>
  HEADGOAL (
    qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),fin)`
      (fn write => POP_ASSUM_LIST (K all_tac) >> mp_tac write) >>
    pure_rewrite_tac[vyperStorageBackendTheory.write_storage_slot_eq] >>
    Cases_on `cx.txn.is_static` >> simp[]) >>>
  HEADGOAL (
    qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),fin)`
      (assume_tac o MATCH_MP vyperScopePreservationTheory.write_storage_slot_scopes)) >>>
  HEADGOAL (
    `type_slot_size stv = 1` by
      (mp_tac (Q.SPECL [`get_tenv cx`,`sty`,`stv`]
         exprSimUnwrapTheory.word_type_slot_size) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
       disch_then ACCEPT_TAC) >>
    `eval_operand op0 m = SOME (typed_val_to_w256 stv vi)` by
      (qpat_assum `if is_word_type sty then _ else _` mp_tac >>
       qpat_assum `op0 = Var xs` (fn eq =>
         qpat_assum `is_word_type sty` (fn word =>
           simp[NoAsms,eq,word,eval_operand_def]))) >>
    `op_taint tmid op0 = {}` by simp[] >>
    `eval_operand (FST target_r) m = SOME slot` by simp[]) >>>
  HEADGOAL (
    `~m.vs_call_ctx.cc_static` by
      (qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`
        (mp_tac o MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel o
          MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel) >>
       simp[call_ctx_rel_def]) >>
    `allocas_from lo m /\ lo <= m.vs_alloca_next` by
      (qpat_assum `ghost_inv_at _ lo d cenv cx mid Gmid tmid m` mp_tac >>
       simp[NoAsms,ghost_inv_at_def] >> strip_tac >> simp[])) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
    !word mem. storage_dead H tr (update_storage slot word mem) = storage_dead H tr mem`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    `valid_horizon cx st0 H mid.storage_trace` by
      (qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _` irule >>
       first_assum ACCEPT_TAC) >>
    qpat_assum `eval_target_place cx bt _ = (INL place,mid)` (fn run =>
      qpat_assum `place = StoragePlace tr slot tv` (fn eq =>
        qpat_assum `tv = stv` (fn ty =>
          qpat_assum `valid_horizon cx st0 H mid.storage_trace` (fn horizon =>
            qpat_assum `type_slot_size stv = 1` (fn size =>
              ACCEPT_TAC (MATCH_MP
                stmtSimAugAssignPlaceStorageTheory.aug_place_target_storage_dead_stable
                (LIST_CONJ [REWRITE_RULE [eq,ty] run,horizon,size])))))))) >>>
  HEADGOAL (
    mp_tac (Q.INST
      [`dst` |-> `FST (target_r : operand # data_location option # place_ty option)`,
       `value` |-> `op0`, `sa` |-> `target_cs`,
       `sb` |-> `sm`, `s` |-> `m`, `tn` |-> `tmid`, `tv` |-> `stv`,
       `w` |-> `typed_val_to_w256 stv vi`, `v` |-> `vi`, `es` |-> `mid`,
       `es'` |-> `fin`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
       `G` |-> `Gmid`]
       (REWRITE_RULE [GSYM slot_loc_def]
         (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
           body_assign_tuple_storage_head_path))) >>
    impl_tac) >>>
  HEADGOAL (rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    disch_then (qx_choose_then `q` (qx_choose_then `tq` (fn endpoint =>
      let
        val state_rule = cj 4 endpoint
        val ghost_rule = cj 5 endpoint
      in
        strip_assume_tac endpoint >>
        mk_asm "storage_word_state" state_rule >>
        mk_asm "storage_word_ghost" ghost_rule
      end)))) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin q /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin Gmid tq q`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!K. valid_horizon cx st0 K fin.storage_trace ==>
                    valid_horizon cx st0 K mid.storage_trace`
      (drule_then assume_tac) >>
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==>
      targetQ K (INL place) mid Gmid tmid m /\ _` (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `Abbrev (targetQ = _)` (fn th =>
      CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
    BETA_TAC >> simp[NoAsms] >> strip_tac) >>>
  HEADGOAL (
    qpat_assum `target_post H ctx func cenv cx src cur target_cs u mid (PlaceR place) (Type sty) target_r m`
      (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
    qpat_assum `!K. valid_horizon cx st0 K fin.storage_trace ==>
      !word mem. storage_dead K tr (update_storage slot word mem) = storage_dead K tr mem`
      (qspec_then `H` (fn guard =>
        qpat_assum `valid_horizon cx st0 H fin.storage_trace`
          (assume_tac o MATCH_MP guard))) >>
    qpat_assum `!K. dead_lo_ok K (DF K) lo cenv cx`
      (qspec_then `H` assume_tac)) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (asm "storage_word_state" match_mp_tac) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (reverse conj_tac) >>>
  HEADGOAL (
    asm "storage_word_ghost" (fn store =>
      qpat_assum `dead_lo_ok H (DF H) lo cenv cx` (fn lo_ok =>
        qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid Gmid tmid m` (fn ghost =>
          qpat_assum `!word mem. storage_dead H tr (update_storage slot word mem) = storage_dead H tr mem`
            (fn dead => ACCEPT_TAC (MATCH_MP store (LIST_CONJ [lo_ok,ghost,dead]))))))) >>>
  HEADGOAL (
    qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
      (assume_tac o MATCH_MP vyperTypeValuesTheory.evaluate_type_well_formed_type_value) >>
    sg `!tr slot leaf. place = StoragePlace tr slot leaf ==>
      well_formed_type_value leaf /\ value_has_type leaf vi`) >>>
  HEADGOAL (
    qpat_assum `place = StoragePlace tr slot tv` (fn eq =>
      qpat_assum `tv = stv` (fn ty => simp[NoAsms,eq,ty])) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `eval_base_place cx bt _ = (INL (PlaceR place),mid)` (fn run =>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace` (fn horizon =>
        qpat_assum `storage_well_formed_on cx mid (FST H)` (fn wf =>
          qpat_assum `!tr slot leaf. place = StoragePlace tr slot leaf ==> _` (fn fits =>
            qpat_assum `write_place cx place vi mid = (INL (),fin)` (fn write =>
              ACCEPT_TAC (MATCH_MP tuplePlaceStepTheory.tuple_place_write_storage_wf
                (LIST_CONJ [run,horizon,wf,fits,write])))))))) >>>
  HEADGOAL (sg `alloca_history func q`) >>>
  HEADGOAL (
    qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`
      (assume_tac o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv) >>
    irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
    qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (m,Gmid,tmid) [] (OK q,Gmid,tq)`
      (qspec_then `DF (storage_trace_horizon mid.storage_trace)` (irule_at Any)) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `~block_is_terminated sm`) >>>
  HEADGOAL (
    qpat_assum `compile_store_at_loc cenv.ce_imm_alloca (FST target_r) op0
      (SOME (slot_loc tr)) target_cs = ((),sm)` mp_tac >>
    Cases_on `tr` >>
    simp[NoAsms,slot_loc_def,compile_store_at_loc_def] >>
    disch_then (mp_tac o MATCH_MP exprOpenPrimitivesTheory.emit_void_terminated) >>
    simp[NoAsms,is_terminator_def]) >>>
  HEADGOAL (sg `q.vs_initial_fmp = m.vs_initial_fmp`) >>>
  HEADGOAL (
    qpat_assum `q = (_ with vs_inst_idx := _)` mp_tac >>
    Cases_on `tr` >> simp[NoAsms,tstore_def,sstore_def] >>
    disch_then (fn eq => rewrite_tac[eq,tstore_def,sstore_def])) >>>
  HEADGOAL (sg `ctx_has_dalloca ctx ==> allocas_below_fmp q`) >>>
  HEADGOAL (
    qpat_assum `q.vs_initial_fmp = m.vs_initial_fmp` (fn initial =>
      qpat_assum `q.vs_fmp = m.vs_fmp` (fn fmp =>
        qpat_assum `q.vs_allocas = m.vs_allocas` (fn allocas =>
          pure_rewrite_tac[allocas_below_fmp_def,initial,fmp,allocas]))) >>
    qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp m`
      (ACCEPT_TAC o PURE_REWRITE_RULE [allocas_below_fmp_def])) >>>
  HEADGOAL (sg `return_buf_frame d cenv sm q`) >>>
  HEADGOAL (
    irule bodyMemoryDefsTheory.return_buf_frame_frame >>
    qexistsl [`cenv`,`u`,`cur`] >> simp[] >> decide_tac) >>>
  HEADGOAL (qexistsl_tac [`q`,`Gmid`,`tq`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      gen_tac >> disch_tac >>
      qpat_assum `!x. lookup_var x q = lookup_var x m /\ _`
        (qspec_then `x` strip_assume_tac) >> asm_rewrite_tac[]]) >>>
  HEADGOAL (
    sg `compile_assign_value cenv (FST target_r) (slot_loc tr) op0 F
      NONE sty sty (type_memory_bytes cenv sty) target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `head_store target_cs = ((),sm)` mp_tac >>
    qpat_assum `dest_loc = slot_loc tr` (fn loc =>
      qpat_assum `~is_word_type sty` (fn word =>
        simp[NoAsms,Abbr `head_store`,loc,word]))) >>>
  HEADGOAL (
    sg `compile_store_slots cenv op0 (FST target_r) sty tr target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `compile_assign_value cenv (FST target_r) (slot_loc tr) op0 F
      NONE sty sty (type_memory_bytes cenv sty) target_cs = ((),sm)` mp_tac >>
    Cases_on `tr` >>
    simp[NoAsms,slot_loc_def,compile_assign_value_def,comp_bind_def,comp_return_def]) >>>
  HEADGOAL (
    `LENGTH vs = LENGTH tvs` by
      (irule vyperTypingTheory.values_have_types_length >> simp[]) >>
    `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
             tuple_in_memory vs tvs p mem` by
      (qpat_assum `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
                         val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [Once valueEncodingDefsTheory.val_in_memory_def])) >>
    `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
             val_in_memory stv vi (p + SUM (MAP type_memory_size (TAKE k tvs))) mem` by
      (qspecl_then [`vs`,`tvs`,`p`,`m.vs_memory`,`tmid`,`k`] mp_tac
         typedCopyLayoutPtrTheory.tuple_in_memory_robust_element >> simp[])) >>>
  HEADGOAL (
    `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size stv <=
     type_memory_size_list tvs` by
      (drule tupleMemoryLayoutTheory.tuple_element_interval >>
       simp[valueEncodingProofsTheory.type_memory_size_list_sum])) >>>
  HEADGOAL (
    `m.vs_alloca_next < dimword (:256)` by
      (qpat_assum `stmt_state_rel _ _ _ _ _ mid m`
         (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room) >>
       disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
    qabbrev_tac `addr = p + SUM (MAP type_memory_size (TAKE k tvs))` >>
    `addr + type_memory_size stv <= m.vs_alloca_next` by
      (qpat_assum `p + type_memory_size_list tvs <= u.vs_alloca_next` mp_tac >>
       qpat_assum `u.vs_alloca_next <= m.vs_alloca_next` mp_tac >>
       qpat_assum `SUM (MAP type_memory_size (TAKE k tvs)) + _ <= _` mp_tac >>
       simp[NoAsms,Abbr `addr`] >> decide_tac) >>
    `addr < dimword (:256)` by
      (qpat_assum `addr + _ <= m.vs_alloca_next` mp_tac >>
       qpat_assum `m.vs_alloca_next < dimword (:256)` mp_tac >> decide_tac) >>
    `w2n (n2w addr : 256 word) = addr` by
      simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>>
  HEADGOAL (
    qpat_assum `body_inv tops ctx cenv cx`
      (mp_then Any mp_tac immutableDeployAssignRangesTheory.immutable_assign_copy_metadata) >>
    qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
      disch_then (strip_assume_tac o (fn rule => MATCH_MP rule inv)))) >>>
  HEADGOAL (
    qpat_assum `if is_word_type sty then _ else _` (fn cases =>
      qpat_assum `~is_word_type sty` (fn word =>
        strip_assume_tac (REWRITE_RULE [word] cases)))) >>>
  HEADGOAL (
    sg `eval_operand op0 m = SOME (n2w addr) /\ op_taint tmid op0 = {} /\
        ptr_covers Gmid tmid xs m (type_memory_size stv)`) >>>
  HEADGOAL (
    qpat_assum `op0 = Var xs` (fn op_eq => rewrite_tac[op_eq,eval_operand_def]) >>
    conj_tac >- (simp[NoAsms,Abbr `addr`] >> first_assum ACCEPT_TAC) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!x. op0 = Var x \/ FST target_r = Var x ==> not_fresh_at target_cs x`) >>>
  HEADGOAL (
    gen_tac >> disch_then DISJ_CASES_TAC
    >- (qpat_assum `op0 = Var xs` (fn eq => fs[eq])) >>
    qpat_assum `!x. FST target_r = Var x ==> not_fresh_at target_cs x` irule >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `~cx.txn.is_static`) >>>
  HEADGOAL (
    qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),fin)`
      (fn write => POP_ASSUM_LIST (K all_tac) >> mp_tac write) >>
    pure_rewrite_tac[vyperStorageBackendTheory.write_storage_slot_eq] >>
    Cases_on `cx.txn.is_static` >> simp[]) >>>
  HEADGOAL (sg `?writes. encode_value stv vi = SOME writes`) >>>
  HEADGOAL (
    qpat_assum `~cx.txn.is_static` (fn normal =>
      qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),fin)`
        (mp_tac o REWRITE_RULE [vyperStorageBackendTheory.write_storage_slot_eq,normal])) >>
    Cases_on `encode_value stv vi` >> simp[]) >>>
  HEADGOAL (
    qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`
      (assume_tac o CONJUNCT2 o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
    sg `~m.vs_call_ctx.cc_static /\ allocas_from lo m /\ lo <= m.vs_alloca_next`) >>>
  HEADGOAL (conj_tac) >>>
  HEADGOAL (
    qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`
      (fn state =>
        let
          val relation = MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel
            (MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel state)
          val static = cj 5 (REWRITE_RULE [call_ctx_rel_def] relation)
        in
          rewrite_tac[static]
        end) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `ghost_inv_at _ lo d cenv cx mid Gmid tmid m`
      (fn th => let val post = REWRITE_RULE [ghost_inv_at_def] th
                in ACCEPT_TAC (CONJ (cj 7 post) (cj 8 post)) end)) >>>
  HEADGOAL (sg `return_buf_frame d cenv target_cs m`) >>>
  HEADGOAL (
    irule bodyMemoryDefsTheory.return_buf_frame_frame >>
    qexistsl [`cenv`,`u`,`cur`] >> simp[]) >>>
  HEADGOAL (sg `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at target_cs x`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `local_ptrs_reserved cenv target_cs` (fn reserved =>
      qpat_assum `cenv.ce_imm_alloca = SOME (Var x)` (fn base =>
        ACCEPT_TAC (MATCH_MP local_ptrs_reserved_imm_base (CONJ reserved base))))) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H mid.storage_trace ==>
    storage_place_observed H (StoragePlace tr slot stv) /\ regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H)`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `eval_base_place cx bt _ = (INL (PlaceR place),mid)` (fn reached =>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace` (fn horizon =>
        qpat_assum `place = StoragePlace tr slot tv` (fn place_eq =>
          qpat_assum `tv = stv` (fn ty =>
            ACCEPT_TAC (REWRITE_RULE [place_eq,ty]
              (MATCH_MP tuplePlacePointerReadyTheory.tuple_place_pointer_storage_facts
                (CONJ reached horizon)))))))) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H mid.storage_trace ==> 0 < type_slot_size stv ==>
    ?rootk root path delta. MEM (tr,rootk,root) (FST H) /\
      storage_subregion root path delta stv /\ w2n slot = w2n rootk + delta`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==>
      storage_place_observed K (StoragePlace tr slot stv) /\ _`
      (drule_then strip_assume_tac) >>
    disch_tac >>
    qpat_assum `storage_place_observed H (StoragePlace tr slot stv)` (fn observed =>
      qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
        qpat_assum `regions_consistent (FST H)` (fn regions =>
          qpat_assum `0 < type_slot_size stv` (fn size =>
            ACCEPT_TAC (MATCH_MP tuplePlaceValueStorageFrameTheory.tuple_place_storage_leaf_horizon
              (LIST_CONJ [observed,inv,regions,size]))))))) >>>
  HEADGOAL (sg `w2n slot + type_slot_size stv <= dimword (:256)`) >>>
  HEADGOAL (Cases_on `type_slot_size stv = 0`) >>>
  HEADGOAL (
    asm_rewrite_tac[arithmeticTheory.ADD_0] >>
    irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >> simp[wordsTheory.w2n_lt]) >>>
  HEADGOAL (
    `0 < type_slot_size stv` by
      (qpat_assum `type_slot_size stv <> 0` mp_tac >> decide_tac) >>
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> 0 < type_slot_size stv ==>
      ?rootk root path delta. _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (qx_choosel_then [`rk`,`root_ty`,`piece`,`delta`] strip_assume_tac)) >>>
  HEADGOAL (
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
      storage_place_observed H (StoragePlace tr slot stv) /\ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>>
  HEADGOAL (
    qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
      qpat_assum `MEM (tr,rk,root_ty) (FST (storage_trace_horizon mid.storage_trace))` (fn root =>
        qpat_assum `regions_consistent (FST (storage_trace_horizon mid.storage_trace))` (fn consistent =>
          qpat_assum `storage_subregion root_ty piece delta stv` (fn region =>
            qpat_assum `0 < type_slot_size stv` (fn size =>
              mp_tac (MATCH_MP placeStoreStorageTheory.place_store_storage_leaf_bounds
                (LIST_CONJ [inv,root,consistent,region,size]))))))) >>
    qpat_assum `w2n slot = w2n rk + delta` (fn eq => simp[NoAsms,eq])) >>>
  HEADGOAL (sg `eval_operand (FST target_r) m = SOME slot`) >>>
  HEADGOAL (fs[]) >>>
  HEADGOAL (sg `type_memory_size stv <> 0 ==>
    ?x. op0 = Var x /\ ptr_covers Gmid tmid x m (type_memory_size stv)`) >>>
  HEADGOAL (disch_tac >> qexists_tac `xs` >> conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (Q.SUBGOAL_THEN
    `type_memory_size stv = 0 \/ w2n (n2w addr:256 word) + type_memory_size stv <= m.vs_alloca_next`
    ASSUME_TAC) >>>
  HEADGOAL (
    disj2_tac >>
    qpat_assum `w2n (n2w addr:256 word) = addr` (fn eq => pure_rewrite_tac[eq]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `w2n (n2w addr:256 word) + type_memory_size stv < dimword (:256)`) >>>
  HEADGOAL (
    qpat_assum `w2n (n2w addr:256 word) = addr` (fn eq => pure_rewrite_tac[eq]) >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`addr + type_memory_size stv <= m.vs_alloca_next`, `m.vs_alloca_next < dimword (:256)`] >>
    decide_tac) >>>
  HEADGOAL (sg `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
    val_in_memory stv vi (w2n (n2w addr:256 word)) mem`) >>>
  HEADGOAL (
    qpat_assum `w2n (n2w addr:256 word) = addr` (fn eq => pure_rewrite_tac[eq]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    mp_tac (Q.INST [
      `ty` |-> `sty`, `tv` |-> `stv`, `v` |-> `vi`, `tr` |-> `tr`,
      `src` |-> `op0`, `dst` |-> `FST (target_r : operand # data_location option # place_ty option)`,
      `sw` |-> `n2w addr : 256 word`, `dw` |-> `slot : 256 word`,
      `sa` |-> `target_cs`, `sb` |-> `sm`, `s` |-> `m`,
      `G` |-> `Gmid`, `tn` |-> `tmid`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
      (SPEC_ALL bodyFullAssignTopCopyTailTheory.body_assign_slots_full_frame_path)) >>
    impl_tac) >>>
  HEADGOAL (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    disch_then (qx_choosel_then [`q`,`written_slots`,`Gq`,`tq`] (fn endpoint =>
      let val facts = CONJUNCTS endpoint
      in
        map_every assume_tac (List.take (facts,length facts - 1)) >>
        mk_asm "storage_aggregate_post" (List.last facts)
      end))) >>>
  HEADGOAL (
    qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),fin)`
      (assume_tac o MATCH_MP vyperScopePreservationTheory.write_storage_slot_scopes) >>
    qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
      (assume_tac o MATCH_MP vyperTypeValuesTheory.evaluate_type_well_formed_type_value) >>
    sg `!tr slot leaf. place = StoragePlace tr slot leaf ==>
      well_formed_type_value leaf /\ value_has_type leaf vi`) >>>
  HEADGOAL (
    qpat_assum `place = StoragePlace tr slot tv` (fn eq =>
      qpat_assum `tv = stv` (fn ty => simp[NoAsms,eq,ty])) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin q /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin Gq tq q`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `fin.storage_trace = mid.storage_trace` (fn trace =>
      qpat_assum `valid_horizon cx st0 H fin.storage_trace`
        (assume_tac o REWRITE_RULE [trace])) >>
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==>
      targetQ K (INL place) mid Gmid tmid m /\ _` (qspec_then `H` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `Abbrev (targetQ = _)` (fn eq =>
      CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] eq]))) >>
    BETA_TAC >> simp[NoAsms] >> strip_tac) >>>
  HEADGOAL (
    qpat_assum `target_post H ctx func cenv cx src cur target_cs u mid (PlaceR place) (Type sty) target_r m`
      (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
    qpat_assum `!K. dead_lo_ok K (DF K) lo cenv cx` (qspec_then `H` assume_tac) >>
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==>
      storage_place_observed K (StoragePlace tr slot stv) /\ _`
      (drule_then strip_assume_tac)) >>>
  HEADGOAL (Q.SUBGOAL_THEN
    `?rk rt region_path off. 0 < type_slot_size stv ==>
        MEM (tr,rk,rt) (FST H) /\ regions_consistent (FST H) /\
        storage_locks_separated (FST H) (SND H) /\ storage_subregion rt region_path off stv /\
        w2n slot = w2n rk + off`
    (qx_choosel_then [`rk`,`rt`,`region_path`,`off`] assume_tac)) >>>
  HEADGOAL (Cases_on `0 < type_slot_size stv`) >>>
  HEADGOAL (
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==> 0 < type_slot_size stv ==>
      ?rootk root path delta. _` (qspec_then `H` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (qx_choosel_then [`rootk`,`root`,`path`,`delta`] strip_assume_tac) >>
    qexistsl_tac [`rootk`,`root`,`path`,`delta`] >> asm_rewrite_tac[]) >>>
  HEADGOAL (qexistsl_tac [`ARB`,`ARB`,`ARB`,`0`] >> asm_rewrite_tac[]) >>>
  HEADGOAL (
    asm "storage_aggregate_post" (qspecl_then [`H`,`mid`,`env`,`rk`,`rt`,`region_path`,`off`] mp_tac) >>
    impl_tac) >>>
  HEADGOAL (rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    disch_then (qx_choose_then `ef` strip_assume_tac) >>
    sg `ef = fin`) >>>
  HEADGOAL (
    qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),ef)` mp_tac >>
    qpat_assum `write_storage_slot cx tr slot stv vi mid = (INL (),fin)` (fn eq => simp[NoAsms,eq])) >>>
  HEADGOAL (
    qpat_x_assum `ef = fin` SUBST_ALL_TAC >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    qpat_assum `eval_base_place cx bt _ = (INL (PlaceR place),mid)` (fn run =>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace` (fn horizon =>
        qpat_assum `storage_well_formed_on cx mid (FST H)` (fn wf =>
          qpat_assum `!tr slot leaf. place = StoragePlace tr slot leaf ==> _` (fn fits =>
            qpat_assum `write_place cx place vi mid = (INL (),fin)` (fn write =>
              ACCEPT_TAC (MATCH_MP tuplePlaceStepTheory.tuple_place_write_storage_wf
                (LIST_CONJ [run,horizon,wf,fits,write])))))))) >>>
  HEADGOAL (sg `~block_is_terminated sm`) >>>
  HEADGOAL (
    qpat_assum `compile_store_slots cenv op0 (FST target_r) sty tr target_cs = ((),sm)` (fn compile =>
      qpat_assum `acyclic_struct_metadata cenv.ce_struct_fields` (fn metadata =>
        ACCEPT_TAC (MATCH_MP (cj 1 stmtSimAssignStorageSparseTheory.store_slots_open)
          (CONJ compile metadata))))) >>>
  HEADGOAL (qexistsl_tac [`q`,`Gq`,`tq`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    sg `expr_sim_inv cenv cx env fin /\ fin with gas_obs := [] = fin /\
        storage_trace_domain cx st0 fin.storage_trace`) >>>
  HEADGOAL (
    rpt conj_tac
    >- (irule tuplePlaceSourceTheory.tuple_place_write_inv >>
        qexistsl_tac [`place`,`INL ()`,`mid`,`stv`,`vi`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)
    >- (qpat_assum `fin.gas_obs = []` (fn obs =>
          simp[NoAsms,GSYM obs])) >>
    qpat_assum `fin.storage_trace = mid.storage_trace`
      (fn eq => pure_rewrite_tac[eq]) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    sg `!x. not_fresh_at sa x ==> not_fresh_at cur x`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists `sa` >> simp[]) >>>
  HEADGOAL (sg `!x. not_fresh_at cur x ==> not_fresh_at target_cs x`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists_tac `cur` >> simp[]) >>>
  HEADGOAL (sg `!n b sz. local_region cenv fin.scopes q n b sz <=>
                          local_region cenv mid.scopes m n b sz`) >>>
  HEADGOAL (
    qpat_assum `fin.scopes = mid.scopes` (fn eq => pure_rewrite_tac[eq]) >>
    map_every qx_gen_tac [`n`,`b`,`sz`] >>
    match_mp_tac (Q.SPECL [`cenv`,`target_cs`,`m`,`q`,`mid.scopes`,`n`,`b`,`sz`]
      exprSimCopyTheory.copy_buffer_local_region_frame) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt strip_tac >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = lookup_var x m /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1))) >>>
  HEADGOAL (sg `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==>
                       lookup_var x q = SOME w`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`vx`,`vw`] >> strip_tac >>
    qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at target_cs x`
      (drule_then assume_tac) >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = lookup_var x m /\ _`
      (drule_then (fn th => pure_rewrite_tac[CONJUNCT1 th])) >>
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==>
                       lookup_var x m = SOME w`
      (qspecl_then [`vx`,`vw`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!fn inst z. frag_reachable ctx func q fn inst z ==> dalloca_no_wrap inst z`) >>>
  HEADGOAL (
    qpat_assum `body_inv tops ctx cenv cx`
      (mp_then Any mp_tac bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap) >>
    disch_then (qspecl_then [`func`,`q`] assume_tac) >> rpt strip_tac >>
    rename1 `frag_reachable ctx func q rf ri rz` >>
    qpat_assum `!fn inst u. MEM func ctx.ctx_functions /\ frag_reachable ctx func q fn inst u ==> _`
      (qspecl_then [`rf`,`ri`,`rz`] mp_tac) >>
    impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then ACCEPT_TAC) >>>
  HEADGOAL (sg `!mem. mem_agree_outside tq.t_mem q.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`) >>>
  HEADGOAL (
    qpat_assum `tq.t_mem = tmid.t_mem` (fn taint =>
      qpat_assum `q.vs_memory = m.vs_memory` (fn mem =>
        pure_rewrite_tac[taint,mem])) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (Q.SUBGOAL_THEN `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP q.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
        b <= p /\ p + type_memory_size_list tvs <= b + sz /\
        (!n a len. local_region cenv fin.scopes q n a len ==> b + sz <= a \/ a + len <= b)) \/
      (?n b sz. local_region cenv fin.scopes q n b sz /\ b <= p /\
        p + type_memory_size_list tvs <= b + sz /\ local_path_at cenv cx n (p-b) (TupleTV tvs))` ASSUME_TAC) >>>
  HEADGOAL (
    qpat_assum `!n b sz. local_region cenv fin.scopes q n b sz <=> _`
      (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `q.vs_allocas = m.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      DISJ_CASES_TAC >- (disj1_tac >> first_assum ACCEPT_TAC) >>
    disj2_tac >>
    qpat_assum `(?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      DISJ_CASES_TAC
    THENL [disj1_tac, disj2_tac >> first_assum ACCEPT_TAC]) >>>
  HEADGOAL (
    qpat_x_assum `?aid b sz. FLOOKUP m.vs_allocas aid = SOME (b,sz) /\ _`
      (qx_choosel_then [`rid`,`rb`,`rsize`] strip_assume_tac) >>
    qexistsl [`rid`,`rb`,`rsize`] >> asm_rewrite_tac[] >> decide_tac) >>>
  HEADGOAL (sg `!i. i < LENGTH tys_tail ==>
      ?x. EL i ops_tail = Var x /\ not_fresh_at sm x /\ op_taint tq (Var x) = {} /\
          if is_word_type (EL i tys_tail) then
            lookup_var x q = SOME (typed_val_to_w256 (EL i tvs_tail) (EL i vs_tail)) /\
            op_prov Gq (Var x) = NONE
          else lookup_var x q =
                 SOME (n2w (p + SUM (MAP type_memory_size (TAKE (SUC k+i) tvs)))) /\
               ptr_covers Gq tq x q (type_memory_size (EL i tvs_tail))`) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!i. i < LENGTH (sty::tys_tail) ==> ?x. _ /\ not_fresh_at target_cs x /\ _`
      (qspec_then `SUC i` mp_tac) >>
    (impl_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC)) >>
    disch_then (qx_choose_then `xp` strip_assume_tac o SRULE [listTheory.EL])) >>>
  HEADGOAL (
    `not_fresh_at sm xp` by
      (irule freshWritesTheory.not_fresh_at_mono >> qexists `target_cs` >> simp[]) >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = lookup_var x m /\ _`
      (qspec_then `xp` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>>
  HEADGOAL (
    `k + SUC i = SUC k + i` by decide_tac >>
    qexists `xp` >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- asm_rewrite_tac[])) >>>
  HEADGOAL (Cases_on `is_word_type (EL i tys_tail)`) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i tys_tail) then _ else _` (fn values =>
      qpat_assum `is_word_type (EL i tys_tail)` (fn ty => rewrite_tac[ty] >> mp_tac (REWRITE_RULE [ty] values))) >>
    strip_tac >> conj_tac) >>>
  HEADGOAL (
    qpat_assum `lookup_var xp q = lookup_var xp m` (fn eq => pure_rewrite_tac[eq]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `op_prov Gmid (Var xp) = NONE` mp_tac >>
    qpat_assum `FLOOKUP (Gq:(string,num # num) fmap) xp = FLOOKUP Gmid xp`
      (fn provenance => simp[NoAsms,ptrDisciplineTheory.op_prov_def,provenance])) >>>
  HEADGOAL (
    qpat_x_assum `if is_word_type (EL i tys_tail) then _ else _` (fn values =>
      qpat_assum `~is_word_type (EL i tys_tail)` (fn ty =>
        rewrite_tac[ty] >> mp_tac (REWRITE_RULE [ty] values))) >>
    strip_tac >> conj_tac) >>>
  HEADGOAL (
    qpat_assum `lookup_var xp q = lookup_var xp m` (fn eq => pure_rewrite_tac[eq]) >>
    qpat_assum `lookup_var xp m = SOME _` (fn value =>
      qpat_assum `k + SUC i = SUC k + i` (fn eq =>
        MATCH_ACCEPT_TAC (REWRITE_RULE [eq] value)))) >>>
  HEADGOAL (
    qpat_assum `ptr_covers Gmid tmid xp m _` (fn ptr =>
      qpat_assum `lookup_var xp q = lookup_var xp m` (fn lookup =>
        qpat_assum `op_taint tq (Var xp) = op_taint tmid (Var xp)` (fn taint =>
          qpat_assum `FLOOKUP Gq xp = FLOOKUP Gmid xp` (fn provenance =>
            MATCH_ACCEPT_TAC (MATCH_MP assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame
              (LIST_CONJ [ptr,lookup,provenance,taint]))))))) >>>
  HEADGOAL (sg `alloca_frame cenv src cur u cenv mid m`) >>>
  HEADGOAL (
    match_mp_tac (Q.INST
      [`H` |-> `storage_trace_horizon src.storage_trace`,`ctx` |-> `ctx`,
       `cx` |-> `cx`,`func` |-> `func`]
      (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.alloca_frame_of_mem_frame)) >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      qpat_assum `mid.scopes = src.scopes` (fn eq => simp[NoAsms,eq])]) >>>
  HEADGOAL (sg `alloca_frame cenv es sa s0 cenv mid m`) >>>
  HEADGOAL (
    irule stmtSimDefsTheory.alloca_frame_trans >>
    qexistsl [`cenv`,`src`,`u`,`cur`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP m.vs_allocas aid = SOME b`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`i`,`entry0`] >> disch_tac >>
    qpat_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP m.vs_allocas aid = SOME b`
      (qspecl_then [`i`,`entry0`] match_mp_tac) >>
    qpat_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b`
      (qspecl_then [`i`,`entry0`] match_mp_tac) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `alloca_frame cenv es sa s0 cenv fin q`) >>>
  HEADGOAL (
    qpat_assum `!n b sz. local_region cenv fin.scopes q n b sz <=> _` (fn regions =>
      qpat_assum `q.vs_memory = m.vs_memory` (fn memory =>
        pure_rewrite_tac[stmtSimDefsTheory.alloca_frame_def,regions,memory])) >>
    qpat_assum `alloca_frame cenv es sa s0 cenv mid m`
      (ACCEPT_TAC o PURE_REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def])) >>>
  HEADGOAL (
    `sa.cs_next_id <= sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`sa.cs_next_id <= cur.cs_next_id`, `cur.cs_next_id <= target_cs.cs_next_id`,
         `target_cs.cs_next_id <= sm.cs_next_id`, `sa.cs_next_var <= cur.cs_next_var`,
         `cur.cs_next_var <= sm.cs_next_var`] >> decide_tac) >>
    `p + type_memory_size_list tvs <= q.vs_alloca_next /\
     s0.vs_alloca_next <= q.vs_alloca_next` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`q.vs_alloca_next = m.vs_alloca_next`, `u.vs_alloca_next <= m.vs_alloca_next`,
         `p + type_memory_size_list tvs <= u.vs_alloca_next`,
         `s0.vs_alloca_next <= u.vs_alloca_next`] >> decide_tac)) >>>
  HEADGOAL (
    `local_ptrs_reserved cenv sm` by
      (match_mp_tac (Q.SPECL [`cenv`,`target_cs`,`sm`] local_ptrs_reserved_next_var) >>
       conj_tac >> first_assum ACCEPT_TAC) >>
    `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x` by
      (rpt strip_tac >>
       match_mp_tac (Q.SPECL [`target_cs`,`sm`,`x`] freshWritesTheory.not_fresh_at_mono) >>
       reverse conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x`
         (qspecl_then [`x`,`cap`] match_mp_tac) >> first_assum ACCEPT_TAC) >>
    `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sm x` by
      (rpt strip_tac >>
       match_mp_tac (Q.SPECL [`target_cs`,`sm`,`x`] freshWritesTheory.not_fresh_at_mono) >>
       reverse conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at target_cs x`
         (qspecl_then [`x`,`cap`] match_mp_tac) >> first_assum ACCEPT_TAC)) >>>
  HEADGOAL (sg `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w`) >>>
  HEADGOAL (
    rpt strip_tac >>
    qpat_assum `!x w. not_fresh_at cur x /\ lookup_var x u = SOME w ==> lookup_var x q = SOME w`
      (qspecl_then [`x`,`w`] match_mp_tac) >>
    conj_tac
    >- (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cur x` match_mp_tac >>
        first_assum ACCEPT_TAC) >>
    qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w`
      (qspecl_then [`x`,`w`] match_mp_tac) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!x. not_fresh_at sa x ==>
    FLOOKUP Gq x = FLOOKUP G0 x /\ op_taint tq (Var x) = op_taint tn0 (Var x)`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cur x` (drule_then assume_tac) >>
    qpat_assum `!x. not_fresh_at cur x ==> not_fresh_at target_cs x`
      (drule_then assume_tac) >>
    qpat_assum `!x. not_fresh_at target_cs x ==> lookup_var x q = lookup_var x m /\ _`
      (qspec_then `x` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
    qpat_assum `!x. not_fresh_at cur x ==> FLOOKUP Gmid x = _ /\ _`
      (drule_then strip_assume_tac) >>
    qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gu x = _ /\ _`
      (drule_then strip_assume_tac) >>
    asm_rewrite_tac[]) >>>
  HEADGOAL (sg `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b cap. local_region cenv es.scopes s0 n b cap ==> off+sz <= b \/ b+cap <= off) /\
    off <= i /\ i < off+sz /\ i IN tq.t_mem ==> i IN tn0.t_mem`) >>>
  HEADGOAL (
    map_every qx_gen_tac [`old_id`,`old_base`,`old_size`,`byte`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    `byte IN tmid.t_mem` by (qpat_assum `tq.t_mem = tmid.t_mem` (fn eq => pure_rewrite_tac[GSYM eq]) >>
      first_assum ACCEPT_TAC)) >>>
  HEADGOAL (
    qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
      (qspecl_then [`old_id`,`old_base`,`old_size`,`byte`] match_mp_tac) >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    `FLOOKUP u.vs_allocas old_id = SOME (old_base,old_size)` by
      (qpat_assum `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry`
         match_mp_tac >> first_assum ACCEPT_TAC) >>
    `FLOOKUP m.vs_allocas old_id = SOME (old_base,old_size)` by
      (qpat_assum `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP m.vs_allocas aid = SOME entry`
         match_mp_tac >> first_assum ACCEPT_TAC) >>
    `old_id < cur.cs_next_id /\ old_id < target_cs.cs_next_id` by
      (map_every (fn pat => qpat_assum pat mp_tac)
        [`old_id < sa.cs_next_id`,`sa.cs_next_id <= cur.cs_next_id`,
         `cur.cs_next_id <= target_cs.cs_next_id`] >> decide_tac) >>
    qpat_assum `alloca_frame cenv es sa s0 cenv src u`
      (mp_tac o Q.SPECL [`old_id`,`old_base`,`old_size`] o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (assume_tac o CONJUNCT2) >>
    qpat_assum `alloca_frame cenv es sa s0 cenv mid m`
      (mp_tac o Q.SPECL [`old_id`,`old_base`,`old_size`] o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (assume_tac o CONJUNCT2)) >>>
  HEADGOAL (
    qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tu.t_mem`
      (qspecl_then [`old_id`,`old_base`,`old_size`,`byte`] match_mp_tac) >>
    rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP q.vs_allocas aid = SOME entry` by
      (qpat_assum `q.vs_allocas = m.vs_allocas` (fn eq => rewrite_tac[eq]) >>
       first_assum ACCEPT_TAC) >>
    `EVERY (assignable_type (get_tenv cx)) tys_tail` by
      (qpat_assum `EVERY (assignable_type _) (sty::_)` mp_tac >> simp[NoAsms]) >>
    `values_have_types tvs_tail vs_tail` by simp[vyperTypeDefaultsTheory.values_have_types_LIST_REL]) >>>
  HEADGOAL (
    qexistsl_tac [`Gq`,`q`,`tq`] >>
    gen_tac >> disch_tac >> conj_tac
    >- (qpat_assum `!D. gas_origin_ptr_path _ (m,Gmid,tmid) [] (OK q,Gq,tq)`
         (qspec_then `DF H` ACCEPT_TAC)) >>
    asm "suffix_ih" (qspecl_then
      [`tys_tail`,`tvs_tail`,`vs_tail`,`ops_tail`,`SUC k`,`p`,`sm`,`shadow_sm`,`fin`,`q`,`Gq`,`tq`]
      match_mp_tac) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, first_assum (ACCEPT_TAC o SYM)]) >>>

  HEADGOAL (
    mp_tac (Q.INST [`ty` |-> `sty`, `tv` |-> `stv`, `v` |-> `vi`,
      `p` |-> `place`, `es` |-> `src with gas_obs := gas_explicit target_marks u.vs_gas_readings`,
      `ee` |-> `mid`, `ff` |-> `fin`, `res` |-> `INR y : unit + exception`,
      `H` |-> `storage_trace_horizon mid.storage_trace`, `s` |-> `m`]
      (INST_TYPE [alpha |-> ``:256``] tuplePlaceWriteOutcomeTheory.tuple_place_source_write_outcome)) >>
    impl_tac) >>>
  HEADGOAL (rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    simp[NoAsms] >>
    disch_then (qx_choosel_then [`tr`,`slot`,`tv`] strip_assume_tac)) >>>
  HEADGOAL (sg `w' = slot /\ FST (SND target_r) = SOME (slot_loc tr) /\ tv = stv`) >>>
  HEADGOAL (
    qpat_assum `place = StoragePlace tr slot tv` (fn eq =>
      qpat_assum `place_ptr_rel cenv cx m (PlaceR place) w' _ (Type sty)`
        (mp_tac o REWRITE_RULE [eq,place_ptr_rel_def])) >>
    qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
      (fn eq => simp[NoAsms,eq,EQ_SYM_EQ])) >>>
  HEADGOAL (
    qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid m`
      (fn state =>
        let
          val relation = MATCH_MP stateRelProjTheory.state_rel_call_ctx_rel
            (MATCH_MP stateRelProjTheory.stmt_state_rel_state_rel state)
          val static = cj 5 (REWRITE_RULE [call_ctx_rel_def] relation)
        in
          assume_tac static
        end) >>
    sg `m.vs_call_ctx.cc_static /\ allocas_from lo m /\ lo <= m.vs_alloca_next`) >>>
  HEADGOAL (conj_tac >- asm_rewrite_tac[]) >>>
  HEADGOAL (
    qpat_assum `ghost_inv_at _ lo d cenv cx mid Gmid tmid m`
      (fn th => let val post = REWRITE_RULE [ghost_inv_at_def] th
                in ACCEPT_TAC (CONJ (cj 7 post) (cj 8 post)) end)) >>>
  HEADGOAL (`dest_loc = slot_loc tr` by simp[Abbr `dest_loc`]) >>>
  HEADGOAL (sg `0 < type_slot_size stv`) >>>
  HEADGOAL (
    match_mp_tac (Q.SPECL [`get_tenv cx`,`sty`,`stv`]
      vyperTypeSystemTheory.assignable_type_slot_size_pos) >>
    conj_tac
    >- (qpat_assum `EVERY (assignable_type (get_tenv cx)) (sty::_)` mp_tac >> simp[NoAsms]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `eval_operand (FST target_r) m = SOME slot /\ op_taint tmid (FST target_r) = {}`) >>>
  HEADGOAL (
    conj_tac >- fs[] >>
    qpat_assum `bodyFullTargetDefs$target_ptr_ok cenv (PlaceR place) target_r Gmid tmid m`
      (ACCEPT_TAC o cj 1 o REWRITE_RULE [bodyFullTargetDefsTheory.target_ptr_ok_def])) >>>
  HEADGOAL (Q.SUBGOAL_THEN `?abort_state Gabort tabort.
    !D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (m,Gmid,tmid) [] (Abort ExHalt_abort (halt_state (set_returndata [] abort_state)), Gabort, tabort)`
    (qx_choosel_then [`abort_state`,`Gabort`,`tabort`] assume_tac)) >>>
  HEADGOAL (Cases_on `is_word_type sty`) >>>
  HEADGOAL (sg `compile_store_at_loc cenv.ce_imm_alloca (FST target_r) op0
    (SOME (slot_loc tr)) target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `head_store target_cs = ((),sm)` mp_tac >>
    qpat_assum `FST (SND target_r) = SOME (slot_loc tr)` (fn loc =>
      qpat_assum `is_word_type sty` (fn word =>
        simp[NoAsms,Abbr `head_store`,loc,word]))) >>>
  HEADGOAL (sg `emit_void (if tr then TSTORE else SSTORE) [FST target_r;op0] target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `compile_store_at_loc cenv.ce_imm_alloca (FST target_r) op0
      (SOME (slot_loc tr)) target_cs = ((),sm)` mp_tac >>
    Cases_on `tr` >> simp[NoAsms,slot_loc_def,compile_store_at_loc_def]) >>>
  HEADGOAL (sg `eval_operand op0 m = SOME (typed_val_to_w256 stv vi) /\ op_taint tmid op0 = {}`) >>>
  HEADGOAL (
    qpat_assum `if is_word_type sty then _ else _` mp_tac >>
    qpat_assum `op0 = Var xs` (fn operand =>
      qpat_assum `is_word_type sty` (fn word =>
        simp[NoAsms,operand,word,eval_operand_def])) >> simp[]) >>>
  HEADGOAL (
    qexistsl_tac [`m`,`Gmid`,`tmid`] >> gen_tac >>
    match_mp_tac (Q.INST [
      `dst` |-> `FST (target_r : operand # data_location option # place_ty option)`,
      `value` |-> `op0`, `addr` |-> `slot : 256 word`, `w` |-> `typed_val_to_w256 stv vi`,
      `sa` |-> `target_cs`, `sb` |-> `sm`, `tr` |-> `tr`]
      augAssignFullStoreTheory.storage_emit_static_origin_ptr) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    sg `compile_assign_value cenv (FST target_r) (slot_loc tr) op0 F
      NONE sty sty (type_memory_bytes cenv sty) target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `head_store target_cs = ((),sm)` mp_tac >>
    qpat_assum `dest_loc = slot_loc tr` (fn loc =>
      qpat_assum `~is_word_type sty` (fn word =>
        simp[NoAsms,Abbr `head_store`,loc,word]))) >>>
  HEADGOAL (
    sg `compile_store_slots cenv op0 (FST target_r) sty tr target_cs = ((),sm)`) >>>
  HEADGOAL (
    qpat_assum `compile_assign_value cenv (FST target_r) (slot_loc tr) op0 F
      NONE sty sty (type_memory_bytes cenv sty) target_cs = ((),sm)` mp_tac >>
    Cases_on `tr` >>
    simp[NoAsms,slot_loc_def,compile_assign_value_def,comp_bind_def,comp_return_def]) >>>
  HEADGOAL (
    `LENGTH vs = LENGTH tvs` by
      (irule vyperTypingTheory.values_have_types_length >> simp[]) >>
    `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
             tuple_in_memory vs tvs p mem` by
      (qpat_assum `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
                         val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [Once valueEncodingDefsTheory.val_in_memory_def])) >>
    `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
             val_in_memory stv vi (p + SUM (MAP type_memory_size (TAKE k tvs))) mem` by
      (qspecl_then [`vs`,`tvs`,`p`,`m.vs_memory`,`tmid`,`k`] mp_tac
         typedCopyLayoutPtrTheory.tuple_in_memory_robust_element >> simp[])) >>>
  HEADGOAL (
    `SUM (MAP type_memory_size (TAKE k tvs)) + type_memory_size stv <=
     type_memory_size_list tvs` by
      (drule tupleMemoryLayoutTheory.tuple_element_interval >>
       simp[valueEncodingProofsTheory.type_memory_size_list_sum])) >>>
  HEADGOAL (
    `m.vs_alloca_next < dimword (:256)` by
      (qpat_assum `stmt_state_rel _ _ _ _ _ mid m`
         (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room) >>
       disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
    qabbrev_tac `addr = p + SUM (MAP type_memory_size (TAKE k tvs))` >>
    `addr + type_memory_size stv <= m.vs_alloca_next` by
      (qpat_assum `p + type_memory_size_list tvs <= u.vs_alloca_next` mp_tac >>
       qpat_assum `u.vs_alloca_next <= m.vs_alloca_next` mp_tac >>
       qpat_assum `SUM (MAP type_memory_size (TAKE k tvs)) + _ <= _` mp_tac >>
       simp[NoAsms,Abbr `addr`] >> decide_tac) >>
    `addr < dimword (:256)` by
      (qpat_assum `addr + _ <= m.vs_alloca_next` mp_tac >>
       qpat_assum `m.vs_alloca_next < dimword (:256)` mp_tac >> decide_tac) >>
    `w2n (n2w addr : 256 word) = addr` by
      simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD]) >>>
  HEADGOAL (
    qpat_assum `body_inv tops ctx cenv cx`
      (mp_then Any mp_tac immutableDeployAssignRangesTheory.immutable_assign_copy_metadata) >>
    qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
      disch_then (strip_assume_tac o (fn rule => MATCH_MP rule inv)))) >>>
  HEADGOAL (
    qpat_assum `if is_word_type sty then _ else _` (fn cases =>
      qpat_assum `~is_word_type sty` (fn word =>
        strip_assume_tac (REWRITE_RULE [word] cases)))) >>>
  HEADGOAL (
    sg `eval_operand op0 m = SOME (n2w addr) /\ op_taint tmid op0 = {} /\
        ptr_covers Gmid tmid xs m (type_memory_size stv)`) >>>
  HEADGOAL (
    qpat_assum `op0 = Var xs` (fn op_eq => rewrite_tac[op_eq,eval_operand_def]) >>
    conj_tac >- (simp[NoAsms,Abbr `addr`] >> first_assum ACCEPT_TAC) >>
    conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!x. op0 = Var x \/ FST target_r = Var x ==> not_fresh_at target_cs x`) >>>
  HEADGOAL (
    gen_tac >> disch_then DISJ_CASES_TAC
    >- (qpat_assum `op0 = Var xs` (fn eq => fs[eq])) >>
    qpat_assum `!x. FST target_r = Var x ==> not_fresh_at target_cs x` irule >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H mid.storage_trace ==>
    storage_place_observed H (StoragePlace tr slot stv) /\ regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H)`) >>>
  HEADGOAL (
    gen_tac >> disch_tac >>
    qpat_assum `eval_base_place cx bt _ = (INL (PlaceR place),mid)` (fn reached =>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace` (fn horizon =>
        qpat_assum `place = StoragePlace tr slot tv` (fn place_eq =>
          qpat_assum `tv = stv` (fn ty =>
            ACCEPT_TAC (REWRITE_RULE [place_eq,ty]
              (MATCH_MP tuplePlacePointerReadyTheory.tuple_place_pointer_storage_facts
                (CONJ reached horizon)))))))) >>>
  HEADGOAL (sg `!H. valid_horizon cx st0 H mid.storage_trace ==> 0 < type_slot_size stv ==>
    ?rootk root path delta. MEM (tr,rootk,root) (FST H) /\
      storage_subregion root path delta stv /\ w2n slot = w2n rootk + delta`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==>
      storage_place_observed K (StoragePlace tr slot stv) /\ _`
      (drule_then strip_assume_tac) >>
    disch_tac >>
    qpat_assum `storage_place_observed H (StoragePlace tr slot stv)` (fn observed =>
      qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
        qpat_assum `regions_consistent (FST H)` (fn regions =>
          qpat_assum `0 < type_slot_size stv` (fn size =>
            ACCEPT_TAC (MATCH_MP tuplePlaceValueStorageFrameTheory.tuple_place_storage_leaf_horizon
              (LIST_CONJ [observed,inv,regions,size]))))))) >>>
  HEADGOAL (sg `w2n slot + type_slot_size stv <= dimword (:256)`) >>>
  HEADGOAL (
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> 0 < type_slot_size stv ==>
      ?rootk root path delta. _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (qx_choosel_then [`rk`,`root_ty`,`piece`,`delta`] strip_assume_tac)) >>>
  HEADGOAL (
    qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
      storage_place_observed H (StoragePlace tr slot stv) /\ _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>>
  HEADGOAL (
    qpat_assum `expr_sim_inv cenv cx env mid` (fn inv =>
      qpat_assum `MEM (tr,rk,root_ty) (FST (storage_trace_horizon mid.storage_trace))` (fn root =>
        qpat_assum `regions_consistent (FST (storage_trace_horizon mid.storage_trace))` (fn consistent =>
          qpat_assum `storage_subregion root_ty piece delta stv` (fn region =>
            qpat_assum `0 < type_slot_size stv` (fn size =>
              mp_tac (MATCH_MP placeStoreStorageTheory.place_store_storage_leaf_bounds
                (LIST_CONJ [inv,root,consistent,region,size]))))))) >>
    qpat_assum `w2n slot = w2n rk + delta` (fn eq => simp[NoAsms,eq])) >>>
  HEADGOAL (sg `eval_operand (FST target_r) m = SOME slot`) >>>
  HEADGOAL (fs[]) >>>
  HEADGOAL (sg `type_memory_size stv <> 0 ==>
    ?x. op0 = Var x /\ ptr_covers Gmid tmid x m (type_memory_size stv)`) >>>
  HEADGOAL (disch_tac >> qexists_tac `xs` >> conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (Q.SUBGOAL_THEN
    `type_memory_size stv = 0 \/ w2n (n2w addr:256 word) + type_memory_size stv <= m.vs_alloca_next`
    ASSUME_TAC) >>>
  HEADGOAL (
    disj2_tac >>
    qpat_assum `w2n (n2w addr:256 word) = addr` (fn eq => pure_rewrite_tac[eq]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `w2n (n2w addr:256 word) + type_memory_size stv < dimword (:256)`) >>>
  HEADGOAL (
    qpat_assum `w2n (n2w addr:256 word) = addr` (fn eq => pure_rewrite_tac[eq]) >>
    map_every (fn pat => qpat_assum pat mp_tac)
      [`addr + type_memory_size stv <= m.vs_alloca_next`, `m.vs_alloca_next < dimword (:256)`] >>
    decide_tac) >>>
  HEADGOAL (sg `!mem. mem_agree_outside tmid.t_mem m.vs_memory mem ==>
    val_in_memory stv vi (w2n (n2w addr:256 word)) mem`) >>>
  HEADGOAL (
    qpat_assum `w2n (n2w addr:256 word) = addr` (fn eq => pure_rewrite_tac[eq]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `value_has_type stv vi`
      (qx_choose_then `writes` assume_tac o
       REWRITE_RULE [optionTheory.IS_SOME_EXISTS] o
       MATCH_MP (cj 1 vyperTypingTheory.value_has_type_equiv))) >>>
  HEADGOAL (
    mp_tac (Q.SPECL [`cenv`,`get_tenv cx`,`sty`,`stv`,`vi`,`op0`,
      `FST (target_r : operand # data_location option # place_ty option)`,`tr`,
      `target_cs`,`sm`,`m`,`n2w addr : 256 word`,`slot : 256 word`,
      `tmid`,`Gmid`,`writes`,`func`,`ctx`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`PG`]
      bodyFullStoreSlotsStaticTheory.compile_store_slots_static_origin_ptr_path) >>
    impl_tac) >>>
  HEADGOAL (rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    disch_then (qx_choosel_then [`q`,`Gq`,`tq`] (map_every assume_tac o CONJUNCTS)) >>
    qexistsl_tac [`q`,`Gq`,`tq`] >> qx_gen_tac `D` >>
    `type_slot_size stv <> 0` by
      (qpat_assum `0 < type_slot_size stv` mp_tac >> decide_tac) >>
    qpat_assum `type_slot_size stv <> 0` (fn size =>
      qpat_assum `!D. gas_origin_ptr_path _ (m,Gmid,tmid) [] ((if _ then _ else _),Gq,tq)`
        (qspec_then `D` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [size])))) >>>
  HEADGOAL (
    irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >> BETA_TAC >>
    reverse conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`Gabort`,`fin`,`Abort ExHalt_abort (halt_state (set_returndata [] abort_state))`,
      `INR y`,`tabort`]) >>>
  HEADGOAL (conj_tac >- first_assum ACCEPT_TAC) >>>
  HEADGOAL (simp[NoAsms,exit_result_def]) >>>
  HEADGOAL (gen_tac >> disch_tac >> conj_tac) >>>
  HEADGOAL (
    qpat_assum `!D. gas_origin_ptr_path _ (m,Gmid,tmid) [] (Abort _ _,Gabort,tabort)`
      (qspec_then `DF H` ACCEPT_TAC)) >>>
  HEADGOAL (
    simp[Abbr `suffixR`,stmt_exit_ptr_def,halt_exit_def,expr_exit_def]) >>>
  HEADGOAL (
    `LENGTH gs = LENGTH tys` by metis_tac[LIST_REL_LENGTH] >>
    `env.type_defs = get_tenv cx` by
      (irule exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >>
       qexistsl_tac [`cenv`,`es`] >> simp[]) >>
    `EVERY (assignable_type (get_tenv cx)) tys` by
      (qpat_assum `env.type_defs = get_tenv cx` (fn types =>
       qpat_assum `assignable_type env.type_defs (TupleT tys)`
         (ACCEPT_TAC o cj 3 o PURE_REWRITE_RULE [types,Once assignable_type_def])))) >>>
  HEADGOAL (
  `!ats g. alloc_limits_assignments cenv ats /\ MEM g ats ==>
      alloc_limits_assignment cenv g` by
    (Induct >> simp[NoAsms,allocLimitsTheory.alloc_limits_assignment_def] >> metis_tac[]) ) >>>
  HEADGOAL (
  `!ats g. call_evaluation_safe cx (int_calls_atargets ats) /\ MEM g ats ==>
      call_evaluation_safe cx (int_calls_atarget g)` by
    (Induct >> simp[NoAsms,int_calls_atarget_def] >>
     metis_tac[call_evaluation_safe_append_left,call_evaluation_safe_append_right]) ) >>>
  HEADGOAL (
    sg `!i. i < LENGTH gs ==> ?head.
      EL i gs = BaseTarget head /\ supported_target tops bindings head /\
      well_typed_target env head (EL i tys) /\
      call_evaluation_safe cx (int_calls_target head) /\
      target_indices_pre cenv cx env head`) >>>
  HEADGOAL (qx_gen_tac `i` >> strip_tac >>
     `MEM (EL i gs) gs` by simp[listTheory.EL_MEM] >>
     `?head. EL i gs = BaseTarget head /\ supported_target tops bindings head` by
       (qpat_assum `EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt | TupleTarget ts => F) gs`
          (qspec_then `EL i gs` mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
        BETA_TAC >> impl_tac >- first_assum ACCEPT_TAC >>
        Cases_on `EL i gs` >> simp[])) >>>
  HEADGOAL (
     `type_place_target env head = SOME (Type (EL i tys))` by
       (qpat_assum `LIST_REL (\g ty. well_typed_atarget env g ty) _ _`
         (mp_tac o REWRITE_RULE [listTheory.LIST_REL_EL_EQN]) >>
        strip_tac >> first_x_assum (qspec_then `i` mp_tac) >>
        simp[tuple_target_base_type]) ) >>>
  HEADGOAL (

     `MEM (BaseTarget head) gs` by metis_tac[] >>
     `call_evaluation_safe cx (int_calls_target head)` by
       (`call_evaluation_safe cx (int_calls_atargets gs)` by
          (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
           simp[NoAsms,int_calls_stmt_def,int_calls_atarget_def] >>
           metis_tac[call_evaluation_safe_append_left]) >>
        qpat_assum `!ats g. call_evaluation_safe _ _ /\ MEM _ _ ==> _`
          (qspecl_then [`gs`,`BaseTarget head`] mp_tac) >>
        simp[int_calls_atarget_def]) ) >>>
  HEADGOAL (
     `!ats p g. MEM g ats /\ supported_assignment_exists p g ==>
       supported_assignments_exists p ats` by
       (POP_ASSUM_LIST (K all_tac) >> Induct >>
        simp[NoAsms,supported_assignment_exists_def] >> metis_tac[])) >>>
  HEADGOAL (
     `!p. supported_target_exists p head ==>
       supported_stmt_expr_exists p (Assign (TupleTarget gs) e)` by
       (gen_tac >> strip_tac >>
        simp[NoAsms,supported_stmt_expr_exists_def,supported_assignment_exists_def] >>
        disj1_tac >>
        qpat_assum `!ats p g. MEM g ats /\ supported_assignment_exists p g ==> _`
          (qspecl_then [`gs`,`p`,`BaseTarget head`] match_mp_tac) >>
        simp[supported_assignment_exists_def])) >>>
  HEADGOAL (

     `alloc_limits_target cenv head` by
       (`alloc_limits_assignments cenv gs` by
          fs[stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,
             allocLimitsTheory.alloc_limits_assignment_def] >>
        qpat_assum `!ats g. alloc_limits_assignments _ _ /\ MEM _ _ ==> _`
          (qspecl_then [`gs`,`BaseTarget head`] mp_tac) >>
        simp[allocLimitsTheory.alloc_limits_assignment_def]) ) >>>
  HEADGOAL (

     qexists_tac `head` >> asm_simp_tac bool_ss [well_typed_target_def] >>
     `supported_program tops /\ get_module_code cx NONE = SOME tops /\
       (!a. is_dynamic (vyper_to_abi_type (get_tenv cx) a) ==>
            is_dynamic (vyper_to_abi_type (type_env tops) a))` by fs[body_inv_def] >>
     `cx_tops cx = tops` by metis_tac[cx_tops_module] ) >>>
  HEADGOAL (
     `~supported_target_exists (const_name_root cx) head` by
       (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
        qpat_assum `supported_stmt tops bindings (Assign (TupleTarget gs) e)`
          (fn supported =>
           assume_tac (MATCH_MP
             (MATCH_MP (cj 1 supported_stmts_no_name_root) supported)
             (MATCH_MP body_inv_const_name_root inv)))) >>
        qpat_assum `!p. supported_target_exists p head ==> _`
          (qspec_then `const_name_root cx` mp_tac) >>
        simp[])) >>>
  HEADGOAL (
     `~supported_target_exists (\x. ~is_extcode x /\ ~byte_widths_expr x) head` by
       (qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o REWRITE_RULE [stmt_exprs_ok_def]) >>
        metis_tac[]) >>
     drule_then strip_assume_tac bodyStorageCasesTheory.supported_target_storage_syntax >>
     irule popTargetPreTheory.target_indices_pre_of_body >>
     simp[]) >>>
  HEADGOAL (
     `~supported_target_exists is_extcode head` by
       metis_tac[ctorDeployLoweringFrameSupportTheory.deploy_frame_supported_target_no_extcode] >>
     qpat_assum `supported_target tops bindings head` mp_tac >>
     qpat_assum `~supported_target_exists (\x. ~is_extcode x /\ _) head` mp_tac >>
     qpat_assum `~supported_target_exists is_extcode head` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `head` >> gvs[byte_widths_expr_def,supported_target_def,
       supportedExprTraverseTheory.supported_expr_exists_def,AllCaseEqs()] >>
     rpt strip_tac
     >~ [`byte_widths_expr x`]
     >- (rename1 `byte_widths_expr x` >>
         `~is_extcode x` by metis_tac[supportedExprTraverseTheory.supported_expr_exists_root] >>
         spose_not_then assume_tac >>
         qpat_x_assum `~supported_expr_exists (\y. ~is_extcode y /\ _) x`
           (irule o NOT_ELIM) >>
         irule supportedExprTraverseTheory.supported_expr_exists_root >> simp[]) >>
     rename1 `byte_widths_target b` >> Cases_on `b` >> gvs[byte_widths_expr_def]) >>>
  HEADGOAL (
    `EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt /\
            target_indices_pre cenv cx env bt | TupleTarget ts => F) gs` by
      (rewrite_tac[EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
       qpat_assum `!i. i < LENGTH gs ==> ?head. _`
         (qspec_then `i` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
       disch_then (qx_choose_then `head` strip_assume_tac) >> simp[])) >>>
  HEADGOAL (
    `call_evaluation_safe cx (int_calls_atargets gs)` by
      (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
       simp[NoAsms,int_calls_stmt_def,int_calls_atarget_def] >>
       metis_tac[call_evaluation_safe_append_left]) >>
    `expr_sim_inv cenv cx env (ee with gas_obs := [])` by
      simp[exprSimHypsDefsTheory.expr_sim_inv_gas_obs]) >>>
  HEADGOAL (
    `?tv er. eval_expr cx e (es with gas_obs := obs) = (INL tv,er) /\
       read_result cx tv er = (INL (ArrayV (TupleV vs)),ee with gas_obs := [])` by
      (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL (ArrayV (TupleV vs)),_)`
         (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split) >> simp[]) >>
    `body_tuple_targets_full_ok cx gs vs` by
      (qpat_assum `!s tv t s' v t'. _ ==> body_tuple_target_full_ok _ _ _`
         (qspecl_then [`es with gas_obs := obs`,`tv`,`er`,`er`,`ArrayV (TupleV vs)`,
             `ee with gas_obs := []`] mp_tac) >> simp[body_tuple_target_full_ok_def])) >>>
  HEADGOAL (
    `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) =
       assign_tuple_target_list cx gs vs` by simp[Once evaluate_def] >>
    `gas_admissible (assign_tuple_target_list cx gs vs) (stmt_res_ok lctx)
       (ee with gas_obs := [])` by
      (qpat_assum `gas_admissible (eval_stmt cx (Assign (TupleTarget gs) e)) _ es`
        (fn adm => qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
         (fn step => mp_tac (MATCH_MP stmtSimForRoundsTheory.gas_admissible_bind_tail
            (CONJ (REWRITE_RULE [stmtSimAssignTupleTheory.eval_assign_tuple_action] adm) step))))
       >> simp[])) >>>
  HEADGOAL (
    Cases_on `is_memory_view e /\ vv_location vv = SOME LocMemory /\
      EXISTS (\t. ~is_word_type t) tys /\
      0 < SUM (MAP (type_memory_bytes cenv) tys)`) >>>
  HEADGOAL (
    qpat_assum `ptr_val_ok _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def,is_word_type_def]) >>
    qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
      (mp_tac o Q.SPECL [`TupleTV tvs`,`w`] o REWRITE_RULE [ptr_mem_ok_def]) >>
    simp[is_word_type_def,val_footprint_def,valueEncodingTheory.type_memory_size_def] >> strip_tac >>
    qpat_assum `expr_store_bound _ _ _ _ _`
      (mp_tac o Q.SPECL [`TupleTV tvs`,`w`] o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
    simp[is_word_type_def,val_store_size_def,valueEncodingTheory.type_memory_size_def] >> strip_tac >>
    qpat_assum `op = Var x` SUBST_ALL_TAC) >>>
  HEADGOAL (
    `lookup_var x v = SOME w` by
      (qpat_assum `eval_operand (Var x) v = SOME w`
         (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])) >>
    `ptr_covers G' tn' x v (type_memory_size_list tvs)` by
      (rewrite_tac[ptr_covers_def] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl_tac [`w`,`b`,`sz`] >> rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC,
         qpat_assum `w2n w + val_store_size (TupleTV tvs) _ <= b + sz` mp_tac >>
         simp[NoAsms,val_store_size_def,valueEncodingTheory.type_memory_size_def,ADD_COMM]]) >>
    `v.vs_alloca_next < dimword (:256)` by
      (qpat_assum `stmt_state_rel _ _ _ _ _ _ v`
         (ACCEPT_TAC o MATCH_MP alloca_room_next_lt o
          MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room))) >>>
  HEADGOAL (
    `w2n w + type_memory_size_list tvs < dimword (:256) /\
     type_memory_size_list tvs < dimword (:256)` by
      (qpat_assum `type_memory_size_list tvs + w2n w <= v.vs_alloca_next` mp_tac >>
       qpat_assum `v.vs_alloca_next < dimword (:256)` mp_tac >> decide_tac)) >>>
  HEADGOAL (
    `allocas_from lo v /\ lo <= v.vs_alloca_next` by
      (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ v`
         (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
    `local_ptrs_reserved cenv su` by
      (match_mp_tac (Q.SPECL [`cenv`,`sa`,`su`] local_ptrs_reserved_next_var) >>
       conj_tac >> first_assum ACCEPT_TAC) >>
    `not_fresh_at su x` by
      (qpat_assum `lower_value compile_expr cenv (TupleT tys) e sa = (Var x,su)` (fn code =>
         qpat_assum `local_ptrs_reserved cenv sa` (fn reserved =>
           qspec_then `x` mp_tac
             (MATCH_MP exprOperandVarTheory.compile_lower_value_var (CONJ code reserved)))) >>
       simp[NoAsms])) >>>
  HEADGOAL (
    `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by
      (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[]) >>
    `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x` by
      (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[])) >>>
  HEADGOAL (
    `~v.vs_halted` by
      (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK v,G',tn')`
         (ACCEPT_TAC o MATCH_MP fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted o
          CONJUNCT2 o MATCH_MP gas_origin_ptr_path_projections)) >>
    qpat_x_assum `(if _ then _ else _) su = (staged,sl)` mp_tac >>
    simp[comp_bind_def,comp_return_def] >>
    Cases_on `compile_alloc_buffer (type_memory_size_list tvs) su` >>
    rename1 `compile_alloc_buffer _ su = (stage_buf,stage_mid)` >>
    Cases_on `emit_void MCOPY [stage_buf.buf_operand; Var x;
      Lit (n2w (type_memory_size_list tvs))] stage_mid` >>
    simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >> strip_tac) >>>
  HEADGOAL (Cases_on `q` >> gvs[] >>
    rename1 `compile_tuple_load_all _ _ _ _ sl = _` >>
    `0 < type_memory_size_list tvs` by metis_tac[]) >>>
  HEADGOAL (
    `compile_copy_memory stage_buf.buf_operand (Var x) (type_memory_size_list tvs)
       stage_mid = ((),sl)` by
      (Cases_on `type_memory_size_list tvs` >> gvs[compile_copy_memory_def]) >>
    `cs_extends su stage_mid /\ cs_extends stage_mid sl` by
      metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,ci_mono_def,pairTheory.SND] >>
    `fn_has_code su stage_mid func /\ fn_has_code stage_mid sl func` by
      metis_tac[fn_has_code_split]) >>>
  HEADGOAL (
    `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (ee with gas_obs := []) v` by
      simp[exprLoweringPropsTheory.stmt_state_rel_start_gas_obs] >>
    drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)
      (INST_TYPE [beta |-> ``:256``] bodyFullMemoryStageTheory.body_full_memory_stage_frame_path) >>
    disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
    disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
    disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
    disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
    disch_then (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
    disch_then (drule_at (Pat `lookup_var _ _ = SOME _`))) >>>
  HEADGOAL (disch_then (qspec_then `lo` mp_tac) >>
    disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
    disch_then (qspec_then `PG` mp_tac)) >>>
  HEADGOAL ((impl_tac >- simp[is_word_type_def,valueEncodingTheory.type_memory_size_def]) >>
    strip_tac) >>>
  HEADGOAL (
    `local_ptrs_reserved cenv sl` by metis_tac[local_ptrs_reserved_next_var] >>
    `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x` by
      metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x` by
      metis_tac[freshWritesTheory.not_fresh_at_mono] >>
    qpat_assum `stage_buf.buf_operand = Var root` SUBST_ALL_TAC >>
    drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)
      (INST_TYPE [alpha |-> ``:256``] body_assign_tuple_load_all_path)) >>>
  HEADGOAL (disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`))) >>>
  HEADGOAL (disch_then (drule_at (Pat `lookup_var _ _ = _`))) >>>
  HEADGOAL (disch_then (drule_at (Pat `values_have_types _ _`))) >>>
  HEADGOAL (disch_then (qspec_then `lo` mp_tac) >>
    disch_then (qspec_then `func` mp_tac) >>
    disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
    disch_then (qspec_then `ee with gas_obs := []` mp_tac) >>
    disch_then (qspec_then `cx` mp_tac) >>
    disch_then (qspec_then `ctx` mp_tac) >>
    disch_then (qspec_then `PG` mp_tac)) >>>
  HEADGOAL (
    `b' < dimword (:256)` by decide_tac >>
    (impl_tac >- (simp[wordsTheory.w2n_n2w] >>
      metis_tac[valueEncodingPropsTheory.val_in_memory_tuple])) >> strip_tac) >>>
  HEADGOAL (
    `w2n (n2w b' :256 word) = b'` by
      simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
    `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (v,G',tn') [] (OK t',Gf',tf')` by
      (gen_tac >>
       qpat_assum `!D. gas_origin_ptr_path _ (v,G',tn') [] (OK t,Gf,tf)`
         (qspec_then `D` assume_tac) >>
       qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tf) [] (OK t',Gf',tf')`
         (qspec_then `D` (fn load =>
            qpat_assum `gas_origin_ptr_path _ (v,G',tn') [] (OK t,Gf,tf)`
              (fn stage => ACCEPT_TAC
                (MATCH_MP fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans
                  (CONJ stage load))))))) >>>
  HEADGOAL (
    `!n a cap. local_region cenv (ee with gas_obs := []).scopes t' n a cap <=>
      local_region cenv (ee with gas_obs := []).scopes t n a cap` by
      (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
       qexists_tac `sl` >> simp[]) >>
    `!mem. mem_agree_outside tf'.t_mem t'.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b' mem` by
      (qpat_assum `!mem. _ ==> tuple_in_memory vs tvs (w2n (n2w b') + 0) mem` mp_tac >>
       simp[Once valueEncodingDefsTheory.val_in_memory_def]) >>
    `b' + type_memory_size_list tvs <= t'.vs_alloca_next` by simp[]) >>>
  HEADGOAL (
    `stage_mid.cs_next_id = su.cs_next_id + 1` by
      (qpat_assum `compile_alloc_buffer _ su = (_,stage_mid)`
         (ACCEPT_TAC o cj 3 o MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts)) >>
    `ci_mono stage_mid sl` by
      (qpat_assum `compile_copy_memory _ _ _ stage_mid = ((),sl)` (fn code =>
         ACCEPT_TAC (REWRITE_RULE [code,pairTheory.SND]
           (SPECL (snd (strip_comb (lhs (concl code)))) ci_mono_compile_copy_memory)))) >>
    `ci_mono sl ss` by
      (qpat_assum `compile_tuple_load_all _ _ _ _ sl = (elems,ss)` (fn code =>
         ACCEPT_TAC (REWRITE_RULE [code,pairTheory.SND] (Q.SPECL [`cenv`,`Var root`,
           `tys`,`0`,`sl`] (cj 4 stmtLoweringMonoTheory.ci_mono_list_helpers))))) >>
    `su.cs_next_id < ss.cs_next_id` by
      (qpat_assum `ci_mono stage_mid sl` mp_tac >>
       qpat_assum `ci_mono sl ss` mp_tac >> simp[NoAsms,ci_mono_def] >>
       qpat_assum `stage_mid.cs_next_id = su.cs_next_id + 1` mp_tac >> decide_tac)) >>>
  HEADGOAL (
    `sa.cs_next_id <= su.cs_next_id` by
      (qpat_assum `lower_value compile_expr _ _ e sa = (_,su)`
        (ACCEPT_TAC o cj 3 o MATCH_MP (cj 2 compile_expr_grows))) >>
    `sa.cs_next_id <= ss.cs_next_id` by decide_tac >>
    `!x. not_fresh_at sa x ==> not_fresh_at su x /\ not_fresh_at sl x` by
      (gen_tac >> disch_tac >> conj_tac >>
       irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
       simp[] >> decide_tac)) >>>
  HEADGOAL (
    `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at ss x` by
      (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
    `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at ss x` by
      (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
    `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w` by
      (rpt strip_tac >> simp[]) >>
    `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t'.vs_allocas aid = SOME ent` by
      (rpt strip_tac >> simp[])) >>>
  HEADGOAL (
    qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'`
      (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
    `!x. not_fresh_at sa x ==> FLOOKUP Gf' x = FLOOKUP G0 x /\
                                op_taint tf' (Var x) = op_taint tn0 (Var x)` by
      (rpt strip_tac >> simp[])) >>>
  HEADGOAL (
    `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (ee with gas_obs := []) t` by
      (qpat_assum `!H. stmt_state_rel H ctx func cenv cx _ v ==> stmt_state_rel H _ _ _ _ _ t`
         (qspec_then `storage_trace_horizon ee.storage_trace` MATCH_MP_TAC) >>
       first_assum ACCEPT_TAC) >>
    `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (ee with gas_obs := []) t'` by
      (qpat_assum `!H. stmt_state_rel H ctx func cenv cx _ t ==> stmt_state_rel H _ _ _ _ _ t'`
         (qspec_then `storage_trace_horizon ee.storage_trace` MATCH_MP_TAC) >>
       first_assum ACCEPT_TAC) >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx _ t'`
        (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)))) >>>
  HEADGOAL (
    `alloca_inv v` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx ee v`
         (ACCEPT_TAC o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv)) >>
    `gas_marked_path T ctx func v 0 (OK t')` by
      (qpat_assum `!D. gas_origin_ptr_path _ (v,G',tn') [] (OK t',Gf',tf')`
         (qspec_then `DF (storage_trace_horizon ee.storage_trace)`
            (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
             CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections)) >> simp[]) >>
    `alloca_history func t' /\ v.vs_alloca_next <= t'.vs_alloca_next` by
      (drule_all bodyMemBopRestWordPathTheory.rest_word_marked_allocation_posts >> simp[]) >>
    `s0.vs_alloca_next <= t'.vs_alloca_next` by decide_tac) >>>
  HEADGOAL (
    `return_buf_frame d cenv ss t'` by
      (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
       qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >> decide_tac)) >>>
  HEADGOAL (
    `!fn inst z. frag_reachable ctx func t' fn inst z ==> dalloca_no_wrap inst z` by
      (qpat_assum `body_inv tops ctx cenv cx`
        (mp_then Any mp_tac bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap) >>
       disch_then (qspecl_then [`func`,`t'`] assume_tac) >> rpt strip_tac >>
       rename1 `frag_reachable ctx func t' rf ri rz` >>
       qpat_assum `!fn inst u. MEM func ctx.ctx_functions /\ frag_reachable ctx func t' fn inst u ==> _`
         (qspecl_then [`rf`,`ri`,`rz`] mp_tac) >>
       impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC)) >>>
  HEADGOAL (
    `~block_is_terminated stage_mid` by
      (qpat_assum `compile_alloc_buffer _ su = (_,stage_mid)`
         (ACCEPT_TAC o MATCH_MP (SPEC_ALL exprOpenPrimitivesTheory.compile_alloc_buffer_open))) >>
    `~block_is_terminated sl` by
      (irule exprOpenCopiesTheory.compile_copy_memory_open >>
       qpat_assum `compile_copy_memory _ _ _ stage_mid = ((),sl)` (irule_at Any) >> simp[]) >>
    `gas_marked_path F ctx func t 0 (OK t')` by
      (qpat_assum `!D. gas_origin_ptr_path _ (t,Gf,tf) [] (OK t',Gf',tf')`
         (qspec_then `DF (storage_trace_horizon ee.storage_trace)`
           (mp_tac o MATCH_MP fragGasModeTheory.gas_marked_path_exec o
            MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
            CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections)) >>
       simp[fragGasModeTheory.gas_marked_path_def]) >>
    `~block_is_terminated ss` by
      (irule assignPlaceEndpointTheory.endpoint_path_open >>
       qpat_assum `gas_marked_path F ctx func t 0 (OK t')` (irule_at Any) >>
       qpat_assum `cs_extends sl ss` (irule_at Any) >> simp[])) >>>
  HEADGOAL (
    `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
      (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
       simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
            vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
    `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
      (gen_tac >> disch_tac >>
       `valid_horizon cx st0 H (es with gas_obs := obs).storage_trace` suffices_by simp[] >>
       irule (INST_TYPE [alpha |-> ``:value``] vyperStorageFootprintTheory.valid_horizon_frame) >>
       qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`,
         `INL (ArrayV (TupleV vs))`, `ee with gas_obs := []`] >> simp[])) >>>
  HEADGOAL (
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by simp[] >>
    qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>>
  HEADGOAL (
    `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by simp[]) >>>
  HEADGOAL (
    `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) v` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx es s0` (fn rel =>
       qpat_assum `local_ptrs_reserved cenv sa` (fn reserved =>
       qpat_assum `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` (fn scopes =>
       qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x v = SOME w` (fn regs =>
       qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz v.vs_memory = _` (fn mem =>
         ACCEPT_TAC (MATCH_MP stmtSimDefsTheory.alloca_frame_of_mem_frame
            (LIST_CONJ [rel,reserved,scopes,regs,mem]))))))))) >>>
  HEADGOAL (
    `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) t` by
      (irule stmtSimDefsTheory.alloca_frame_trans >>
       qexistsl_tac [`cenv`,`ee with gas_obs := []`,`v`,`su`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    sg `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) t'`) >>>
  HEADGOAL (rewrite_tac[alloca_frame_def] >>
    map_every qx_gen_tac [`old_id`,`old_off`,`old_size`] >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    qpat_assum `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) t`
      (qspecl_then [`old_id`,`old_off`,`old_size`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (fn frame =>
      qpat_assum `t'.vs_memory = t.vs_memory` (fn mem =>
        qpat_assum `!n a cap. local_region cenv _ t' n a cap <=> local_region cenv _ t n a cap`
          (fn regs => ACCEPT_TAC (PURE_REWRITE_RULE [GSYM mem, GSYM regs] frame))))) >>>
  HEADGOAL (
    sg `!old_id old_off old_size i. FLOOKUP s0.vs_allocas old_id = SOME (old_off,old_size) /\ old_id < sa.cs_next_id /\
       (!n b len. local_region cenv es.scopes s0 n b len ==> old_off+old_size <= b \/ b+len <= old_off) /\
       old_off <= i /\ i < old_off+old_size /\ i IN tf'.t_mem ==> i IN tn0.t_mem`) >>>
  HEADGOAL (map_every qx_gen_tac [`old_id`,`old_off`,`old_size`,`i`] >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
       `!n b len. local_region cenv (ee with gas_obs := []).scopes v n b len ==>
         old_off+old_size <= b \/ b+len <= old_off` by
         (qpat_assum `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) v`
            (qspecl_then [`old_id`,`old_off`,`old_size`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then (ACCEPT_TAC o CONJUNCT2))) >>>
  HEADGOAL (
       `FLOOKUP v.vs_allocas old_id = SOME (old_off,old_size)` by simp[] >>
       `old_id < su.cs_next_id` by decide_tac >>
       `i IN tf.t_mem` by
         (qpat_assum `tf'.t_mem = tf.t_mem` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
          first_assum ACCEPT_TAC)) >>>
  HEADGOAL (
       `i IN tn'.t_mem` by
         (qpat_assum `!old_id old_off old_size i. FLOOKUP v.vs_allocas old_id = SOME (old_off,old_size) /\ _ ==> i IN tn'.t_mem`
            (qspecl_then [`old_id`,`old_off`,`old_size`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          disch_then ACCEPT_TAC)) >>>
  HEADGOAL (qpat_assum `!old_id old_off old_size i. FLOOKUP s0.vs_allocas old_id = SOME (old_off,old_size) /\ _ ==> i IN tn0.t_mem`
         (qspecl_then [`old_id`,`old_off`,`old_size`,`i`] mp_tac) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>>
  HEADGOAL (
    sg `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) t' /\
       storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gf' tf' t'`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (fn post => map_every (fn i => assume_tac (cj i (REWRITE_RULE [expr_post_def] post))) [1,2])
      assume_tac)) >> rpt conj_tac) >>>
  HEADGOAL (
    qpat_assum `!H. stmt_state_rel H ctx func cenv cx _ t ==> _ t'`
      (qspec_then `H` MATCH_MP_TAC) >>
    qpat_assum `!H. stmt_state_rel H ctx func cenv cx _ v ==> _ t`
      (qspec_then `H` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `!D d. ghost_inv_at D lo d cenv cx _ Gf tf t ==> _ t'`
      (qspecl_then [`DF H`,`d`] MATCH_MP_TAC) >>
    qpat_assum `!D d. ghost_inv_at D lo d cenv cx _ G' tn' v ==> _ t`
      (qspecl_then [`DF H`,`d`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    `sa.cs_next_var <= ss.cs_next_var` by decide_tac >>
    `FLOOKUP t'.vs_allocas su.cs_next_id = SOME (b',type_memory_size_list tvs)` by simp[] >>
    `!n a len. local_region cenv (ee with gas_obs := []).scopes t' n a len ==>
       b' + type_memory_size_list tvs <= a \/ a + len <= b'` by
      (qpat_assum `!n a len. local_region cenv _ t n a len ==> regions_disjoint _ _ _ _` mp_tac >>
       simp[regions_disjoint_def])) >>>
  HEADGOAL (
    qpat_assum `!todo ops1 k p cur shadow_cur src u Gu tu. _ ==> _`
      (qspecl_then [`gs`,`elems`,`0`,`b'`,`ss`,`shadow_ss`,`ee with gas_obs := []`,
        `t'`,`Gf'`,`tf'`] mp_tac) >>
    simp[NoAsms] >> impl_tac) >>>
  HEADGOAL (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t' /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (ACCEPT_TAC o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_start_gas_obs]
      o CONJUNCT1)) >>>
  HEADGOAL (
    disj1_tac >>
    qexistsl_tac [`su.cs_next_id`,`b'`,`type_memory_size_list tvs`] >>
    simp[] >>
    qpat_assum `!n a len. local_region cenv (ee with gas_obs := []).scopes t' n a len ==> _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>>
  HEADGOAL (
    qpat_assum `LENGTH tys = LENGTH tvs` (fn len =>
    qpat_assum `w2n (n2w b':256 word) = b'` (fn addr =>
    qpat_assum `!i. i < LENGTH tys ==> ?x. EL i elems = Var x /\ _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [len,addr])))) >>>
  HEADGOAL (
    qpat_assum `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) t'` mp_tac >>
    simp[NoAsms,alloca_frame_def]) >>>
  HEADGOAL strip_tac >>>
  HEADGOAL (
    `gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace),lo,
        gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s0,G0,tn0) marks (OK t',Gf',tf')` by
      (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
         (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append o CONJUNCT1) >>
       disch_then (qspecl_then [`v`,`G'`,`tn'`,`[]`,`OK t'`,`Gf'`,`tf'`] mp_tac) >>
       simp[])) >>>
  HEADGOAL (
    `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t'` by
      (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t',Gf',tf')` (fn path =>
       qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
       qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
         ACCEPT_TAC (MATCH_MP bodyFullSharedTheory.return_buf_allocas_path
           (LIST_CONJ [path,frame,sep]))))))) >>>
  HEADGOAL (sg `EVERY (\g. ?bt. g = BaseTarget bt) gs`) >>>
  HEADGOAL (
    rewrite_tac[EVERY_MEM] >> BETA_TAC >> qx_gen_tac `g` >> disch_tac >>
    qpat_assum `EVERY (\h. case h of BaseTarget _ => _ | TupleTarget _ => F) gs`
      (qspec_then `g` mp_tac o BETA_RULE o PURE_REWRITE_RULE [EVERY_MEM]) >>
    Cases_on `g` >> simp[]) >>>
  HEADGOAL (
    qpat_assum `gas_outcome_full _ _ _ _ (assign_tuple_target_list cx gs vs)
      (ee with gas_obs := [],t',Gf',tf') _ _` (fn outcome =>
      qpat_assum `return_buf_frame d cenv ss t'` (fn frame =>
        qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t'`
          (fn floor => assume_tac (BETA_RULE (MATCH_MP
            bodyFullSharedTheory.gas_outcome_full_return_buf_allocas_from
            (LIST_CONJ [outcome,frame,floor]))))))) >>>
  HEADGOAL (qmatch_goalsub_abbrev_tac `gas_outcome_full cfg _ _ _ _ _ Q R` >>
    sg `gas_outcome_full cfg (cx_tops cx) cx st0 (assign_tuple_target_list cx gs vs)
      (ee with gas_obs := [],t',Gf',tf') Q R`) >>>
  HEADGOAL (
    simp[Abbr `cfg`] >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    qpat_assum `gas_outcome_full _ _ _ _ (assign_tuple_target_list cx gs vs)
      (_,t',Gf',tf') (\H res ee G tn t. _ /\ _) _` (irule_at Any) >>
    BETA_TAC >> reverse conj_tac >- simp[Abbr `R`] >>
    map_every qx_gen_tac [`H`,`res`,`fin`,`Gend`,`tn_end`,`s_end`] >>
    disch_then (map_every strip_assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    `fin with gas_obs := [] = fin` by
      simp[vyperStateTheory.evaluation_state_component_equality] >>
    qpat_assum `fin with gas_obs := [] = fin` (fn normalized =>
      qpat_assum `!tail. assign_tuple_target_list cx gs vs _ = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [normalized])))) >>>
  HEADGOAL (sg `res = INL ()`) >>>
  HEADGOAL (Cases_on `res` >- simp[]) >>>
  HEADGOAL (
    rename1 `INR exc = INL ()` >>
    qpat_assum `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) = _`
      (fn eq =>
        qpat_assum `assign_tuple_target_list cx gs vs _ = (INR exc,fin)`
          (assume_tac o MATCH_MP vyperExprNoControlTheory.assign_tuple_targets_no_control o
           PURE_REWRITE_RULE [GSYM eq])) >>
    qpat_assum `stmt_lands lctx sb (INR exc) s_end` mp_tac >>
    qpat_assum `no_control_exc exc` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `exc` >>
    simp[stmt_lands_def,vyperExprNoControlTheory.no_control_exc_def]) >>>
  HEADGOAL (`cenv'' = cenv` by simp[]) >>>
  HEADGOAL (sg `MAP FDOM fin.scopes = MAP FDOM es.scopes`) >>>
  HEADGOAL (
    qpat_assum `EVERY (\g. ?bt. g = BaseTarget bt) gs` (fn flat =>
      qpat_assum `assign_tuple_target_list cx gs vs _ = (res,fin)` (fn eval =>
      qpat_assum `res = INL ()` (fn normal =>
      qpat_assum `MAP FDOM es.scopes = MAP FDOM ee.scopes` (fn initial =>
        ACCEPT_TAC (TRANS
          (SIMP_RULE (srw_ss()) [] (MATCH_MP tuple_flat_targets_success_scopes
            (CONJ flat (PURE_REWRITE_RULE [normal] eval))))
          (SYM initial))))))) >>>
  HEADGOAL (sg `return_buf_sep d cenv fin s_end`) >>>
  HEADGOAL (
    irule (INST_TYPE [alpha |-> ``:256``] bodyFullSharedTheory.return_buf_sep_locals_kept) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_x_assum `cenv'' = cenv` SUBST_ALL_TAC >>
    qpat_assum `Abbrev (Q = _)`
      (fn eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
    BETA_TAC >> qexists_tac `cenv` >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    sg `gas_outcome_full cfg (cx_tops cx) cx st0 (assign_tuple_target_list cx gs vs)
      (ee with gas_obs := [],v,G',tn') Q R`) >>>
  HEADGOAL (
    qpat_assum `Abbrev (cfg = _)` (fn abbrev =>
      let val cfg_eq = REWRITE_RULE [markerTheory.Abbrev_def] abbrev in
        PURE_REWRITE_TAC [cfg_eq] >>
        irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
        qexistsl_tac [`Gf'`,`t'`,`tf'`] >>
        conj_tac
        >- (qx_gen_tac `H` >>
            qpat_assum `!D. gas_origin_ptr_path _ (v,G',tn') [] (OK t',Gf',tf')`
              (qspec_then `DF H` ACCEPT_TAC)) >>
        qpat_assum `gas_outcome_full cfg _ _ _ (assign_tuple_target_list cx gs vs)
          (_,t',Gf',tf') Q R` (ACCEPT_TAC o PURE_REWRITE_RULE [cfg_eq])
      end)) >>>
  HEADGOAL (
    qpat_assum `Abbrev (cfg = _)`
      (fn eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
    pure_rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_bind >> BETA_TAC >> rpt conj_tac) >>>
  HEADGOAL (simp[cj 9 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>>
  HEADGOAL (
    rpt strip_tac >>
    rename1 `gas_marked_exec _ _ _ _ _ (INL source_v) source_mid (OK source_end)` >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`source_mid`,`source_end`,`source_v`] >>
    BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `storage_trace_frame (bind (eval_expr cx e) (read_result cx))`
      ACCEPT_TAC) >>>
  HEADGOAL (
    irule gasOutcomeFullComposeTheory.gas_outcome_full_intro >>
    qexistsl_tac [`G'`,`ee`,`marks`,`OK v`,`INL (ArrayV (TupleV vs))`,`tn'`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >> BETA_TAC >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (assume_tac o CONJUNCT1) >>
    qpat_assum `Abbrev (cfg = _)` (fn abbrev =>
      qpat_assum `gas_outcome_full cfg _ _ _ (assign_tuple_target_list cx gs vs) (_,v,G',tn') Q R`
        (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>
    qpat_assum `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) = _`
      (fn source_eq => simp[NoAsms,source_eq]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (qpat_x_assum `(if _ then _ else _) su = (staged,sl)` mp_tac >>
    simp[comp_return_def] >> strip_tac >> gvs[]) >>>
  HEADGOAL (
    `0 < type_memory_size_list tvs` by
      (`0 < type_slot_size (TupleTV tvs)` by metis_tac[assignable_type_slot_size_pos] >>
       drule (cj 1 valueEncodingPropsTheory.type_memory_size_pos) >>
       simp[valueEncodingTheory.type_memory_size_def])) >>>
  HEADGOAL (
    qpat_assum `ptr_val_ok _ _ _ _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def,is_word_type_def]) >>
    qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
      (mp_tac o Q.SPECL [`TupleTV tvs`,`w`] o REWRITE_RULE [ptr_mem_ok_def]) >>
    simp[is_word_type_def,val_footprint_def,valueEncodingTheory.type_memory_size_def] >> strip_tac >>
    qpat_assum `expr_store_bound _ _ _ _ _`
      (mp_tac o Q.SPECL [`TupleTV tvs`,`w`] o REWRITE_RULE [exprSimMemDefsTheory.expr_store_bound_def]) >>
    simp[is_word_type_def,val_store_size_def,valueEncodingTheory.type_memory_size_def] >> strip_tac >>
    qpat_assum `op = Var x` SUBST_ALL_TAC) >>>
  HEADGOAL (
    `lookup_var x v = SOME w` by fs[eval_operand_def] >>
    `ptr_covers G' tn' x v (type_memory_size_list tvs)` by
      (rewrite_tac[ptr_covers_def] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl_tac [`w`,`b`,`sz`] >> rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC,
         qpat_assum `w2n w + val_store_size (TupleTV tvs) _ <= b + sz` mp_tac >>
         simp[NoAsms,val_store_size_def,valueEncodingTheory.type_memory_size_def,ADD_COMM]]) >>
    `v.vs_alloca_next < dimword (:256)` by
      (qpat_assum `stmt_state_rel _ _ _ _ _ _ v`
         (ACCEPT_TAC o MATCH_MP alloca_room_next_lt o
          MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room))) >>>
  HEADGOAL (
    `w2n w + type_memory_size_list tvs <= v.vs_alloca_next /\
     w2n w + type_memory_size_list tvs < dimword (:256)` by
      (qpat_assum `type_memory_size_list tvs + w2n w <= v.vs_alloca_next` mp_tac >>
       qpat_assum `v.vs_alloca_next < dimword (:256)` mp_tac >> decide_tac)) >>>
  HEADGOAL (
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    `allocas_from lo v` by
      (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ v`
         (ACCEPT_TAC o cj 7 o REWRITE_RULE [ghost_inv_at_def])) >>
    `local_ptrs_reserved cenv sl` by
      (match_mp_tac (Q.SPECL [`cenv`,`sa`,`sl`] local_ptrs_reserved_next_var) >>
       conj_tac >> first_assum ACCEPT_TAC) >>
    `not_fresh_at sl x` by
      (qpat_assum `lower_value compile_expr cenv (TupleT tys) e sa = (Var x,sl)` (fn code =>
         qpat_assum `local_ptrs_reserved cenv sa` (fn reserved =>
           qspec_then `x` mp_tac
             (MATCH_MP exprOperandVarTheory.compile_lower_value_var (CONJ code reserved)))) >>
       simp[NoAsms]) >>
    `~v.vs_halted` by
      (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK v,G',tn')`
         (ACCEPT_TAC o MATCH_MP fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted o
          CONJUNCT2 o MATCH_MP gas_origin_ptr_path_projections))) >>>
  HEADGOAL (
    `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x` by
      (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[]) >>
    `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x` by
      (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[])) >>>
  HEADGOAL (
    `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (ee with gas_obs := []) v` by
      simp[exprLoweringPropsTheory.stmt_state_rel_start_gas_obs] >>
    `dead_lo_ok (storage_trace_horizon ee.storage_trace)
       (DF (storage_trace_horizon ee.storage_trace)) lo cenv cx` by simp[] >>
    sg `lo <= w2n w`) >>>
  HEADGOAL (
    irule (INST_TYPE [alpha |-> ``:256``] tuple_immutable_rhs_floor) >>
    qexistsl [`DF (storage_trace_horizon ee.storage_trace)`,
      `storage_trace_horizon ee.storage_trace`, `cenv`, `ctx`, `cx`, `env`,
      `ee with gas_obs := []`, `func`, `Var x`, `v`, `sa`, `sl`, `tops`,
      `tvs`, `TupleT tys`, `ArrayV (TupleV vs)`] >>
    simp[is_word_type_def,val_footprint_def,valueEncodingTheory.type_memory_size_def]) >>>
  HEADGOAL (
    drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)
      (INST_TYPE [alpha |-> ``:256``] body_assign_tuple_load_all_path) >>
    disch_then (drule_at (Pat `ptr_covers G' tn' x v _`)) >>
    disch_then (drule_at (Pat `lookup_var x v = SOME w`)) >>
    disch_then (drule_at (Pat `values_have_types _ _`)) >>
    disch_then (qspec_then `lo` mp_tac) >>
    disch_then (qspec_then `func` mp_tac) >>
    disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
    disch_then (qspec_then `ee with gas_obs := []` mp_tac) >>
    disch_then (qspec_then `cx` mp_tac) >>
    disch_then (qspec_then `ctx` mp_tac) >>
    disch_then (qspec_then `PG` mp_tac)) >>>
  HEADGOAL ((impl_tac >- (simp[] >> metis_tac[valueEncodingPropsTheory.val_in_memory_tuple])) >>
    disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`t'`,`Gf'`,`tf'`] (map_every assume_tac o CONJUNCTS))))) >>>
  HEADGOAL (
    `ci_mono sl ss` by
      (qpat_assum `compile_tuple_load_all cenv (Var x) tys 0 sl = (elems,ss)` (fn code =>
         ACCEPT_TAC (REWRITE_RULE [code,pairTheory.SND] (Q.SPECL [`cenv`,`Var x`,
           `tys`,`0`,`sl`] (cj 4 stmtLoweringMonoTheory.ci_mono_list_helpers))))) >>
    `sa.cs_next_id <= sl.cs_next_id` by
      (qpat_assum `lower_value compile_expr _ _ e sa = (_,sl)`
        (ACCEPT_TAC o cj 3 o MATCH_MP (cj 2 compile_expr_grows))) >>
    `sl.cs_next_id <= ss.cs_next_id` by fs[ci_mono_def] >>
    `sa.cs_next_id <= ss.cs_next_id /\ sa.cs_next_var <= ss.cs_next_var` by decide_tac) >>>
  HEADGOAL (
    `!x. not_fresh_at sa x ==> not_fresh_at sl x` by
      (gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sa` >> simp[]) >>
    `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at ss x` by
      (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
    `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at ss x` by
      (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sl` >> simp[]) >>
    `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w` by
      (rpt strip_tac >> simp[]) >>
    `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t'.vs_allocas aid = SOME ent` by
      (rpt strip_tac >> simp[])) >>>
  HEADGOAL (
    qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'`
      (strip_assume_tac o PURE_REWRITE_RULE [ghost_kept_at_def]) >>
    `!x. not_fresh_at sa x ==> FLOOKUP Gf' x = FLOOKUP G0 x /\
                                op_taint tf' (Var x) = op_taint tn0 (Var x)` by
      (rpt strip_tac >> simp[])) >>>
  HEADGOAL (
    `!n a cap. local_region cenv (ee with gas_obs := []).scopes t' n a cap <=>
      local_region cenv (ee with gas_obs := []).scopes v n a cap` by
      (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
       qexists_tac `sl` >> simp[]) >>
    `!mem. mem_agree_outside tf'.t_mem t'.vs_memory mem ==>
      val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) mem` by
      (qpat_assum `!mem. _ ==> tuple_in_memory vs tvs (w2n w + 0) mem` mp_tac >>
       simp[Once valueEncodingDefsTheory.val_in_memory_def]) >>
    `w2n w + type_memory_size_list tvs <= t'.vs_alloca_next` by simp[]) >>>
  HEADGOAL (
    Q.SUBGOAL_THEN `type_memory_size_list tvs = 0 \/
       (?aid b sz. FLOOKUP t'.vs_allocas aid = SOME (b,sz) /\ aid < ss.cs_next_id /\
         b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
         (!n a len. local_region cenv (ee with gas_obs := []).scopes t' n a len ==>
           b+sz <= a \/ a+len <= b)) \/
       (?n b sz. local_region cenv (ee with gas_obs := []).scopes t' n b sz /\
         b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
         local_path_at cenv cx n (w2n w-b) (TupleTV tvs))` assume_tac) >>>
  HEADGOAL (
    qpat_assum `!n a cap. local_region cenv _ t' n a cap <=> local_region cenv _ v n a cap`
      (fn regions =>
       qpat_assum `t'.vs_allocas = v.vs_allocas` (fn allocas =>
         PURE_REWRITE_TAC [regions,allocas])) >>
    simp[NoAsms] >>
    asm "rhs_window" (DISJ_CASES_THEN2 assume_tac
      (DISJ_CASES_THEN2
        (qx_choosel_then [`root_aid`,`root_b`,`root_sz`]
          (map_every assume_tac o CONJUNCTS))
        (qx_choosel_then [`root_n`,`root_b`,`root_sz`]
          (map_every assume_tac o CONJUNCTS))))
  ) >>>
  HEADGOAL (disj1_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    disj2_tac >> disj1_tac >> qexistsl_tac [`root_aid`,`root_b`,`root_sz`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,ALL_TAC]) >>>
  HEADGOAL (
    qpat_assum `root_aid < sl.cs_next_id` (fn below =>
      qpat_assum `sl.cs_next_id <= ss.cs_next_id` (fn forward =>
        ACCEPT_TAC (MATCH_MP LESS_LESS_EQ_TRANS (CONJ below forward))))) >>>
  HEADGOAL (
    qpat_assum `w2n w + type_memory_size_list tvs <= root_b + root_sz`
      (ACCEPT_TAC o PURE_REWRITE_RULE
          [Q.SPECL [`w2n w`,`type_memory_size_list tvs`] ADD_COMM])) >>>
  HEADGOAL (
    disj2_tac >> disj2_tac >> qexistsl_tac [`root_n`,`root_b`,`root_sz`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      qpat_assum `w2n w + type_memory_size_list tvs <= root_b + root_sz`
        (ACCEPT_TAC o PURE_REWRITE_RULE
          [Q.SPECL [`w2n w`,`type_memory_size_list tvs`] ADD_COMM])]) >>>
  HEADGOAL (
    `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (ee with gas_obs := []) t'` by
      (qpat_assum `!H. stmt_state_rel H ctx func cenv cx _ v ==> _ t'`
        (qspec_then `storage_trace_horizon ee.storage_trace` MATCH_MP_TAC) >>
       first_assum ACCEPT_TAC) >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx _ t'`
        (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)))) >>>
  HEADGOAL (
    `alloca_inv v` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx ee v`
         (ACCEPT_TAC o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv)) >>
    `gas_marked_path T ctx func v 0 (OK t')` by
      (qpat_assum `!D. gas_origin_ptr_path _ (v,G',tn') [] (OK t',Gf',tf')`
         (qspec_then `DF (storage_trace_horizon ee.storage_trace)`
            (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
             CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections)) >> simp[]) >>
    `alloca_history func t' /\ v.vs_alloca_next <= t'.vs_alloca_next` by
      (drule_all bodyMemBopRestWordPathTheory.rest_word_marked_allocation_posts >> simp[]) >>
    `s0.vs_alloca_next <= t'.vs_alloca_next` by decide_tac) >>>
  HEADGOAL (
    `return_buf_frame d cenv ss t'` by
      (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
       qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >> decide_tac)) >>>
  HEADGOAL (
    `!fn inst z. frag_reachable ctx func t' fn inst z ==> dalloca_no_wrap inst z` by
      (qpat_assum `body_inv tops ctx cenv cx`
        (mp_then Any mp_tac bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap) >>
       disch_then (qspecl_then [`func`,`t'`] assume_tac) >> rpt strip_tac >>
       rename1 `frag_reachable ctx func t' rf ri rz` >>
       qpat_assum `!fn inst u. MEM func ctx.ctx_functions /\ frag_reachable ctx func t' fn inst u ==> _`
         (qspecl_then [`rf`,`ri`,`rz`] mp_tac) >>
       impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC)) >>>
  HEADGOAL (
    `gas_marked_path F ctx func s0 (LENGTH marks) (OK v)` by
      (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK v,G',tn')`
        (mp_tac o MATCH_MP fragGasModeTheory.gas_marked_path_exec o
         MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
         CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections) >>
       simp[fragGasModeTheory.gas_marked_path_def]) >>
    `~block_is_terminated sl` by
      (irule assignPlaceEndpointTheory.endpoint_path_open >>
       qpat_assum `gas_marked_path F ctx func s0 (LENGTH marks) (OK v)`
         (irule_at Any) >>
       qpat_assum `cs_extends sa sl` (irule_at Any) >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>>
  HEADGOAL (
    `gas_marked_path F ctx func v 0 (OK t')` by
      (qpat_assum `!D. gas_origin_ptr_path _ (v,G',tn') [] (OK t',Gf',tf')`
         (qspec_then `DF (storage_trace_horizon ee.storage_trace)`
           (mp_tac o MATCH_MP fragGasModeTheory.gas_marked_path_exec o
            MATCH_MP fragGasOriginTheory.gas_origin_path_erase o
            CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections)) >>
       simp[fragGasModeTheory.gas_marked_path_def]) >>
    `~block_is_terminated ss` by
      (irule assignPlaceEndpointTheory.endpoint_path_open >>
       qpat_assum `gas_marked_path F ctx func v 0 (OK t')` (irule_at Any) >>
       qpat_assum `cs_extends sl ss` (irule_at Any) >> simp[])) >>>
  HEADGOAL (
    `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
      (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
       simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
            vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
    `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
      (gen_tac >> disch_tac >>
       `valid_horizon cx st0 H (es with gas_obs := obs).storage_trace` suffices_by simp[] >>
       irule (INST_TYPE [alpha |-> ``:value``] vyperStorageFootprintTheory.valid_horizon_frame) >>
       qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`,
         `INL (ArrayV (TupleV vs))`, `ee with gas_obs := []`] >> simp[])) >>>
  HEADGOAL (
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by simp[] >>
    qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >> strip_tac) >>>
  HEADGOAL (
    `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` by simp[]) >>>
  HEADGOAL (
    `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) v` by
      (qpat_assum `stmt_state_rel _ ctx func cenv cx es s0` (fn rel =>
       qpat_assum `local_ptrs_reserved cenv sa` (fn reserved =>
       qpat_assum `MAP FDOM (ee with gas_obs := []).scopes = MAP FDOM es.scopes` (fn scopes =>
       qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x v = SOME w` (fn regs =>
       qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz v.vs_memory = _` (fn mem =>
         ACCEPT_TAC (MATCH_MP stmtSimDefsTheory.alloca_frame_of_mem_frame
            (LIST_CONJ [rel,reserved,scopes,regs,mem]))))))))) >>>
  HEADGOAL (
    sg `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) t'`) >>>
  HEADGOAL (rewrite_tac[alloca_frame_def] >>
    map_every qx_gen_tac [`old_id`,`old_off`,`old_size`] >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    qpat_assum `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) v`
      (qspecl_then [`old_id`,`old_off`,`old_size`] mp_tac o REWRITE_RULE [alloca_frame_def]) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then (fn frame =>
      qpat_assum `t'.vs_memory = v.vs_memory` (fn mem =>
        qpat_assum `!n a cap. local_region cenv _ t' n a cap <=> local_region cenv _ v n a cap`
          (fn regs => ACCEPT_TAC (PURE_REWRITE_RULE [GSYM mem, GSYM regs] frame))))) >>>
  HEADGOAL (
    sg `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) /\
       off <= i /\ i < off+sz /\ i IN tf'.t_mem ==> i IN tn0.t_mem`) >>>
  HEADGOAL (
    qpat_assum `tf'.t_mem = tn'.t_mem` (fn mem => PURE_REWRITE_TAC [mem]) >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    sg `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) t' /\
       storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) Gf' tf' t'`) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
      (fn post => map_every (fn i => assume_tac (cj i (REWRITE_RULE [expr_post_def] post))) [1,2])
      assume_tac)) >> rpt conj_tac) >>>
  HEADGOAL (
    qpat_assum `!H. stmt_state_rel H ctx func cenv cx _ v ==> _ t'`
      (qspec_then `H` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `!D d. ghost_inv_at D lo d cenv cx _ G' tn' v ==> _ t'`
      (qspecl_then [`DF H`,`d`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `!todo ops1 k p cur shadow_cur src u Gu tu. _ ==> _`
      (qspecl_then [`gs`,`elems`,`0`,`w2n w`,`ss`,`shadow_ss`,`ee with gas_obs := []`,
        `t'`,`Gf'`,`tf'`] mp_tac) >>
    simp[NoAsms] >> impl_tac) >>>
  HEADGOAL (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, ALL_TAC]) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t' /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      qpat_assum `stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) t'`
        (ACCEPT_TAC o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_start_gas_obs])]) >>>
  HEADGOAL (
    qpat_assum `type_memory_size_list tvs = 0 \/
      (?aid b sz. FLOOKUP t'.vs_allocas aid = SOME (b,sz) /\ _) \/ _`
      (fn window => mp_tac window >>
        simp[NoAsms,Q.SPECL [`w2n (w:256 word)`,`type_memory_size_list tvs`] ADD_COMM])) >>>
  HEADGOAL (
    qpat_assum `LENGTH tys = LENGTH tvs` (fn len =>
    qpat_assum `!i. i < LENGTH tys ==> ?x. EL i elems = Var x /\ _`
      (ACCEPT_TAC o PURE_REWRITE_RULE
        [len,ADD_CLAUSES,Q.SPECL
          [`w2n (w:256 word)`,`SUM (MAP type_memory_size (TAKE i tvs))`] ADD_COMM]))) >>>
  HEADGOAL (
    qpat_assum `alloca_frame cenv es sa s0 cenv (ee with gas_obs := []) t'` mp_tac >>
    simp[NoAsms,alloca_frame_def]) >>>
  HEADGOAL strip_tac >>>
  HEADGOAL (
    `gas_origin_ptr_path (DF (storage_trace_horizon ee.storage_trace),lo,
        gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s0,G0,tn0) marks (OK t',Gf',tf')` by
      (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
         (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append o CONJUNCT1) >>
       disch_then (qspecl_then [`v`,`G'`,`tn'`,`[]`,`OK t'`,`Gf'`,`tf'`] mp_tac) >>
       simp[])) >>>
  HEADGOAL (
    `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t'` by
      (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t',Gf',tf')` (fn path =>
       qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
       qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
         ACCEPT_TAC (MATCH_MP bodyFullSharedTheory.return_buf_allocas_path
           (LIST_CONJ [path,frame,sep]))))))) >>>
  HEADGOAL (sg `EVERY (\g. ?bt. g = BaseTarget bt) gs`) >>>
  HEADGOAL (
    rewrite_tac[EVERY_MEM] >> BETA_TAC >> qx_gen_tac `g` >> disch_tac >>
    qpat_assum `EVERY (\h. case h of BaseTarget _ => _ | TupleTarget _ => F) gs`
      (qspec_then `g` mp_tac o BETA_RULE o PURE_REWRITE_RULE [EVERY_MEM]) >>
    Cases_on `g` >> simp[]) >>>
  HEADGOAL (
    qpat_assum `gas_outcome_full _ _ _ _ (assign_tuple_target_list cx gs vs)
      (ee with gas_obs := [],t',Gf',tf') _ _` (fn outcome =>
      qpat_assum `return_buf_frame d cenv ss t'` (fn frame =>
        qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t'`
          (fn floor => assume_tac (BETA_RULE (MATCH_MP
            bodyFullSharedTheory.gas_outcome_full_return_buf_allocas_from
            (LIST_CONJ [outcome,frame,floor]))))))) >>>
  HEADGOAL (qmatch_goalsub_abbrev_tac `gas_outcome_full cfg _ _ _ _ _ Q R` >>
    sg `gas_outcome_full cfg (cx_tops cx) cx st0 (assign_tuple_target_list cx gs vs)
      (ee with gas_obs := [],t',Gf',tf') Q R`) >>>
  HEADGOAL (
    simp[Abbr `cfg`] >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
    qpat_assum `gas_outcome_full _ _ _ _ (assign_tuple_target_list cx gs vs)
      (_,t',Gf',tf') (\H res ee G tn t. _ /\ _) _` (irule_at Any) >>
    BETA_TAC >> reverse conj_tac >- simp[Abbr `R`] >>
    map_every qx_gen_tac [`H`,`res`,`fin`,`Gend`,`tn_end`,`s_end`] >>
    disch_then (map_every strip_assume_tac o CONJUNCTS)) >>>
  HEADGOAL (
    `fin with gas_obs := [] = fin` by
      simp[vyperStateTheory.evaluation_state_component_equality] >>
    qpat_assum `fin with gas_obs := [] = fin` (fn normalized =>
      qpat_assum `!tail. assign_tuple_target_list cx gs vs _ = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [normalized])))) >>>
  HEADGOAL (sg `res = INL ()`) >>>
  HEADGOAL (Cases_on `res` >- simp[]) >>>
  HEADGOAL (
    rename1 `INR exc = INL ()` >>
    qpat_assum `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) = _`
      (fn eq =>
        qpat_assum `assign_tuple_target_list cx gs vs _ = (INR exc,fin)`
          (assume_tac o MATCH_MP vyperExprNoControlTheory.assign_tuple_targets_no_control o
           PURE_REWRITE_RULE [GSYM eq])) >>
    qpat_assum `stmt_lands lctx sb (INR exc) s_end` mp_tac >>
    qpat_assum `no_control_exc exc` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `exc` >>
    simp[stmt_lands_def,vyperExprNoControlTheory.no_control_exc_def]) >>>
  HEADGOAL (`cenv'' = cenv` by simp[]) >>>
  HEADGOAL (sg `MAP FDOM fin.scopes = MAP FDOM es.scopes`) >>>
  HEADGOAL (
    qpat_assum `EVERY (\g. ?bt. g = BaseTarget bt) gs` (fn flat =>
      qpat_assum `assign_tuple_target_list cx gs vs _ = (res,fin)` (fn eval =>
      qpat_assum `res = INL ()` (fn normal =>
      qpat_assum `MAP FDOM es.scopes = MAP FDOM ee.scopes` (fn initial =>
        ACCEPT_TAC (TRANS
          (SIMP_RULE (srw_ss()) [] (MATCH_MP tuple_flat_targets_success_scopes
            (CONJ flat (PURE_REWRITE_RULE [normal] eval))))
          (SYM initial))))))) >>>
  HEADGOAL (sg `return_buf_sep d cenv fin s_end`) >>>
  HEADGOAL (
    irule (INST_TYPE [alpha |-> ``:256``] bodyFullSharedTheory.return_buf_sep_locals_kept) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_x_assum `cenv'' = cenv` SUBST_ALL_TAC >>
    qpat_assum `Abbrev (Q = _)`
      (fn eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
    BETA_TAC >> qexists_tac `cenv` >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    sg `gas_outcome_full cfg (cx_tops cx) cx st0 (assign_tuple_target_list cx gs vs)
      (ee with gas_obs := [],v,G',tn') Q R`) >>>
  HEADGOAL (
    qpat_assum `Abbrev (cfg = _)` (fn abbrev =>
      let val cfg_eq = REWRITE_RULE [markerTheory.Abbrev_def] abbrev in
        PURE_REWRITE_TAC [cfg_eq] >>
        irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
        qexistsl_tac [`Gf'`,`t'`,`tf'`] >>
        conj_tac
        >- (qx_gen_tac `H` >>
            qpat_assum `!D. gas_origin_ptr_path _ (v,G',tn') [] (OK t',Gf',tf')`
              (qspec_then `DF H` ACCEPT_TAC)) >>
        qpat_assum `gas_outcome_full cfg _ _ _ (assign_tuple_target_list cx gs vs)
          (_,t',Gf',tf') Q R` (ACCEPT_TAC o PURE_REWRITE_RULE [cfg_eq])
      end)) >>>
  HEADGOAL (
    qpat_assum `Abbrev (cfg = _)`
      (fn eq => PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
    pure_rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_bind >> BETA_TAC >> rpt conj_tac) >>>
  HEADGOAL (simp[cj 9 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>>
  HEADGOAL (
    rpt strip_tac >>
    rename1 `gas_marked_exec _ _ _ _ _ (INL source_v) source_mid (OK source_end)` >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`source_mid`,`source_end`,`source_v`] >>
    BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
    first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `storage_trace_frame (bind (eval_expr cx e) (read_result cx))`
      ACCEPT_TAC) >>>
  HEADGOAL (
    irule gasOutcomeFullComposeTheory.gas_outcome_full_intro >>
    qexistsl_tac [`G'`,`ee`,`marks`,`OK v`,`INL (ArrayV (TupleV vs))`,`tn'`] >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, ALL_TAC]) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >> BETA_TAC >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (assume_tac o CONJUNCT1) >>
    qpat_assum `Abbrev (cfg = _)` (fn abbrev =>
      qpat_assum `gas_outcome_full cfg _ _ _ (assign_tuple_target_list cx gs vs) (_,v,G',tn') Q R`
        (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>
    qpat_assum `assign_tuple_targets cx (TupleTarget gs) (ArrayV (TupleV vs)) = _`
      (fn source_eq => simp[NoAsms,source_eq]) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qmatch_asmsub_abbrev_tac
      `gas_origin_ptr_path (_,lo,_,ctx,func,PG) (s0,G0,tn0) marks (r_exit,G',tn')` >>
    `exit_result r_exit` by simp[Abbr `r_exit`,fragExecTheory.exit_result_def] >>
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ _ _ (r_exit,_,_) /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (assume_tac o CONJUNCT1 o CONJUNCT2)) >>>
  HEADGOAL (sg `?exc. (res:value + exception) = INR exc`) >>>
  HEADGOAL (
    qpat_assum `expr_exit res r_exit` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>>
  HEADGOAL (
    qpat_x_assum `res = INR exc` SUBST_ALL_TAC >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_intro >>
    qexistsl_tac [`G'`,`ee`,`marks`,`r_exit`,`INR exc`,`tn'`] >>
    rpt conj_tac) >>>
  HEADGOAL (
    qx_gen_tac `tail` >>
    rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
    qpat_assum `!tail. _ = (INR exc,ee with gas_obs := tail)`
      (qspec_then `tail` (fn rhs => simp[NoAsms,Once bind_def,rhs]))) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ _ _ (r_exit,_,_) /\ _` (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (BETA_TAC >> conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (disj2_tac >> conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (rpt conj_tac) >>>
  HEADGOAL (
    gen_tac >> simp[stmt_exit_ptr_def,
      GSYM (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        stmtSimPropsTheory.expr_exit_INR_type)]) >>>
  HEADGOAL (
    irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
      haltExitProjTheory.halt_exit_INR_type)) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `Abbrev (r_exit = _)` (fn abbrev =>
      simp[NoAsms,REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qmatch_asmsub_abbrev_tac
      `gas_origin_ptr_path (_,lo,_,ctx,func,PG) (s0,G0,tn0) marks (r_exit,G',tn')` >>
    `exit_result r_exit` by simp[Abbr `r_exit`,fragExecTheory.exit_result_def] >>
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ _ _ (r_exit,_,_) /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (assume_tac o CONJUNCT1 o CONJUNCT2)) >>>
  HEADGOAL (sg `?exc. (res:value + exception) = INR exc`) >>>
  HEADGOAL (
    qpat_assum `expr_exit res r_exit` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>>
  HEADGOAL (
    qpat_x_assum `res = INR exc` SUBST_ALL_TAC >>
    irule gasOutcomeFullComposeTheory.gas_outcome_full_intro >>
    qexistsl_tac [`G'`,`ee`,`marks`,`r_exit`,`INR exc`,`tn'`] >>
    rpt conj_tac) >>>
  HEADGOAL (
    qx_gen_tac `tail` >>
    rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
    qpat_assum `!tail. _ = (INR exc,ee with gas_obs := tail)`
      (qspec_then `tail` (fn rhs => simp[NoAsms,Once bind_def,rhs]))) >>>
  HEADGOAL (
    qx_gen_tac `H` >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
         gas_origin_ptr_path _ _ _ (r_exit,_,_) /\ _` (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (map_every assume_tac o CONJUNCTS)) >>>
  HEADGOAL (BETA_TAC >> conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (disj2_tac >> conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (rpt conj_tac) >>>
  HEADGOAL (
    gen_tac >> simp[stmt_exit_ptr_def,
      GSYM (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
        stmtSimPropsTheory.expr_exit_INR_type)]) >>>
  HEADGOAL (
    irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``]
      haltExitProjTheory.halt_exit_INR_type)) >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    qpat_assum `Abbrev (r_exit = _)` (fn abbrev =>
      simp[NoAsms,REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (sg `F`) >>>
  HEADGOAL (
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
       gas_origin_ptr_path _ _ _ (IntRet _ _,_,_) /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL] >>
    rename1 `expr_exit (INR exc) (IntRet _ _)` >>
    Cases_on `exc` >> simp[exprSimDefsTheory.expr_exit_def] >>
    rename1 `expr_exit (INR (Error err)) (IntRet _ _)` >>
    Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>>
  HEADGOAL (
    `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    qpat_assum `!H. ~valid_horizon cx st0 H ee.storage_trace`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    simp[]) >>>
  HEADGOAL (
    rename1 `gas_origin_ptr_focus _ _ _ (leaf,leaf_pg,leaf_g,leaf_tn,finish_state)` >>
    rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
    qexists_tac `marks` >> disj2_tac >> disj2_tac >>
    qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish_state`] >>
    conj_tac
    >- (pure_rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
        PURE_ONCE_REWRITE_TAC [ignore_bind_def] >>
        PURE_ONCE_REWRITE_TAC [bind_assoc] >>
        irule gasExemptCertTheory.gas_exempt_cert_error_value >>
        first_assum ACCEPT_TAC) >>
    qexists_tac `H` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>>
  HEADGOAL (
    rename1 `gas_origin_ptr_focus _ _ _ (leaf,leaf_pg,leaf_g,leaf_tn,finish_state)` >>
    rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
    qexists_tac `marks` >> disj1_tac >> conj_tac) >>>
  HEADGOAL (
    pure_rewrite_tac[stmtSimAssignTupleTheory.eval_assign_tuple_action] >>
    irule gasStorageTheory.gas_bad_storage_at_bind_left >> conj_tac
    >~ [`!v. storage_trace_frame (assign_tuple_targets _ _ v)`]
    >- simp[NoAsms, cj 9 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
    qpat_assum `gas_bad_storage_at _ _ _ _ _ _` ACCEPT_TAC) >>>
  HEADGOAL (
    CONV_TAC (RENAME_VARS_CONV
      ["horizon_witness", "leaf_witness", "pg_witness", "ghost_witness",
       "taint_witness", "state_witness"]) >>
    qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish_state`] >>
    conj_tac) >>>
  HEADGOAL (first_assum ACCEPT_TAC) >>>
  HEADGOAL (first_assum ACCEPT_TAC)
QED

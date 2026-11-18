(*
 * Tuple assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAssignTuple
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
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
  haltExitProj immutableRepSensitivity
  assignTuplePtrStoreWord stmtSimDeclStore vyperTypeArgFits instMemFrontier
  tupleTargetStoreProps vyperLookup stmtSimAssignStorageFacts stmtSimDefs exprSimDefs fragGasOriginPtr loweringSlice exprSimBufferStore[qualified,ignore_grammar] immutableDeployAssignFacts[qualified,ignore_grammar] bodyImmutableAugAssignStore[qualified,ignore_grammar] immutableDeployAssignStateFrame[qualified,ignore_grammar] exprSimLiteralBuffer[qualified,ignore_grammar] exprSimAbiEncodeStateTransport[qualified,ignore_grammar] exprSimAggregateLoops[qualified,ignore_grammar] vyperTypeContract[qualified,ignore_grammar] supportedProgram[qualified,ignore_grammar] exprSimHyps structFieldsProps immutableRelation gasContext immSectionDead compileVyper bodyStorageMetadata ctorDeployDeadSectionFrame ctorDeployDeadSection pred_set immutableCopyExecution immutableDeployOperandTransfer fragGasSeqPtr stmtReasonLitFragMemory immutableWordExecution fragExecMem memSafeRun venomExecSemantics exprSimCopy venomInst unitTransformDefs codegenRel contextCodegenRel bodyPtrBopInRepresentation immutableAssignCompose immutableDeployAssignBytes immutableDeployAssignAdmissible valueEncodingProps venomMemProps vyperTypeValues typedCopyOriginPtr placeStoreDynPrepare bodyMemBopRestWordPath allocaSiteResource exprSimPtrLiteralBuffer exprSimAlloc exprOperandVar fragGasMode vyperStorageFootprint[qualified,ignore_grammar] stmtSimAppendStorageCompose[qualified,ignore_grammar] bodyFullMemoryStage[qualified,ignore_grammar]

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
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
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
    (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (map_every assume_tac o CONJUNCTS)))
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
        gvs[stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
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
  rpt conj_tac >> first_assum ACCEPT_TAC
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
  cheat
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
    (!H. stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
         stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!H D. stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
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
    tf.t_mem = tn.t_mem DIFF {j | off <= j /\ j < off + 32}
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
  simp[GSYM lookup_var_def] >> metis_tac[]
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
    (!H. stmt_state_rel H ctx fn ce cx st s /\ storage_well_formed_on cx st (FST H) ==>
      stmt_post H ctx fn cx lctx ce ce sa sb st s (INL ()) fin q) /\
    (!H D. stmt_state_rel H ctx fn ce cx st s /\ dead_lo_ok H D lo ce cx /\
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
  `fin.scopes = st.scopes` by
    (drule_then ACCEPT_TAC vyperPlaceFramesTheory.write_immutable_place_scopes) >>
  `!x. not_fresh_at su x ==> lookup_var x q = lookup_var x t` by simp[] >>
  `alloca_frame ce st su t ce fin q` by
    (qpat_assum `stmt_state_rel _ ctx fn ce cx st t`
       (mp_then Any mp_tac immutableAssignComposeTheory.immutable_assign_suffix_alloca_frame) >>
     disch_then (drule_at (Pat `FLOOKUP ce.ce_module_vars _ = SOME (ImmutableLoc off)`)) >>
     disch_then (drule_all_then ACCEPT_TAC)) >>
  simp[] >> irule stmtSimDefsTheory.alloca_frame_trans >>
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

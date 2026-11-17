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
  tupleTargetStoreRun bodyFullMemoryStore stateRelProj wordLoadStorePtr
  assignTuplePtrStoreWord stmtSimDeclStore vyperTypeArgFits instMemFrontier
  tupleTargetStoreProps vyperLookup

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
val _ = HOLFlags.set_trace "types" 1;

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
  drule_all body_assign_tuple_storage_head_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choosel_then [`t`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`t`,`G`,`tf`] >>
  qpat_x_assum `t = _` kall_tac >> qpat_x_assum `tf = _` kall_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!st0 H. valid_horizon _ _ _ _ ==> _`
        (drule_then assume_tac) >>
      first_x_assum (qspec_then `H` drule) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!st0 H. valid_horizon _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  qpat_x_assum `!H D d. _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
    (qspecl_then [`H`,`D`,`d`] mp_tac) >> simp[]
QED

Resume body_assign_tuple_nonlocal_head_full_path[field]:
  FAIL_TAC "field store"
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
  cheat
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

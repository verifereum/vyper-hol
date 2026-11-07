Theory bodyPtrStructLitProducerAddress
Ancestors bodyPtrStructLitAllocationBridge bodyPtrStructLitMemoryIntegration
  bodyPtrStructLitNonmemoryIntegration bodyPtrStructLitUnwrapSeparation
  bodyPtrStructLitUnwrapFrame bodyPtrStructLitMemoryCaller
  bodyPtrStructLitMemoryUnwrap bodyPtrStructLitNonmemoryRead
  bodyPtrStructLitRawChild exprSafeOperand
  exprLowering compileEnv loweringPosts venomState venomExecSemantics compileEnv finite_map words

Theorem structlit_vv_post_root_value:
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  not_fresh_at sb root /\ eval_operand (Var root) t = SOME w ==>
  lookup_var root s = SOME w
Proof
  simp[vv_post_def, eval_operand_def] >> metis_tac[]
QED

Theorem structlit_child_zero_add_address:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  eval_operand buf.buf_operand t = SOME w ==>
  lookup_var dst (update_var dst (w+0w) s with
    vs_inst_idx := SUC s.vs_inst_idx) = SOME w /\
  lookup_var root s = SOME w
Proof
  strip_tac >> drule alloc_buffer_safe_operand >> strip_tac >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule structlit_vv_post_root_value >> fs[safe_operand_def] >> metis_tac[]
QED

(* Companion to the coverage wrapper: the concrete load endpoint also retains
   every register other than its fresh output. *)
Theorem structlit_first_memory_word_register_continuation:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  fn_has_code sa sd fn /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  q.ptr_location = LocMemory /\ is_word_type cty /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)) /\
  vv_post ctx fn ce cx e es sb sm t ee tv (LocatedValue cty q) s /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue cty q) ee G tn s /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  buf.buf_operand = Var root /\ not_fresh_at sb root /\
  ptr_covers G tn root s N /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn ce cx e es sb su t ee v (Var load) s1 /\
    ptr_val_ok cx cty v (Var load) G1 tn1 s1 /\
    ghost_inv d ce cx ee G1 tn1 s1 /\
    ghost_kept ce es sb G0 tn0 t G1 tn1 /\
    s1.vs_current_bb = su.cs_current_bb /\
    s1.vs_inst_idx = LENGTH su.cs_current_insts /\
    ptr_covers G1 tn1 root s1 N /\
    (!r sz. r <> load /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz) /\
    (?r. dst = Var r /\ r <> load) /\
    (!x. x <> load ==> lookup_var x s1 = lookup_var x s)
Proof
  strip_tac >> drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `fn_has_code sm su fn` by (irule structlit_first_unwrap_code >> metis_tac[]) >>
  drule_all memory_word_unwrap_code >> strip_tac >>
  `?r. dst = Var r /\ r <> load` by
    (irule emitted_operand_fresh_separation >> metis_tac[]) >>
  drule_all raw_child_unwrap_compiler_frame >> strip_tac >>
  `cty = expr_type e` by
    (drule_all bodyPtrStructLitMemoryReadTheory.vv_post_memory_word_read >> simp[]) >>
  `ptr_vv_ok cx cty tv (LocatedValue cty q) ee G tn s` by metis_tac[] >>
  `!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> load` by
      metis_tac[] >>
  `root <> load` by metis_tac[] >>
  `not_local_ptr ce ee.scopes load` by simp[] >>
  gvs[] >> drule memory_word_unwrap_ptr_continuation >> simp[] >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`v`, `G1`, `tn1`, `s1`] >> simp[]
QED

Theorem structlit_first_nonmemory_word_register_continuation:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  fn_has_code sa sd fn /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (q.ptr_location = slot_loc tr \/
    (q.ptr_location = LocCode /\ ~ce.ce_is_ctor)) /\ is_word_type cty /\
  vv_post ctx fn ce cx e es sb sm t ee tv (LocatedValue cty q) s /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx cty tv (LocatedValue cty q) ee G tn s /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  buf.buf_operand = Var root /\ not_fresh_at sb root /\
  ptr_covers G tn root s N /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn ce cx e es sb su t ee v (Var load) s1 /\
    ptr_val_ok cx cty v (Var load) G1 tn1 s1 /\
    ghost_inv d ce cx ee G1 tn1 s1 /\
    ghost_kept ce es sb G0 tn0 t G1 tn1 /\
    s1.vs_current_bb = su.cs_current_bb /\
    s1.vs_inst_idx = LENGTH su.cs_current_insts /\
    ptr_covers G1 tn1 root s1 N /\
    (!r sz. r <> load /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz) /\
    (?r. dst = Var r /\ r <> load) /\
    (!x. x <> load ==> lookup_var x s1 = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `fn_has_code sm su fn` by (irule structlit_first_unwrap_code >> metis_tac[]) >>
  `~not_fresh_at sm load` by
    (irule (cj 3 nonmemory_word_unwrap_code) >> simp[] >>
     Cases_on `tr` >> gvs[slot_loc_def] >> metis_tac[]) >>
  `?r. dst = Var r /\ r <> load` by
    (irule emitted_operand_fresh_separation >> metis_tac[]) >>
  drule_all raw_child_unwrap_compiler_frame >> strip_tac >>
  `!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> load` by
      metis_tac[] >>
  `root <> load` by metis_tac[] >>
  `not_local_ptr ce ee.scopes load` by simp[] >>
  Cases_on `q.ptr_location = slot_loc tr`
  >- (drule storage_word_unwrap_continuation >> simp[] >>
      disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >> simp[] >>
      disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
      disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >> simp[] >>
      disch_then (qspecl_then [`tr`, `PG`, `D`] mp_tac) >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qexistsl [`v`, `G1`, `tn1`, `s1`] >> simp[]) >>
  gvs[] >> drule runtime_code_word_unwrap_continuation >> simp[] >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`v`, `G1`, `tn1`, `s1`] >> simp[]
QED

(* The endpoint equalities are the concrete ADD and load witnesses exported by
   their producers, not a frame assumption on an arbitrary counted endpoint.
   The allocation-table resource remains attached to its original word. *)
Theorem structlit_producer_word_load_address:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm) /\
  lookup_var root s = SOME a /\
  sA = (update_var dst (a+0w) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  is_word_type cty /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  ((q.ptr_location = LocMemory) \/
   (q.ptr_location = LocStorage) \/ (q.ptr_location = LocTransient) \/
   (q.ptr_location = LocCode /\ ~ce.ce_is_ctor)) /\
  s1 = (update_var load value sA with vs_inst_idx := SUC sA.vs_inst_idx) ==>
  lookup_var dst s1 = SOME w /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N)
Proof
  strip_tac >>
  `lookup_var root s = SOME w` by
    (irule (cj 2 structlit_child_zero_add_address) >> metis_tac[]) >>
  `~not_fresh_at sm load` by
    (Cases_on `q.ptr_location = LocMemory`
     >- (drule_all memory_word_unwrap_code >> simp[]) >>
     irule (cj 3 nonmemory_word_unwrap_code) >> simp[] >> metis_tac[]) >>
  `?r. Var dst = Var r /\ r <> load` by
    (irule emitted_operand_fresh_separation >> metis_tac[]) >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem structlit_producer_stack_unwrap_address:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm) /\
  lookup_var root s = SOME a /\
  sA = (update_var dst (a+0w) s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  unwrap_value ce (StackValue cty op) sm = (op,sm) /\
  lookup_var dst sA = SOME w /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N)
Proof
  strip_tac >>
  `lookup_var root s = SOME w` by
    (irule (cj 2 structlit_child_zero_add_address) >> metis_tac[]) >>
  gvs[unwrap_value_def, comp_return_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Actual struct-field compiler frames for storage, transient and runtime code. *)
Theory bodyPtrStructLitNonmemoryIntegration
Ancestors bodyPtrStructLitUnwrapFrame bodyPtrStructLitMemoryIntegration
  bodyPtrStructLitNonmemoryRead bodyPtrStructLitRawChild
  bodyPtrStructLitAddContinuation loweringPosts

Theorem structlit_first_nonmemory_word_continuation:
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
    ptr_covers G1 tn1 root s1 N
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `fn_has_code sm su fn` by (irule structlit_first_unwrap_code >> metis_tac[]) >>
  `~not_fresh_at sm load` by
    (irule (cj 3 nonmemory_word_unwrap_code) >> simp[] >>
     Cases_on `tr` >> gvs[slot_loc_def] >> metis_tac[]) >>
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

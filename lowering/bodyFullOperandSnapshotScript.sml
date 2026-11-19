Theory bodyFullOperandSnapshot
Ancestors
  bodyPtrBopRepresentationFrame bodyPtrDefs loweringPosts
  exprLowering compileEnv context freshWrites
  valueEncodingDefs valueEncodingProofs venomState finite_map words

(* A materialized operand is in its own allocation, so later writes to
   live locals, including Pop's length update, leave it intact. *)
Theorem compile_snapshot_vv_materialized_frame:
  compile_snapshot_vv cenv T vv sa = (saved,sm) /\
  ~is_word_type (vv_type vv) /\ vv_operand saved = Var p /\
  evaluate_type (get_tenv cx) (vv_type vv) = SOME tv /\ val_wf tv v /\
  ptr_val_ok cx (vv_type vv) v (Var p) G tn s /\
  not_fresh_at cut p /\ lookup_var p s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,sz) /\ aid < cut.cs_next_id /\
  val_footprint tv v <= sz /\
  (!n b len. local_region cenv es.scopes s n b len ==>
     w2n w + sz <= b \/ b + len <= w2n w) /\
  wb_frame cenv es ee cut s t /\ ghost_kept_at lo cenv es cut G tn s G' tn' ==>
  compile_materialize_vv cenv (vv_type vv) vv sa = (Var p,sm) /\
  saved = LocatedValue (vv_type vv) (mk_ptr (Var p) LocMemory) /\
  lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  mem_bytes_at (w2n w) sz t.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory /\
  FLOOKUP G' p = FLOOKUP G p /\ ptr_val_ok cx (vv_type vv) v (Var p) G' tn' t
Proof
  strip_tac >>
  `compile_materialize_vv cenv (vv_type vv) vv sa = (Var p,sm) /\
   saved = LocatedValue (vv_type vv) (mk_ptr (Var p) LocMemory)` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     Cases_on `compile_materialize_vv cenv (vv_type vv) vv sa` >>
     simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[vv_operand_def, mk_ptr_def]) >>
  `lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
   mem_bytes_at (w2n w) sz t.vs_memory = mem_bytes_at (w2n w) sz s.vs_memory` by
    (qpat_assum `wb_frame _ _ _ _ _ _` (mp_tac o REWRITE_RULE [wb_frame_def]) >>
     metis_tac[]) >>
  `FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)` by
    (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (mp_tac o Q.SPEC `p` o CONJUNCT1) >> simp[]) >>
  simp[] >>
  irule bop_ptr_val_ok_frame >> simp[] >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  simp[eval_operand_def] >> conj_tac
  >- (qpat_assum `mem_bytes_at (w2n w) sz t.vs_memory = _`
        (mp_tac o MATCH_MP (cj 1 mem_bytes_at_agree_window) o SYM) >>
      disch_then (qspecl_then [`w2n w`,`val_footprint tv v`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  `i < w2n w + sz` by decide_tac >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
  disch_then (qspecl_then [`aid`,`w2n w`,`sz`,`i`] mp_tac) >> simp[] >>
  disch_then irule >>
  rpt strip_tac >>
  qpat_assum `!n b len. local_region cenv es.scopes s n b len ==> _`
    (qspecl_then [`n`,`b`,`sz'`] drule) >>
  decide_tac
QED

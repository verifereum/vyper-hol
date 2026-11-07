Theory bodyPtrStructLitStoreLiveFrame
Ancestors bodyPtrStructLitEndpointAllocation bodyPtrStructLitSingleSlotMaterialize
  bodyPtrStructLitSourceFrame exprSimAlloc exprSimProps compileEnv
  loweringPosts exprLoweringProps localPtrsProps bodyPtrDefs
  finite_map venomState venomInst words

(* A region boundary rather than a second implementation of the store frame.
   literal_ptr_local_footprint_exterior gives pointwise exclusion; here the
   interval disjunction matches fresh_word_store_ghost_inv directly. *)
Theorem structlit_local_store_footprint:
  local_ptrs_rel fn ce es.scopes s /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    regions_disjoint b N lo sz) /\ b <= a /\ a + 32 <= b + N ==>
  !name entry p sz q.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME q ==>
    val_wf entry.type entry.value /\
    (w2n q + val_footprint entry.type entry.value <= a \/ a + 32 <= w2n q)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `local_region ce es.scopes s name (w2n q) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  conj_tac >- simp[] >>
  qpat_x_assum `!name lo sz. _ ==> _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem structlit_word_store_live_frame:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,N) /\
  expr_post ctx fn ce cx e es sb su t ee v value s /\
  ghost_inv d ce cx ee G tn s /\ lookup_var dst s = SOME a /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  b <= w2n a /\ w2n a + 32 <= b + N /\
  tn1 = step_taint (mk_inst iid MSTORE [Var dst;value] []) s
    (mstore (w2n a) w s) tn ==>
  stmt_state_rel ctx fn ce cx ee
    (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx) /\
  ghost_inv d ce cx ee G tn1
    (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `!name lo sz. local_region ce ee.scopes s name lo sz ==>
    regions_disjoint b N lo sz` by
    (rpt strip_tac >> irule structlit_endpoint_allocation_disjoint >> metis_tac[]) >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[expr_post_def] >>
  `FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,N)` by
    (irule structlit_expr_post_allocated >> metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (irule buffer_alloc_code >> metis_tac[]) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule literal_mstore_state_rel >>
      reverse conj_tac >- simp[] >>
      qexistsl [`b`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
        [STRING #"%" (toString sa.cs_next_var)]`, `N`] >>
      simp[mk_inst_def] >> fs[regions_disjoint_def]) >>
  irule fresh_word_store_ghost_inv >> simp[] >>
  reverse conj_tac
  >- (qexistsl [`dst`, `iid`, `tn`, `value`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule structlit_local_store_footprint >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]
QED

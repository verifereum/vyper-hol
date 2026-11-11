Theory bodyPtrSubscriptSeamArrayMemoryFrame
Ancestors
  exprSimSubscriptArrayFrame bodyPtrBopRepresentationFrame bodyPtrDefs
  exprSimAttributeFields loweringPosts finite_map
  bodyPtrPrecompileBuiltinsGhost logValueFramePtr
  exprSimSubscriptArraySource vyperState exprBopSimProps

Theorem vv_at_memory_taint_frame:
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  expr_sim_inv cenv cx env es /\ dynarray_free tv /\
  ghost_kept cenv es sb G tn s G' tn' ==>
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
      i IN tn'.t_mem ==> i IN tn.t_mem
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[ghost_kept_def] >> rpt strip_tac >>
      qpat_x_assum `!aid off sz i. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> gvs[]) 
  >- (rpt strip_tac >>
      `!k. dynarray_len_at cenv n k ==>
           i < b + k \/ b + k + 32 <= i` by
        (rpt strip_tac >> drule_all local_val_at_dynarray_apart >>
         decide_tac) >>
      gvs[ghost_kept_def] >>
      `b <= i /\ i < b + sz` by decide_tac >>
      qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem vv_at_ptr_mem_frame:
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_sim_inv cenv cx env es /\ dynarray_free tv /\
  wb_frame cenv es ee sb s s' /\
  ghost_kept cenv es sb G tn s G' tn' /\
  eval_operand p.ptr_operand s' = eval_operand p.ptr_operand s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  ptr_mem_ok cx ty v p.ptr_operand G tn s ==>
  ptr_mem_ok cx ty v p.ptr_operand G' tn' s'
Proof
  strip_tac >> irule bop_ptr_mem_ok_frame >>
  qexistsl_tac [`G`, `s`, `tn`, `tv`] >> simp[] >>
  conj_tac >- (gvs[ghost_kept_def] >> metis_tac[]) >>
  reverse conj_tac >- (gvs[vv_at_def] >> metis_tac[]) >>
  gen_tac >> disch_tac >> conj_tac
  >- (drule_all vv_at_memory_bytes_frame >> simp[]) >>
  metis_tac[vv_at_memory_taint_frame]
QED

Theorem vv_at_ptr_vv_memory_frame:
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_sim_inv cenv cx env es /\ dynarray_free tv /\
  wb_frame cenv es ee sb s s' /\
  ghost_kept cenv es sb G tn s G' tn' /\
  eval_operand p.ptr_operand s' = eval_operand p.ptr_operand s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  es'.scopes = es.scopes /\ es'.immutables = es.immutables /\
  ptr_vv_ok cx ty r (LocatedValue ty p) es G tn s ==>
  ptr_vv_ok cx ty r (LocatedValue ty p) es' G' tn' s'
Proof
  strip_tac >>
  `op_taint tn' p.ptr_operand = op_taint tn p.ptr_operand` by
    (drule ghost_kept_operand_taint >> simp[]) >>
  gvs[ptr_vv_ok_def] >>
  `read_result cx r es' = (INL v,es')` by
    (`FST (read_result cx r es') = FST (read_result cx r es)` by
       (irule read_result_nonstorage_frame >> simp[]) >>
     Cases_on `read_result cx r es'` >> gvs[] >>
     drule read_result_state >> simp[]) >>
  qexists_tac `v` >> simp[] >>
  irule vv_at_ptr_mem_frame >> metis_tac[]
QED

Theorem captured_memory_ptr_index_frame:
  vv_at cenv cx ty sa sb es r (LocatedValue ty p) s /\
  ptr_vv_ok cx ty r (LocatedValue ty p) es G tn s /\
  ptr_buf_ok cenv obj p.ptr_operand G s /\
  expr_post ctx func cenv cx idx es sb sc s es' iv iop s' /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_sim_inv cenv cx env es /\ dynarray_free tv /\
  ghost_kept cenv es sb G tn s G' tn' /\
  eval_operand p.ptr_operand s = SOME w /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  es'.scopes = es.scopes /\ es'.immutables = es.immutables ==>
  ptr_vv_ok cx ty r (LocatedValue ty p) es' G' tn' s' /\
  ptr_buf_ok cenv obj p.ptr_operand G' s'
Proof
  strip_tac >>
  `wb_frame cenv es es' sb s s'` by
    (gvs[expr_post_def, wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand p.ptr_operand s' = SOME w` by
    (irule eval_operand_frame >> goal_assum (drule_at Any) >>
     gvs[wb_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (irule vv_at_ptr_vv_memory_frame >> metis_tac[]) >>
  irule ptr_buf_ok_frame >>
  qexistsl_tac [`G`, `s`] >> simp[] >>
  gvs[ghost_kept_def] >> metis_tac[]
QED

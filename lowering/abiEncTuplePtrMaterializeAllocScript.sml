(* Physical source allocation: unlike the IfExp wrapper this does not identify
   the post representation with the expression annotation. *)
Theory abiEncTuplePtrMaterializeAlloc
Ancestors
  abiEncodeMaterialize bodyPtrIfExpAllocSource bodyPtrIfExpAllocResources
  bodyPtrIfExpAllocOrdered bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocStep
  bodyPtrIfExpAllocSeparation bodyPtrDefs exprSimVVFrame loweringPosts
  compileEnv exprLoweringProps ptrDiscipline venomState venomInst
  loweringHalt finite_map exprLowering context allocationPtr
  bodyPtrEnvBuiltinsScalar

Theorem materialize_alloc_physical_vv_post:
  vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  compile_alloc_buffer n sm = (buf,sn) /\ fn_has_code sm sn fn /\
  buf.buf_operand = Var out /\ n < dimword (:256) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  vv_post ctx fn ce cx e es sa sn s0 ee raw vv u
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee s` by gvs[vv_post_def] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (irule alloca_step_operand_preserved >> simp[] >> rpt strip_tac >> metis_tac[]) >>
  drule_all alloca_step_contracts >> strip_tac >>
  irule materialize_vv_post_alloc_storage_frame >>
  simp[] >> qexistsl [`s`, `sm`] >> simp[]
QED

Theorem materialize_alloc_physical_source_frame:
  !D d ctx fn PG G0 tn0 G tn ce cx e es sa sm s0 ee raw vv s n buf sn.
    vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv d ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
    local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sm = (buf,sn) /\ fn_has_code sm sn fn /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\ fn_inst_ids_distinct fn /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
        ptr_buf_ok ce e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok ce e p.ptr_operand G s) ==>
    ?out G1 tn1 t.
      buf.buf_operand = Var out /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      ptr_covers G1 tn1 out t n /\ ghost_inv d ce cx ee G1 tn1 t /\
      ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
      vv_post ctx fn ce cx e es sa sn s0 ee raw vv t /\
      ptr_vv_ok cx (post_value_type ce e) raw vv ee G1 tn1 t /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e op G1 t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p.ptr_operand G1 t) /\
      ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
      t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      lookup_var out t = SOME (n2w (buffer_allocation_base s sm.cs_next_id)) /\
      buffer_allocation_base s sm.cs_next_id + n < dimword (:256) /\
      MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (buffer_allocation_base s sm.cs_next_id,n)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx fn ce cx ee s` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `!x. vv_operand vv = Var x ==> x <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> metis_tac[]) >>
  drule_all materialize_alloc_physical_vv_post >> strip_tac >>
  `vv_at ce cx (post_value_type ce e) sa sm ee raw vv s` by gvs[vv_post_def] >>
  drule_all alloca_step_source_vv >> disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_ghost_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  `lookup_var out u = SOME (n2w (buffer_allocation_base s sm.cs_next_id))` by
    (drule_all ifexp_alloca_step_base >> simp[]) >>
  `buffer_allocation_base s sm.cs_next_id + n < dimword (:256)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
     drule_all ifexp_alloca_base_bound >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  `FLOOKUP u.vs_allocas sm.cs_next_id = SOME (buffer_allocation_base s sm.cs_next_id,n)` by
    (drule_all ifexp_alloca_step_site >> simp[]) >>
  qexistsl [`out`, `G1`, `tn1`, `t`] >> simp[lookup_var_def] >>
  conj_tac >- (rpt strip_tac >> irule alloca_step_source_buffer >>
              gvs[vv_operand_def] >> qexists `s` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule alloca_step_source_buffer >>
              gvs[vv_operand_def] >> qexists `s` >> simp[]) >>
  drule_all alloca_step_contracts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >> gvs[lookup_var_def]
QED

Theorem materialize_alloc_physical_ordered_frame:
  !D d ctx fn PG G0 tn0 G tn ce cx e es sa sm s0 ee raw vv s n buf sn.
    vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv d ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
    local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    compile_alloc_buffer n sm = (buf,sn) /\ fn_has_code sm sn fn /\
    n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\ fn_inst_ids_distinct fn /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
        ptr_buf_ok ce e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok ce e p.ptr_operand G s) ==>
    ?out G1 tn1 t.
      buf.buf_operand = Var out /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
      ptr_covers G1 tn1 out t n /\ ghost_inv d ce cx ee G1 tn1 t /\
      ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
      vv_post ctx fn ce cx e es sa sn s0 ee raw vv t /\
      ptr_vv_ok cx (post_value_type ce e) raw vv ee G1 tn1 t /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e op G1 t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p.ptr_operand G1 t) /\
      ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
      t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      lookup_var out t = SOME (n2w (buffer_allocation_base s sm.cs_next_id)) /\
      buffer_allocation_base s sm.cs_next_id + n < dimword (:256) /\
      (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
        off+sz <= buffer_allocation_base s sm.cs_next_id \/
        buffer_allocation_base s sm.cs_next_id+n <= off) /\
      (!name p sz. local_region ce es.scopes s0 name p sz ==>
        p+sz <= buffer_allocation_base s sm.cs_next_id \/
        buffer_allocation_base s sm.cs_next_id+n <= p) /\
      MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (buffer_allocation_base s sm.cs_next_id,n) /\
      sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sn.cs_next_id /\
      not_local_ptr ce ee.scopes out
Proof
  rpt strip_tac >> drule_all materialize_alloc_physical_source_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `stmt_state_rel ctx fn ce cx ee s` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[] >>
  `not_local_ptr ce ee.scopes out` by
    (drule_all compile_alloc_buffer_frame_separation >> simp[]) >>
  `n < dimword (:256)` by decide_tac >>
  `sm.cs_next_id < sn.cs_next_id` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  qexistsl [`G1`, `tn1`, `t`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> drule_all ifexp_alloca_original_site_separate >> simp[]) >>
  rpt strip_tac >> drule_all ifexp_alloca_original_local_separate >> simp[]
QED

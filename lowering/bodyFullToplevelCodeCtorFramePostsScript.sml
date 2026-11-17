(* Frame-only terminal posts at the constructor copy's fixed endpoint. *)
Theory bodyFullToplevelCodeCtorFramePosts
Ancestors
  bodyFullToplevelCodeCtorPosts bodyFullToplevelCodeWitnessPosts
  bodyFullToplevelCodeNormalize bodyFullToplevelCodePosts
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocation exprPtrUnwrapCodeCopyShape
  exprLoweringProps exprSimCopy exprSimStorageCopy bufferAllocationExecution immutableCopyWordsPtr
  loweringPosts bodyPtrDefs loweringStateRelDefs ptrDiscipline
  venomState venomInst venomMemDefs allocaHistory words arithmetic finite_map list

Theorem toplevel_code_ctor_frame_posts:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv0,sm0) /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee
    raw (LocatedValue t p) s /\ p.ptr_location = LocCode /\
  ghost_inv_at D lo ret cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer nb sm = (buf,mid) /\
  compile_imm_copy_to_memory T imm src buf.buf_operand n 0 mid = ((),sc) /\
  fn_has_code sm mid func /\ fn_has_code mid sc func /\
  fn_inst_ids_distinct func /\ nb < dimword(:256) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  buf.buf_operand = Var root /\
  u = update_var root (n2w (buffer_allocation_base s sm.cs_next_id))
    (buffer_allocation_fields s sm.cs_next_id nb) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := SUC s.vs_inst_idx /\
  Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword(:256) /\
  copy_runtime_frame mid a sc z /\ z.vs_current_bb = sc.cs_current_bb /\
  (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x /\
    op_taint tf (Var x) = op_taint tm (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  allocas_from lo z ==>
  ghost_inv_at D lo ret cenv cx ee Gf tf (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
  (!x. not_fresh_at sm x ==>
    lookup_var x (z with vs_inst_idx := LENGTH sc.cs_current_insts) = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  wb_frame cenv ee ee sm s (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
  ghost_kept_at lo cenv es sa Gi ti s0 Gf tf /\
  ghost_kept_at lo cenv ee sm G tn s Gf tf
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all toplevel_code_runtime_witness_allocation >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sc)` by
    metis_tac[immutable_copy_nonterminators] >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     drule_all toplevel_code_runtime_witness_old >> simp[NoAsms]) >>
  pop_assum (mk_asm "old_sm") >> asm "old_sm" assume_tac >>
  drule_all toplevel_code_runtime_history >> strip_tac >>
  `s.vs_alloca_next <= z.vs_alloca_next` by fs[] >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by (fs[not_fresh_at_def] >> decide_tac) >>
     metis_tac[]) >>
  drule_all toplevel_code_ctor_ghost >> strip_tac >>
  suspend "retained"
QED

Resume toplevel_code_ctor_frame_posts[retained]:
  `!j. j < buffer_allocation_base s sm.cs_next_id \/
    buffer_allocation_base s sm.cs_next_id+nb <= j ==>
    (j IN tf.t_mem <=> j IN tn.t_mem)` by
    (`w2n d = buffer_allocation_base s sm.cs_next_id` by simp[] >> metis_tac[]) >>
  `!off len. off+len <= buffer_allocation_base s sm.cs_next_id \/
    buffer_allocation_base s sm.cs_next_id+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (`w2n d = buffer_allocation_base s sm.cs_next_id` by simp[] >> metis_tac[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  drule_all toplevel_code_runtime_retained >> strip_tac >>
  `vv_post H ctx func cenv cx (TopLevelName ann nsid) ee sm sm s ee
    raw (LocatedValue t p) s` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, vv_at_def, vv_own_def, locals_kept_def]) >>
  `ghost_kept_at lo cenv ee sm G tn s G tn` by simp[ghost_kept_at_def] >>
  `ghost_kept_at lo cenv ee sm G tn s Gf tf` by
    (irule toplevel_code_runtime_retained >>
     qpat_assum `vv_post _ _ _ _ _ _ ee sm sm s ee _ _ s` (irule_at Any) >>
     qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
     qexistsl [`tn`, `G`] >> simp[] >> rpt strip_tac >> simp[]) >>
  suspend "writeback"
QED

Resume toplevel_code_ctor_frame_posts[writeback]:
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP z.vs_allocas aid = SOME entry` by
    (`z.vs_allocas = u.vs_allocas` by
       (qpat_assum `copy_runtime_frame _ _ _ _` mp_tac >>
        qpat_assum `a = u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[copy_runtime_frame_def, copy_static_def, venom_state_component_equality]) >>
     qpat_assum `u = update_var _ _ _` mp_tac >>
     qpat_assum `z.vs_allocas = u.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[update_var_def, buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = sm.cs_next_id` >> gvs[]) >>
  `wb_frame cenv ee ee sm s z` by
    (irule toplevel_code_runtime_wb_frame >>
     qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt strip_tac >> simp[]) >>
  suspend "normalize"
QED

Resume toplevel_code_ctor_frame_posts[normalize]:
  conj_tac
  >- (qpat_assum `ghost_inv_at D lo ret cenv cx ee Gf tf z` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `ret`
      >- (rw[ghost_inv_at_def, lookup_var_def, local_region_def,
              ptr_covers_def, stor_taint_ok_at_def, allocas_from_def,
              return_buf_ptr_def] >> metis_tac[]) >>
      PairCases_on `x` >>
      rw[ghost_inv_at_def, lookup_var_def, local_region_def,
           ptr_covers_def, stor_taint_ok_at_def, allocas_from_def,
           return_buf_ptr_def] >> metis_tac[]) >>
  `wb_frame cenv ee ee sm s (z with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qpat_assum `wb_frame cenv ee ee sm s z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wb_frame_def, lookup_var_def, local_region_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  asm "old_sm" (qspec_then `x` mp_tac) >>
  qpat_assum `not_fresh_at sm x` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[lookup_var_def] >> metis_tac[]
QED

Finalise toplevel_code_ctor_frame_posts

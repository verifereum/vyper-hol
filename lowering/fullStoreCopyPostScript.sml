(* Runtime transport for a storage-copy endpoint. *)
Theory fullStoreCopyPost
Ancestors
  fullStoreCopyTaint exprSimProps stmtSimStoreCopy bodyMemoryDefs
  bodyPtrDefs localPtrsProps loweringStateRelDefs loweringPosts exprLoweringProps
  venomState venomMemDefs ptrDiscipline fragGasOriginPtr fragGasOrigin fragGasMode
  fragGasPathFrameMem bodyMemAggregatePath allocaHistory
Libs
  pairLib

Theorem store_copy_normalize_state_post:
  stmt_state_rel H ctx func cenv cx es (store_copy_normalize s u) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx es u
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es
    ((store_copy_normalize s u) with vs_vars := u.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >>
     rpt strip_tac >>
     fs[local_ptrs_reserved_def, store_copy_normalize_def, lookup_var_def] >>
     metis_tac[]) >>
  pop_assum mp_tac >>
  simp[store_copy_normalize_def, stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def,
       storage_rel_def, transient_rel_def, immutables_rel_def, logs_rel_def,
       call_ctx_rel_def, contract_storage_def, contract_transient_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_room_def, pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, fmp_room_def, accounts_rel_def] >>
  strip_tac >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem store_copy_joint_frame_post_at:
  ghost_inv_at D lo d cenv cx es G tn s /\
  stor_taint_ok_at D tf u /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  ef.scopes = es.scopes /\ u.vs_memory = s.vs_memory /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm ==>
  ghost_inv_at D lo d cenv cx ef Gf tf u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gf tf p u sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[])
  >- metis_tac[]
QED

Theorem store_copy_joint_frame_post:
  ghost_inv_at D lo d cenv cx es G tn s /\
  dead_lo_ok H D lo cenv cx /\ stor_taint_ok H cx tf u /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  ef.scopes = es.scopes /\ u.vs_memory = s.vs_memory /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm ==>
  ghost_inv_at D lo d cenv cx ef Gf tf u
Proof
  strip_tac >>
  `stor_taint_ok_at D tf u` by
    fs[stor_taint_ok_at_def, stor_taint_ok_def, dead_lo_ok_def] >>
  irule store_copy_joint_frame_post_at >> simp[] >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[]
QED

Theorem store_copy_path_history:
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,Gf,tf) ==>
  alloca_history func u
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >> strip_tac >>
  irule gas_path_mem_zero_history >> simp[] >>
  metis_tac[aggregate_mem_path_alloca_inv]
QED

(* Compose the RHS's old-resource frame with a nonallocating store frame. *)
Theorem store_copy_kept_resources_post:
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d cenv sm s /\ u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_allocas = s.vs_allocas /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  (!x. not_fresh_at sm x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) ==>
  return_buf_frame d cenv sb u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\
       op_taint tf (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  conj_tac
  >- (irule return_buf_frame_frame >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> metis_tac[]
QED

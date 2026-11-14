(* Runtime transport for a storage-copy endpoint. *)
Theory fullStoreCopyPost
Ancestors
  fullStoreCopyTaint exprSimProps stmtSimStoreCopy bodyMemoryDefs
  bodyPtrDefs localPtrsProps loweringStateRelDefs loweringPosts exprLoweringProps
  venomState venomMemDefs ptrDiscipline
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
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gf tf p u sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_def, stor_taint_ok_at_def, stor_taint_ok_def,
     dead_lo_ok_def, allocas_from_def] >>
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

(* Source and VM resource transport for the guarded internal entry. *)
Theory bodyIntCallNrLockResources
Ancestors
  bodyIntCallActualJointInit bodyIntCallNonreentrantLock
  vyperTypeEvalStoragePreservation vyperTypeStoragePreservation
  exprSimHypsDefs nonreentrantEquiv vyperInterpreter vyperState vyperTypeInvariants
  exprSimIfExpWidenedEntry exprLoweringProps loweringStateRelDefs
  intCallFrame venomExecProps venomState localPtrsProps exprSimProps loweringPosts
Libs
  monadsyntax

Theorem lock_if_nr_success_shape:
  lock_if_nr cx nr view es = (INL (),locked) ==>
  locked = es \/
  ?slot. cx.nonreentrant_slot = SOME slot /\
    acquire_nonreentrant_lock cx.txn.target slot (view \/ cx.txn.is_static) es =
      (INL (),locked)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  simp[ignore_bind_def, bind_def, check_not_static_def,
       check_def, assert_def, return_def, raise_def,
       acquire_nonreentrant_lock_execution] >>
  rpt IF_CASES_TAC >> gvs[assert_def, return_def, raise_def] >> metis_tac[]
QED

Theorem lock_if_nr_source_frame:
  lock_if_nr cx nr view es = (INL (),locked) ==>
  locked = es with tStorage := locked.tStorage
Proof
  strip_tac >> drule lock_if_nr_success_shape >> strip_tac
  >- simp[] >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  simp[acquire_nonreentrant_lock_execution] >>
  rpt IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[]
QED

Theorem expr_sim_inv_after_lock:
  expr_sim_inv root cx env es /\
  lock_if_nr cx nr view es = (INL (),locked) ==>
  expr_sim_inv root cx env locked
Proof
  strip_tac >> drule lock_if_nr_success_shape >> strip_tac >- simp[] >>
  `contract_storage_well_formed cx locked` by
    (fs[expr_sim_inv_def] >>
     drule_all acquire_nonreentrant_lock_preserves_contract_storage_well_formed >>
     simp[]) >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  simp[acquire_nonreentrant_lock_execution] >>
  rpt IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def,
     oracle_storage_ok_payload] >> rpt conj_tac >> metis_tac[]
QED

(* Control-dependent resources (FMP and constructor labels) are deliberately
   supplied by the entry execution, not inferred from operand preservation. *)
Theorem stmt_state_rel_after_lock:
  stmt_state_rel ctx func root cx es v /\
  local_ptrs_reserved root before /\
  lock_if_nr cx nr view es = (INL (),locked) /\
  state_rel func root cx locked u /\
  u.vs_allocas = v.vs_allocas /\ u.vs_alloca_next = v.vs_alloca_next /\
  (!op w. eval_operand op v = SOME w ==> eval_operand op u = SOME w) /\
  fmp_room ctx func u /\ immutable_base_zero root u ==>
  stmt_state_rel ctx func root cx locked u
Proof
  strip_tac >>
  `locked.scopes = es.scopes /\ locked.immutables = es.immutables` by
    (drule lock_if_nr_source_frame >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!n b sz. local_region root locked.scopes u n b sz ==>
             local_region root es.scopes v n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`before`, `locked.scopes`, `u`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def]) >>
  `immutable_alloca_sep func root cx locked u` by
    (irule immutable_alloca_sep_fields >>
     qexistsl [`v`, `es`] >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def] >>
  conj_tac >- (irule alloca_inv_fields >> qexists `v` >> simp[]) >>
  conj_tac >- (irule alloca_room_fields >> qexists `v` >> simp[]) >>
  metis_tac[]
QED

Theorem internal_entry_root_joint_after_lock:
  supported_program tops /\ cxf.stk = owner::ancestors /\
  call_stack_follows (call_edge_rel edges) cxf.stk /\
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cxf /\
  evaluate_type (get_tenv cxf) ret = SOME rtv /\
  root.ce_return_pc = SOME (PtrVar rpc 0) /\ cenv_module_pins tops root /\
  root.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields root.ce_struct_fields name)) ret /\
  (has_rb <=> root.ce_returns_count = 0 /\ ret <> NoneT) /\
  (?x. rpc = Var x /\ not_fresh_at st x /\ lookup_var x v = SOME pc) /\
  (!op sz. root.ce_return_buf = SOME (PtrVar op sz) ==>
    ?x w. op = Var x /\ not_fresh_at st x /\ lookup_var x v = SOME w) /\
  (!op. root.ce_imm_alloca = SOME op ==>
    ?x w. op = Var x /\ not_fresh_at st x /\ lookup_var x v = SOME w) /\
  (!a k. P a k ==> a + k <= lo) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  (has_rb ==> cap = type_memory_size rtv /\ w2n bw + cap <= lo /\
    (!b z. staged b z ==> regions_disjoint (w2n bw) cap b z) /\
    (!a k. P a k ==> regions_disjoint a k (w2n bw) cap)) /\
  stmt_state_rel ctx callee root cxf es v /\ expr_sim_inv root cxf env es /\
  ce_locals_declared root env /\ locals_alloc_ok root env /\
  local_ptrs_reserved root st /\ allocas_above lo v /\
  (!a k. P a k ==> mem_bytes_at a k v.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!n p k. local_region root es.scopes v n p k ==>
    lo <= p \/ ?b z. staged b z /\ b <= p /\ p + k <= b + z) /\
  return_buf_frame (if has_rb then SOME (bw,cap) else NONE) root st v /\
  (has_rb /\ root.ce_is_ctor ==> !nm tv iv io.
    FLOOKUP root.ce_module_vars (root.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cxf.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables root.ce_module imms) nm = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n bw) cap) /\
  lock_if_nr cxf nr view es = (INL (),locked) /\
  state_rel callee root cxf locked u /\ fresh_vars_wrt st u /\
  u.vs_memory = v.vs_memory /\ u.vs_allocas = v.vs_allocas /\
  u.vs_alloca_next = v.vs_alloca_next /\
  (!op w. eval_operand op v = SOME w ==> eval_operand op u = SOME w) /\
  fmp_room ctx callee u /\ immutable_base_zero root u ==>
  ?fp. intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = cxf /\ fp.jc_owner = owner /\ fp.jc_ancestors = ancestors /\
    fp.jc_edges = edges /\ fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = lo /\ fp.jc_morig = origin /\ fp.jc_oorig = u /\
    fp.jc_root_ce = root /\ fp.jc_rpc = rpc /\ fp.jc_pc = pc /\
    fp.jc_rb = (if has_rb then SOME (bw,cap) else NONE) /\
    fp.jc_prot = P /\ fp.jc_staged = staged /\
    fp.jc_reserved = (\op. op = rpc \/
      (?sz. root.ce_return_buf = SOME (PtrVar op sz)) \/
      root.ce_imm_alloca = SOME op) /\
    intcall_joint_res fp root env locked st
      (u with vs_inst_idx := LENGTH st.cs_current_insts)
Proof
  strip_tac >>
  `locked.scopes = es.scopes /\ locked.immutables = es.immutables` by
    (drule lock_if_nr_source_frame >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!x w. lookup_var x v = SOME w ==> lookup_var x u = SOME w` by
    (qx_gen_tac `vn` >> qx_gen_tac `wv` >> strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var vn` mp_tac) >>
     simp[eval_operand_def]) >>
  `stmt_state_rel ctx callee root cxf locked u` by
    (irule stmt_state_rel_after_lock >> simp[] >>
     conj_tac >- (qexists `st` >> simp[]) >>
     qexistsl [`es`, `nr`, `v`, `view`] >> fs[lock_if_nr_def]) >>
  `expr_sim_inv root cxf env locked` by metis_tac[expr_sim_inv_after_lock] >>
  `!n p k. local_region root locked.scopes u n p k ==>
             local_region root es.scopes v n p k` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists `callee` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`st`, `locked.scopes`, `u`] >> simp[]) >>
  irule internal_entry_root_joint_exists >>
  fs[allocas_above_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (strip_tac >> `has_rb` by metis_tac[] >> gvs[])
  >- gvs[]
  >> IF_CASES_TAC >> gvs[return_buf_frame_def]
QED

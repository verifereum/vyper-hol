(* Semantic reconstruction after a constructor immutable write. *)
Theory immutableAssignState
Ancestors
  exprSimPopNestedImmutableDeploy localPtrsProps exprLoweringProps
  loweringStateRelDefs loweringSlice valueEncodingProps vyperState venomState finite_map alist

(* The absent-address case is a first write, not a read of an old value. *)
Theorem immutable_assign_ctor_relation[local]:
  immutables_rel ce addr src T es s /\
  imms = (case ALOOKUP es.immutables addr of NONE => [] | SOME m => m) /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  es'.immutables =
    (addr,set_source_immutables src
      (get_source_immutables src imms |+ (id,(tv,v))) imms) ::
    ADELKEY addr es.immutables /\
  immutable_value_admissible tv v /\ val_in_memory tv v off t.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) t.vs_memory) /\
  (!name tv0 v0 off0. name <> id /\
    FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off0) /\
    FLOOKUP (get_source_immutables src imms) name = SOME (tv0,v0) ==>
    mem_bytes_at off0 (type_memory_size tv0) t.vs_memory =
    mem_bytes_at off0 (type_memory_size tv0) s.vs_memory) ==>
  immutables_rel ce addr src T es' t
Proof
  strip_tac >> Cases_on `ALOOKUP es.immutables addr` >> gvs[]
  >- (gvs[immutables_rel_def, get_source_immutables_def,
          set_source_immutables_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[])
  >> irule immutables_rel_ctor_update >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

(* Declaration separation covers the destination even on its first write. *)
Theorem immutable_assign_alloca_sep[local]:
  immutable_alloca_sep func ce cx es t /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m) /\
  es' = es with immutables :=
    (cx.txn.target,set_source_immutables ce.ce_module
      (get_source_immutables ce.ce_module imms |+ (id,(tv,v))) imms) ::
    ADELKEY cx.txn.target es.immutables ==>
  immutable_alloca_sep func ce cx es' t
Proof
  strip_tac >> gvs[] >>
  fs[immutable_alloca_sep_def] >>
  strip_tac >> map_every qx_gen_tac [`name`, `tv0`, `v0`, `off0`] >>
  Cases_on `name = id`
  >- (gvs[get_source_immutables_def, set_source_immutables_def, FLOOKUP_UPDATE] >>
      strip_tac >>
      qpat_x_assum `immutable_decl_sep _ _ _ _ _ _` mp_tac >>
      rewrite_tac[immutable_decl_sep_alt] >> simp[] >>
      disch_then (qspecl_then [`id`, `ty`, `tv`, `off0`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def, set_source_immutables_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* Allocation growth and ISTORE bookkeeping are deliberately not frozen. *)
Theorem immutable_assign_stmt_state_rel:
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m) /\
  es' = es with immutables :=
    (cx.txn.target,set_source_immutables ce.ce_module
      (get_source_immutables ce.ce_module imms |+ (id,(tv,v))) imms) ::
    ADELKEY cx.txn.target es.immutables /\
  immutable_value_admissible tv v /\ val_in_memory tv v off t.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) t.vs_memory) /\
  (!name tv0 v0 off0. name <> id /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off0) /\
    FLOOKUP (get_source_immutables ce.ce_module imms) name = SOME (tv0,v0) ==>
    mem_bytes_at off0 (type_memory_size tv0) t.vs_memory =
    mem_bytes_at off0 (type_memory_size tv0) s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s) /\
  (!p. ce.ce_imm_alloca = SOME (Var p) ==> lookup_var p t = lookup_var p s) /\
  (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP t.vs_allocas aid = SOME r) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    FLOOKUP s.vs_allocas inst.inst_id = NONE ==> sz = w2n n) /\
  alloca_inv t /\ alloca_room ctx func t /\ fmp_room ctx func t /\
  t.vs_labels = s.vs_labels /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions ==>
  stmt_state_rel ctx func ce cx es' t
Proof
  strip_tac >>
  `local_ptrs_rel func ce es.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func ce es.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists `s` >> simp[] >>
     rpt conj_tac >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_x_assum `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==> _` drule_all >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `!name b sz. local_region ce es.scopes t name b sz ==>
     local_region ce es.scopes s name b sz` by
    (rpt strip_tac >> gvs[local_region_def] >> metis_tac[]) >>
  `immutable_alloca_sep func ce cx es t` by
    (irule immutable_alloca_sep_frame >> qexistsl [`s`, `es`] >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >> disj1_tac >>
         qpat_x_assum `!name b sz. local_region ce es.scopes t name b sz ==> _` drule_all >>
         strip_tac >> goal_assum (drule_at Any)) 
     >- gvs[stmt_state_rel_def] >> first_assum ACCEPT_TAC) >>
  `immutable_alloca_sep func ce cx es' t` by
    (irule immutable_assign_alloca_sep >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `immutable_base_zero ce t` by
    (irule immutable_base_zero_frame >> qexists `s` >>
     gvs[stmt_state_rel_def]) >>
  `immutables_rel ce cx.txn.target ce.ce_module T es' t` by
    (`immutables_rel ce cx.txn.target ce.ce_module T es s` by
       gvs[stmt_state_rel_def, state_rel_def] >>
     drule immutable_assign_ctor_relation >> disch_then irule >>
     goal_assum (drule_at Any) >> simp[] >> qexistsl [`tv`, `v`] >> simp[]) >>
  `state_rel func ce cx es' t` by
    (gvs[stmt_state_rel_def, state_rel_def,
         storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
         contract_storage_def, contract_transient_def]) >>
  simp[stmt_state_rel_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> gvs[]
  >- metis_tac[] >>
  qpat_x_assum `!aid r. _` drule >> strip_tac >> gvs[] >>
  gvs[stmt_state_rel_def] >> metis_tac[]
QED

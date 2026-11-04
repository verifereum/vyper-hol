Theory abiMaterializeFrameProbe
Ancestors
  abiEncodeMaterializeExec exprSim exprLoweringProps accountsRelProps compileEnv
  vfmState venomState venomMemDefs vyperState words arithmetic combin

(* A zero-length declared array ignores its sole element's slot, whereas
   a captured scalar at that slot still demands agreement. This is only
   the storage-interface probe, not a full materialization counterexample. *)
Theorem frame_probe_dead_element:
  lookup_storage 0w st = 0w ==>
  !b. b < 32 ==>
    dead_bytes st 0 (ArrayTV (BaseTV BoolT) (Dynamic 1)) 1 b
Proof
  simp[dead_bytes_def, vyperValueTheory.type_slot_size_def]
QED

Theorem frame_probe_declared_agreement:
  lookup_storage 0w st = 0w ==>
  storage_agree (dead_bytes st 0 (ArrayTV (BaseTV BoolT) (Dynamic 1)))
    st (update_storage 1w 1w st)
Proof
  strip_tac >> simp[storage_agree_def] >> rpt strip_tac >>
  Cases_on `k = 1w` >-
    (gvs[] >> metis_tac[frame_probe_dead_element]) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

Theorem frame_probe_captured_disagreement:
  lookup_storage 1w st = 0w ==>
  ~storage_range_agree st (update_storage 1w 1w st) 1w (BaseTV BoolT)
Proof
  strip_tac >> strip_tac >> drule storage_range_agree_head >>
  simp[vyperValueTheory.type_slot_size_def, lookup_storage_def, update_storage_def,
       APPLY_UPDATE_THM] >> gvs[lookup_storage_def]
QED

Theorem frame_probe_zero_storage:
  lookup_storage 0w (K 0w) = 0w /\ lookup_storage 1w (K 0w) = 0w
Proof
  EVAL_TAC
QED

Theorem frame_probe_range_transport_fails:
  storage_agree (dead_bytes (K 0w) 0 (ArrayTV (BaseTV BoolT) (Dynamic 1)))
    (K 0w) (update_storage 1w 1w (K 0w)) /\
  ~storage_range_agree (K 0w) (update_storage 1w 1w (K 0w))
    1w (BaseTV BoolT)
Proof
  metis_tac[frame_probe_zero_storage, frame_probe_declared_agreement,
    frame_probe_captured_disagreement]
QED

Definition frame_probe_context_def:
  frame_probe_context vis cx = cx with <|
    sources := [(cx.txn.target, [(NONE,
      [VariableDecl vis Storage "a" (ArrayT (BaseT BoolT) (Dynamic 1)) NONE])])];
    layouts := [(cx.txn.target, ([((NONE,"a"),0)],[]))] |>
End

Theorem frame_probe_declared_region:
  declared_storage_region (frame_probe_context vis cx) mid n subs = SOME (tr,w,tv) <=>
  mid = NONE /\ n = "a" /\ subs = [] /\ tr = F /\ w = 0w /\
    tv = ArrayTV (BaseTV BoolT) (Dynamic 1)
Proof
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def,
       frame_probe_context_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def,
       vyperContextTheory.type_env_all_modules_def,
       vyperContextTheory.type_env_for_module_def,
       vyperStateTheory.find_var_decl_by_name_def,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def,
       wordsTheory.dimword_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem frame_probe_actual_dead_slot:
  !b. b < 32 ==>
  storage_dead (frame_probe_context vis cx) F (K 0w) 1 b
Proof
  rpt strip_tac >> simp[storage_dead_def] >>
  qexistsl [`NONE`, `"a"`, `[]`, `0w`,
    `ArrayTV (BaseTV BoolT) (Dynamic 1)`] >>
  simp[frame_probe_declared_region, vyperValueTheory.type_slot_size_def,
       wordsTheory.dimword_def, frame_probe_dead_element,
       frame_probe_zero_storage]
QED

Theorem frame_probe_actual_storage_agreement:
  storage_agree (storage_dead (frame_probe_context vis cx) F (K 0w))
    (K 0w) (update_storage 1w 1w (K 0w)) /\
  ~storage_range_agree (K 0w) (update_storage 1w 1w (K 0w))
    1w (BaseTV BoolT)
Proof
  conj_tac
  >- (simp[storage_agree_def] >> rpt strip_tac >>
      Cases_on `k = 1w`
      >- (gvs[] >> metis_tac[frame_probe_actual_dead_slot]) >>
      simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]) >>
  metis_tac[frame_probe_range_transport_fails]
QED

Theorem frame_probe_accounts_update:
  accounts_rel (frame_probe_context vis cx) es s /\
  (es.accounts (frame_probe_context vis cx).txn.target).storage = K 0w /\
  s.vs_call_ctx.cc_address = (frame_probe_context vis cx).txn.target ==>
  accounts_rel (frame_probe_context vis cx) es (sstore 1w 1w s)
Proof
  simp[accounts_rel_def, accounts_agree_def, sstore_def,
       APPLY_UPDATE_THM] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `_ with storage := _ = _` (mp_tac o Q.AP_TERM `\a. a with storage := update_storage 1w 1w (lookup_account (frame_probe_context vis cx).txn.target s.vs_accounts).storage`) >>
      simp[lookup_account_def]) >>
  simp[storage_agree_def] >> rpt strip_tac >>
  Cases_on `k = 1w`
  >- (gvs[] >> metis_tac[frame_probe_actual_dead_slot]) >>
  simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  gvs[storage_agree_def, lookup_storage_def, lookup_account_def] >> metis_tac[]
QED

Theorem frame_probe_stmt_update:
  stmt_state_rel ctx func ce (frame_probe_context vis cx) es s /\
  (es.accounts (frame_probe_context vis cx).txn.target).storage = K 0w /\
  s.vs_call_ctx.cc_address = (frame_probe_context vis cx).txn.target ==>
  stmt_state_rel ctx func ce (frame_probe_context vis cx) es (sstore 1w 1w s)
Proof
  strip_tac >>
  `accounts_rel (frame_probe_context vis cx) es (sstore 1w 1w s)` by
    (irule frame_probe_accounts_update >> gvs[stmt_state_rel_def, state_rel_def]) >>
  `storage_rel (frame_probe_context vis cx) (frame_probe_context vis cx).txn.target es (sstore 1w 1w s)` by
    (drule accounts_rel_storage_transient >> simp[sstore_def]) >>
  gvs[stmt_state_rel_def, state_rel_def, sstore_def,
      local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def,
      storage_rel_def, contract_storage_def, transient_rel_def,
      contract_transient_def, immutables_rel_def, logs_rel_def,
      immutable_base_zero_def, alloca_inv_def, allocas_non_overlapping_def,
      alloca_next_valid_def, alloca_room_def, fmp_room_def,
      pending_alloca_size_def, immutable_alloca_sep_def,
      lookup_account_def, APPLY_UPDATE_THM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Definition frame_probe_vv_def:
  frame_probe_vv = LocatedValue (BaseT BoolT)
    <|ptr_operand := Lit 1w; ptr_location := LocStorage; ptr_buf := NONE|>
End

Definition frame_probe_seed_def:
  frame_probe_seed ctx func ce vis cx e es sa tv s <=>
    vv_post ctx func ce (frame_probe_context vis cx) e es sa sa s es tv
      frame_probe_vv s /\
    local_ptrs_reserved ce sa /\ expr_type e = BaseT BoolT /\
    (es.accounts (frame_probe_context vis cx).txn.target).storage = K 0w /\
    s.vs_call_ctx.cc_address = (frame_probe_context vis cx).txn.target
End

Theorem frame_probe_output_fails:
  frame_probe_seed ctx func ce vis cx e es sa tv s ==>
  ~vv_post ctx func ce (frame_probe_context vis cx) e es sa sa s es tv
    frame_probe_vv (sstore 1w 1w s)
Proof
  simp[frame_probe_seed_def] >> strip_tac >>
  strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ (sstore _ _ _)`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  gvs[frame_probe_vv_def, vv_holds_def, storage_holds_def,
      eval_operand_def, vyperValueTheory.evaluate_type_def] >>
  drule storage_range_agree_head >>
  simp[vyperValueTheory.type_slot_size_def,
       vyperStorageBackendTheory.get_storage_def,
       contract_storage_def, sstore_def, lookup_account_def,
       lookup_storage_def, update_storage_def, APPLY_UPDATE_THM] >>
  gvs[frame_probe_context_def, vyperStateTheory.bind_def]
QED

Theorem frame_probe_conditional_countermodel:
  frame_probe_seed ctx func ce vis cx e es sa tv s ==>
  ?t.
    vv_post ctx func ce (frame_probe_context vis cx) e es sa sa s es tv frame_probe_vv s /\
    stmt_state_rel ctx func ce (frame_probe_context vis cx) es t /\
    t.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand (vv_operand frame_probe_vv) t =
      eval_operand (vv_operand frame_probe_vv) s /\
    local_ptrs_reserved ce sa /\
    sa.cs_next_var <= sa.cs_next_var /\ sa.cs_next_id <= sa.cs_next_id /\
    sa.cs_next_id <= sa.cs_next_id /\
    ~vv_post ctx func ce (frame_probe_context vis cx) e es sa sa s es tv frame_probe_vv t
Proof
  strip_tac >>
  drule frame_probe_output_fails >> strip_tac >>
  qexists_tac `sstore 1w 1w s` >>
  `stmt_state_rel ctx func ce (frame_probe_context vis cx) es (sstore 1w 1w s)` by
    (irule frame_probe_stmt_update >>
     gvs[frame_probe_seed_def, vv_post_def]) >>
  gvs[frame_probe_seed_def, sstore_def, lookup_var_def,
      frame_probe_vv_def, contextTheory.vv_operand_def, eval_operand_def]
QED

(* Seed satisfiability remains UNKNOWN. The bounded candidate left the
   incoming vv_post and local_ptrs_reserved obligations unresolved;
   frame_probe_conditional_countermodel does not assert a seed exists. *)

Theory exprPtrUnwrapStoragePost
Ancestors
  exprPtrUnwrapCopyPost exprPtrUnwrapStorageFacts exprPtrUnwrapLoopInvariant
  exprPtrUnwrapStorage ptrDiscipline bodyPtrDefs exprSimPtrProps
  abiDecodeStaticProps words pred_set exprSimMemorySource loweringPosts
  exprPtrUnwrapStorageSource slotCopyExecution vyperStorage accountsRelProps venomState arithmetic
  exprPtrUnwrapCopySemantic exprSimUnwrapProps exprSimProps

(* The copied prefix may be tainted, but only in its type's dead bytes. *)
Theorem copy_prefix_storage_dead:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G0 tn0 r /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand r = SOME w /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  w2n w + type_slot_size ty <= dimword (:256) /\
  (!j b. j < type_slot_size ty /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    b IN key_taint (if tr then tn0.t_trans else tn0.t_stor) (w+n2w j)) ==>
  !j b. j < type_slot_size ty /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    dead_bytes
      (if tr then r.vs_transient r.vs_call_ctx.cc_address
       else (r.vs_accounts r.vs_call_ctx.cc_address).storage)
      (w2n w) ty (w2n w+j) b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `w2n (w+n2w j) = w2n w+j` by
    (irule w2n_add_n2w_lt >> simp[] >> decide_tac) >>
  `b IN key_taint (if tr then tn0.t_trans else tn0.t_stor) (w+n2w j)` by
    metis_tac[] >>
  drule ptr_vv_ok_storage_taint >>
  disch_then (qspecl_then [`w`, `ty`, `w+n2w j`, `b`] mp_tac) >> simp[] >>
  Cases_on `tr` >> gvs[slot_loc_def, key_taint_def]
QED

(* The ordinary endpoint projections suffice; no copy-loop invariant is needed. *)
Theorem unwrap_storage_copied_robust:
  storage_holds cx tr t tv w es r /\
  ptr_vv_ok cx t tv (LocatedValue t' p) es G0 tn0 r /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand r = SOME w /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  (!j. j < type_slot_size ty ==>
    mem_word_at (w2n d+32*j) s.vs_memory =
      slot_copy_word (if tr then TLOAD else SLOAD) r (w+n2w j)) /\
  (!j b. j < type_slot_size ty /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    b IN key_taint (if tr then tn0.t_trans else tn0.t_stor) (w+n2w j)) ==>
  ?v. read_result cx tv es = (INL v,es) /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory ty v (w2n d) mem
Proof
  strip_tac >> drule_all storage_holds_decode >> strip_tac >>
  `w2n w + type_slot_size ty <= dimword (:256)` by
    fs[storage_range_agree_def] >>
  `!j b. j < type_slot_size ty /\ b < 32 /\ w2n d+32*j+b IN tn.t_mem ==>
    dead_bytes (if tr then r.vs_transient r.vs_call_ctx.cc_address
      else (r.vs_accounts r.vs_call_ctx.cc_address).storage)
      (w2n w) ty (w2n w+j) b` by
    (rpt strip_tac >> irule copy_prefix_storage_dead >> simp[] >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`d`, `tn`] >>
     `!j b. b+(32*j+w2n d) = w2n d+32*j+b` by
       (rpt gen_tac >> decide_tac) >>
     asm_rewrite_tac[]) >>
  qexists `v` >> simp[] >>
  rpt strip_tac >> irule storage_range_copied_robust >> simp[] >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  qexistsl [`if tr then contract_transient r else contract_storage r`,
    `get_storage cx es tr`, `w`] >>
  simp[] >> Cases_on `tr` >>
  gvs[slot_copy_word_def, sload_def, tload_def, contract_storage_def,
    contract_transient_def, vfmStateTheory.lookup_account_def]
QED

(* Semantic and robust posts use the very same copy endpoint z. *)
Theorem unwrap_storage_copy_post:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  storage_holds cx tr (expr_type e) tv w ee s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME w /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  nb < dimword (:256) /\ 32*n <= nb /\ buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sm.cs_next_id nb) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ slot_copy_runtime_frame mid d n a z /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  n = type_slot_size ty /\ type_memory_size ty <= nb /\
  eval_operand op z = SOME d /\
  (!j. j < n ==> mem_word_at (w2n d+32*j) z.vs_memory =
    slot_copy_word (if tr then TLOAD else SLOAD) s (w+n2w j)) /\
  (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tm.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j)) ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    (!mem. mem_agree_outside tm.t_mem z.vs_memory mem ==>
      val_in_memory ty v (w2n d) mem)
Proof
  strip_tac >> qpat_x_assum `n = type_slot_size ty` SUBST_ALL_TAC >>
  `?v. read_result cx tv ee = (INL v,ee) /\
    !mem. mem_agree_outside tm.t_mem z.vs_memory mem ==>
      val_in_memory ty v (w2n d) mem` by
    (irule unwrap_storage_copied_robust >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`tr`, `w`] >> asm_rewrite_tac[]) >>
  pop_assum strip_assume_tac >>
  drule_all storage_holds_value_bounds >> strip_tac >>
  drule vv_post_read_result >> strip_tac >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     asm_rewrite_tac[]) >>
  qexists `v` >> simp[] >>
  `val_in_memory ty v (w2n d) z.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `val_footprint ty v <= nb` by decide_tac >>
  irule unwrap_copy_semantic_post >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl [`buf`, `k`, `mid`, `type_slot_size ty`, `nb`, `root`] >>
  gvs[]
QED

(* Coverage of the full allocation is stronger than the value's store extent. *)
Theorem unwrap_storage_pointer_posts:
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  eval_operand (Var root) z = SOME w /\ ptr_covers G tn root z nb /\
  val_wf ty v /\ type_memory_size ty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= nb /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
    val_in_memory ty v (w2n w) mem) ==>
  ptr_val_ok cx (expr_type e) v (Var root) G tn z /\
  ptr_buf_ok cenv e (Var root) G z
Proof
  strip_tac >> `val_store_size ty v <= nb` by
    metis_tac[val_store_size_le, LESS_EQ_TRANS] >>
  gvs[ptr_covers_def, eval_operand_def] >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, eval_operand_def] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >> simp[] >> decide_tac
QED

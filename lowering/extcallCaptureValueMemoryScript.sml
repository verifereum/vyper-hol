(* Keep a captured nonword memory value through later pure operands. *)
Theory extcallCaptureValueMemory
Ancestors
  extcallCaptureFrameMemory loweringPosts valueEncodingProofs
  vyperInterpreter vyperState compileEnv accountsRelProps vyperStorageBackend
  exprSimProps loweringStateRelDefs context exprLoweringProps

Theorem extcall_captured_nonword_memory_holds_frame:
  vv_holds ce cx ty (Value v) (LocatedValue tag p) es s /\
  vv_at ce cx ty sa sb es (Value v) (LocatedValue tag p) s /\
  p.ptr_location = LocMemory /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  eval_operand p.ptr_operand t = SOME w /\
  pure_frame ce func es st s t /\ sb.cs_next_id <= st.cs_next_id /\
  alloca_inv t /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) ==>
  vv_holds ce cx ty (Value v) (LocatedValue tag p) ee t
Proof
  strip_tac >>
  `read_result cx (Value v) es = (INL v,es)` by
    simp[read_result_def,return_def] >>
  drule_all extcall_captured_memory_pure_frame >> strip_tac >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) s.vs_memory` by
    (fs[vv_at_def,vv_holds_def,read_result_def,return_def] >> metis_tac[]) >>
  `val_in_memory tv v (w2n w) t.vs_memory` by
    (irule val_in_memory_footprint_agree >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `s.vs_memory` >> simp[]) >>
  fs[vv_holds_def,read_result_def,return_def] >> metis_tac[]
QED

Theorem extcall_captured_storage_holds_refresh:
  storage_holds cx tr ty (Value v) w es s /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    storage_read_live cx tr (get_storage cx es tr) w tv) /\
  get_storage cx ee tr = get_storage cx es tr /\
  stmt_state_rel ctx func ce cx ee t ==>
  storage_holds cx tr ty (Value v) w ee t
Proof
  strip_tac >>
  qpat_x_assum `storage_holds _ _ _ _ _ _ _` mp_tac >>
  simp[storage_holds_def,read_result_def,return_def] >> strip_tac >>
  `w2n w + type_slot_size tvt <= dimword (:256)` by
    fs[storage_range_agree_def] >>
  `storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient t else contract_storage t) w tvt` by
    (irule storage_range_agree_of_live >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cx`,`tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def,state_rel_def,storage_rel_def,transient_rel_def,
         get_storage_def,vfmStateTheory.lookup_account_def]) >>
  `read_storage_slot cx tr w tvt ee = (INL v,ee)` by
    (qpat_x_assum `read_storage_slot _ _ _ _ es = _` mp_tac >>
     simp[read_storage_slot_eq] >> CASE_TAC >> simp[]) >>
  simp[storage_holds_def,read_result_def,return_def] >> metis_tac[]
QED

Theorem extcall_captured_nonword_stack_holds_frame:
  vv_holds ce cx ty (Value v) (StackValue tag op) es s /\
  vv_at ce cx ty sa sb es (Value v) (StackValue tag op) s /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ eval_operand op t = SOME w /\
  pure_frame ce func es st s t /\ sb.cs_next_id <= st.cs_next_id /\
  alloca_inv t /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) ==>
  vv_holds ce cx ty (Value v) (StackValue tag op) ee t
Proof
  strip_tac >>
  `vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr op LocMemory)) es s` by
    (fs[vv_holds_def,expr_val_rel_def,read_result_def,return_def] >>
     simp[vv_holds_def,mk_ptr_def,read_result_def,return_def] >> metis_tac[]) >>
  `vv_at ce cx ty sa sb es (Value v)
     (LocatedValue ty (mk_ptr op LocMemory)) s` by
    (fs[vv_at_def,expr_val_at_def,read_result_def,return_def] >>
     simp[vv_at_def,mk_ptr_def,read_result_def,return_def,local_place_at_def] >>
     metis_tac[]) >>
  `vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr op LocMemory)) ee t` by
    (irule extcall_captured_nonword_memory_holds_frame >>
     simp[mk_ptr_def] >>
     qexistsl_tac [`es`,`func`,`s`,`sa`,`sb`,`st`] >> fs[mk_ptr_def]) >>
  fs[vv_holds_def,mk_ptr_def,expr_val_rel_def,read_result_def,return_def] >>
  metis_tac[]
QED

(* A snapshotted word initializes one separated tuple cell. *)
Theory extcallWordStoreMemory
Ancestors
  extcallStoreCellMemory bodyDeclWordMemory exprSimBufferStore
  abiTupleProps valueEncodingProps loweringPosts compileEnv
  venomExecSemantics venomState venomMemProps exprLoweringProps emitHelper emitHelperProps

Theorem extcall_word_store_result_mem:
  emit_void MSTORE [Var p; src] sa = ((),sb) /\
  lookup_var p s = SOME d /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\
  abi_tuple_word tv v /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b + sz <= w2n d \/ w2n d + 32 <= b) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (w2n d) 32) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n d) z.vs_memory /\
    z.vs_vars = s.vs_vars /\ z.vs_allocas = s.vs_allocas /\
    z.vs_alloca_next = s.vs_alloca_next /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels /\
    (!off len. off + len <= w2n d \/ w2n d + 32 <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all annassign_word_mstore_path_mem >> strip_tac >>
  `val_in_memory tv v (w2n d)
    (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_memory` by
    metis_tac[abi_tuple_word_mstore] >>
  `!off len. off+len <= w2n d \/ w2n d+32 <= off ==>
    mem_bytes_at off len (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_memory =
      mem_bytes_at off len s.vs_memory` by
    metis_tac[mstore_mem_bytes_at_disjoint] >>
  `(mstore (w2n d) (typed_val_to_w256 tv v) s with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    simp[mstore_def,write_memory_with_expansion_def] >>
  `!x. lookup_var x (mstore (w2n d) (typed_val_to_w256 tv v) s) = lookup_var x s` by
    simp[mstore_def,write_memory_with_expansion_def,lookup_var_def] >>
  `LENGTH s.vs_memory <= LENGTH (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_memory` by
    (simp[LENGTH_mstore_eq,arithmeticTheory.MAX_DEF] >>
     decide_tac) >>
  `stmt_state_rel ctx func ce cx es
    (mstore (w2n d) (typed_val_to_w256 tv v) s)` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     qexistsl_tac [`w2n d`,`32`,`sa`] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def,emit_inst_def,comp_bind_def,comp_ignore_bind_def,
          comp_return_def,fresh_id_def,emit_def] >> rpt strip_tac >> gvs[]) >>
  `(mstore (w2n d) (typed_val_to_w256 tv v) s).vs_vars = s.vs_vars /\
   (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_allocas = s.vs_allocas /\
   (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_alloca_next = s.vs_alloca_next /\
   contract_storage (mstore (w2n d) (typed_val_to_w256 tv v) s) = contract_storage s /\
   contract_transient (mstore (w2n d) (typed_val_to_w256 tv v) s) = contract_transient s /\
   (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_data_section = s.vs_data_section /\
   (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_labels = s.vs_labels /\
   ~(mstore (w2n d) (typed_val_to_w256 tv v) s).vs_halted /\
   (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_current_bb = sb.cs_current_bb` by
    simp[mstore_def,contract_storage_def,contract_transient_def] >>
  `!q k. contract_storage (q with vs_inst_idx := k) = contract_storage q /\
         contract_transient (q with vs_inst_idx := k) = contract_transient q` by
    simp[contract_storage_def,contract_transient_def] >>
  qexists_tac `mstore (w2n d) (typed_val_to_w256 tv v) s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

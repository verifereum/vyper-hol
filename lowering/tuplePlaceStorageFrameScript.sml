Theory tuplePlaceStorageFrame
Ancestors
  placeStoreStorage placeDynStorageEmptyPath placeDynStoragePath stmtSimStoreCopy venomState

Theorem tuple_place_dyn_storage_path_frame:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  mload (w2n b) s0 = n2w n /\ n < dimword (:256) /\
  ew < dimword (:256) /\ (ew = 1 ==> ems = 32) /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      store_copy_normalize s0 t =
        (if transient then tstore else sstore) k (n2w n)
          (place_dyn_prefix (if transient then LocTransient else LocStorage)
            b k ew ems s0 n) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_memory = s0.vs_memory
Proof
  strip_tac >> drule_all place_dyn_storage_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >>
  Cases_on `transient` >>
  simp[store_copy_normalize_def, sstore_def, tstore_def, place_dyn_prefix_fields]
QED

Theorem tuple_place_dyn_storage_empty_path_frame:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  mload (w2n b) s0 = 0w /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      store_copy_normalize s0 t =
        (if transient then tstore else sstore) k 0w s0 /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_memory = s0.vs_memory
Proof
  strip_tac >> drule_all place_dyn_storage_empty_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >>
  Cases_on `transient` >>
  simp[store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem tuple_place_typed_memory_suffix_frame:
  (if type_memory_size tv <= 32 then
     ?loaded sm. emit_op MLOAD [src] sa = (loaded,sm) /\
       emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sm = ((),sb)
   else ?r. (if tr then compile_memory_to_transient else compile_memory_to_storage)
       src dst (type_memory_size tv DIV 32) sa = (r,sb)) /\
  type_memory_size tv = 32 * type_slot_size tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
      start tv (start+i) b ==>
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mload (w2n sw+32*i) s) T)` by
    (rpt strip_tac >> irule place_store_memory_live_at >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tv`, `v`] >> pure_asm_rewrite_tac[] >> simp[]) >>
  Cases_on `type_memory_size tv <= 32`
  >- suspend "load" >> suspend "loop"
QED

Resume tuple_place_typed_memory_suffix_frame[loop]:
  `type_slot_size tv < dimword (:256)` by decide_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`n` |-> `type_slot_size tv`, `result` |-> `r`]
    (SPEC_ALL place_store_memory_leaf_run)) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED

Resume tuple_place_typed_memory_suffix_frame[load]:
  `type_slot_size tv = 1` by decide_tac >>
  fs[IgnAsm `start = _`] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all place_store_load_emit_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `store_copy_normalize _ _ = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def] >>
     Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
      (n2w (start+i)) (mload (w2n sw) s) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. mload (w2n (sw:bytes32)) s`]
      (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexists_tac `v` >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at Any) >> simp[] >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >> gvs[]
QED
Finalise tuple_place_typed_memory_suffix_frame

(* Prepared-buffer fixed and bytestring copies to rooted storage places. *)
Theory assignPlaceStorageSuffixMem
Ancestors
  dynStorageCopyAgreement dynStorageState dynStorageDeclaredAgreement
  declaredStorageAgreement storageSubregionAgreement
  bodyMemAssignTopCopyPaths bodyMemAssignTopCopySem bodyMemAssignTopCopySuffix
  stmtSimAssignStorageCopy storageCopyLive valueCopyBytes
  stmtSimStoreCopy stmtLowering venomState valueEncodingProps words arithmetic
  emitHelperProps context list rich_list exprSimConcatPath freshWrites
  exprLoweringProps compileEnv

Theorem suffix_live_buffer[local]:
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n p) initial.vs_memory /\
  val_footprint tv v <= 32*n /\ n <= type_slot_size tv /\
  w2n p+32*n < dimword (:256) /\
  j < type_slot_size tv /\ byte < 32 /\
  ~dead_bytes (apply_writes k writes old) (w2n k) tv (w2n k+j) byte ==>
  EL byte (word_to_bytes (lookup_storage (n2w (w2n k+j))
    (if tr then contract_transient (store_copy_prefix LocTransient p k initial n)
     else contract_storage (store_copy_prefix LocStorage p k initial n))) T) =
  EL byte (word_to_bytes
    (lookup_storage (n2w (w2n k+j)) (apply_writes k writes old)) T)
Proof
  strip_tac >>
  `32*j < val_footprint tv v` by
    (irule storage_copy_live_footprint >>
     simp[] >> qexistsl_tac [`byte`, `w2n k`, `old`] >> simp[] >> metis_tac[ADD_COMM, w2n_lt]) >>
  `j < n /\ w2n k+j < dimword (:256) /\
   w2n k+n <= dimword (:256)` by decide_tac >>
  `w2n (n2w (w2n k+j):bytes32) = w2n k+j` by simp[w2n_n2w] >>
  simp[dyn_storage_chunk_lookup] >>
  `w2n (p+n2w j*32w) = w2n p+32*j` by
    (irule topcopy_word_address >> qexists_tac `32*n` >> simp[]) >>
  asm_rewrite_tac[] >>
  drule_all storageCopyLiveTheory.encode_value_memory_live >>
  metis_tac[mem_word_at_eq_mload, ADD_COMM]
QED

Theorem suffix_declared_agreement[local]:
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ k = root+n2w delta /\
  w2n root + type_slot_size rtv <= dimword (:256) /\
  w2n root+delta < dimword (:256) /\
  (!mid' name' keys' root' tv'.
    declared_storage_region cx mid' name' keys' = SOME (tr,root',tv') /\
    (root',tv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size tv')) /\
  storage_agree (storage_dead cx tr old) old
    (if tr then contract_transient initial else contract_storage initial) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n p) initial.vs_memory /\
  encode_value tv v = SOME writes /\
  val_footprint tv v <= 32*n /\ n <= type_slot_size tv /\
  w2n p+32*n < dimword (:256) /\
  final = (if tr then contract_transient (store_copy_prefix LocTransient p k initial n)
           else contract_storage (store_copy_prefix LocStorage p k initial n)) ==>
  storage_agree (storage_dead cx tr (apply_writes k writes old))
    (apply_writes k writes old) final
Proof
  strip_tac >>
  `delta + type_slot_size tv <= type_slot_size rtv` by
    metis_tac[vyperStoragePlaceRegionTheory.storage_subregion_bounds] >>
  `w2n k = w2n root+delta` by
    metis_tac[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
  `w2n k + type_slot_size tv <= dimword (:256)` by decide_tac >>
  irule storage_agree_subregion_effect >>
  qexistsl_tac [
    `if tr then contract_transient initial else contract_storage initial`,
    `w2n k`, `keys`, `tv`, `mid`, `name`, `old`, `root`, `rtv`] >>
  rpt conj_tac
  >- suspend "outside_mask"
  >- (rpt strip_tac >> drule storage_subregion_dead_bytes >>
      disch_then irule >> metis_tac[])
  >- (rpt strip_tac >>
      `w2n k+n <= dimword (:256)` by decide_tac >>
      `~(w2n k <= j /\ j < w2n k+n)` by decide_tac >>
      gvs[dyn_storage_chunk_lookup, w2n_n2w, LESS_MOD])
  >- (rpt strip_tac >> irule copy_encoded_outside >> metis_tac[])
  >- asm_rewrite_tac[]
  >- simp[]
  >- decide_tac
  >- asm_rewrite_tac[]
  >- asm_rewrite_tac[]
  >- asm_rewrite_tac[] >>
  simp_tac bool_ss [compileEnvTheory.storage_agree_def] >>
  rpt gen_tac >> strip_tac >> suspend "live"
QED
Resume suffix_declared_agreement[live]:
  `w2n k+(w2n k'-w2n k) = w2n k' /\
   w2n k'-w2n k < type_slot_size tv` by decide_tac >>
  qpat_x_assum `final = _` (fn th => pure_rewrite_tac[th]) >>
  sym_tac >>
  qpat_x_assum `k = root+_` kall_tac >>
  qpat_x_assum `w2n k = _` kall_tac >>
  mp_tac (Q.INST [`j` |-> `w2n (k':bytes32)-w2n (k:bytes32)`, `byte` |-> `b`]
    suffix_live_buffer) >>
  asm_rewrite_tac[n2w_w2n] >> metis_tac[]
QED
Resume suffix_declared_agreement[outside_mask]:
  rpt strip_tac >>
  `!a. a < dimword (:256) /\
       ~(w2n k <= a /\ a < w2n k+type_slot_size tv) ==>
       lookup_storage (n2w a) (apply_writes k writes old) = lookup_storage (n2w a) old` by
    (rpt strip_tac >> irule copy_encoded_outside >> metis_tac[]) >>
  drule storage_subregion_dead_bytes_outside >>
  disch_then (qspecl_then [`old`, `apply_writes k writes old`, `w2n root`, `j`, `b`] mp_tac) >>
  impl_tac
  >- (conj_tac >- asm_rewrite_tac[] >>
      reverse conj_tac >- decide_tac >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED
Finalise suffix_declared_agreement

Theorem suffix_write_state[local]:
  stmt_state_rel ctx func cenv cx es initial /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ k = root+n2w delta /\
  w2n root + type_slot_size rtv <= dimword (:256) /\
  w2n root+delta < dimword (:256) /\
  (!mid' name' keys' root' tv'.
    declared_storage_region cx mid' name' keys' = SOME (tr,root',tv') /\
    (root',tv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size tv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n p) initial.vs_memory /\
  val_footprint tv v <= 32*n /\ n <= type_slot_size tv /\
  w2n p+32*n < dimword (:256) /\
  write_storage_slot cx tr k tv v es = (res,es') ==>
  res = INL () /\ stmt_state_rel ctx func cenv cx es'
    (store_copy_prefix (if tr then LocTransient else LocStorage) p k initial n)
Proof
  strip_tac >>
  `~cx.txn.is_static` by fs[exprLoweringPropsTheory.stmt_state_rel_def,
    compileEnvTheory.state_rel_def] >>
  drule_all topcopy_typed_storage_write >>
  disch_then (qspecl_then [`tr`, `k`, `es`] strip_assume_tac) >> fs[] >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
    (get_storage cx es tr)
    (if tr then contract_transient initial else contract_storage initial)` by
    metis_tac[topcopy_initial_agree] >>
  `storage_agree
    (storage_dead cx tr (apply_writes k writes (get_storage cx es tr)))
    (apply_writes k writes (get_storage cx es tr))
    (if tr then contract_transient
       (store_copy_prefix LocTransient p k initial n)
     else contract_storage (store_copy_prefix LocStorage p k initial n))` by
    (irule suffix_declared_agreement >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     qexists_tac `n` >> gvs[] >> metis_tac[]) >>
  gvs[] >> Cases_on `tr` >> gvs[store_copy_prefix_def]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) []
        (Q.INST [`tr` |-> `T`] (SPEC_ALL topcopy_state_fold))) >>
      asm_rewrite_tac[] >>
      rule_assum_tac (CONV_RULE (ONCE_DEPTH_CONV (HO_REWR_CONV
        (SIMP_RULE (srw_ss()) []
          (Q.INST [`tr` |-> `T`] (SPEC_ALL topcopy_backend_fold)))))) >>
      fs[contract_transient_def, combinTheory.APPLY_UPDATE_THM]) >>
  ho_match_mp_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`tr` |-> `F`] (SPEC_ALL topcopy_state_fold))) >>
  asm_rewrite_tac[] >>
  rule_assum_tac (CONV_RULE (ONCE_DEPTH_CONV (HO_REWR_CONV
    (SIMP_RULE (srw_ss()) []
      (Q.INST [`tr` |-> `F`] (SPEC_ALL topcopy_backend_fold)))))) >>
  fs[contract_storage_def, vfmStateTheory.lookup_account_def,
     combinTheory.APPLY_UPDATE_THM]
QED

Theorem suffix_singleton_path[local]:
  emit_op MLOAD [src] sa = (op,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sm = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME k /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  w2n p+32 <= s.vs_alloca_next /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      store_copy_prefix (if tr then LocTransient else LocStorage) p k s 1 /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule_all emitted_insts_append >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def, IS_PREFIX_APPEND3] >> simp[GSYM APPEND_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> decide_tac) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule concat_code_prefix >> metis_tac[]) >>
  drule_at (Pat `lookup_block _ _ = _`) topcopy_singleton_path >>
  disch_then (qspecl_then [`if tr then LocTransient else LocStorage`,
    `src`, `dst`, `p`, `k`, `out`, `sa.cs_next_id`, `ctx`] mp_tac) >>
  impl_tac >- (Cases_on `tr` >> gvs[] >> metis_tac[]) >>
  strip_tac >> qexists_tac `t` >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  Cases_on `tr` >> gvs[store_copy_prefix_def, WORD_ADD_0, WORD_MULT_CLAUSES] >>
  metis_tac[]
QED

Theorem suffix_buffer_path[local]:
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    src F loc typ src_ty NONE mem_size sa = ((),sb) /\
  (typ = src_ty \/ is_bytestring_type typ /\ is_bytestring_type src_ty) /\
  copy_size = (if is_bytestring_type typ
               then type_memory_bytes cenv src_ty else mem_size) /\
  n = (if copy_size <= 32 then 1 else copy_size DIV 32) /\
  n < dimword (:256) /\ w2n p+32*n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME k /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      store_copy_prefix (if tr then LocTransient else LocStorage) p k s n /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  `~(typ <> src_ty /\ ~(is_bytestring_type typ /\ is_bytestring_type src_ty))` by
    metis_tac[] >>
  qpat_x_assum `typ = src_ty \/ _` kall_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_return_def] >>
  qpat_x_assum `~(typ <> src_ty /\ _)` kall_tac >>
  Cases_on `copy_size <= 32`
  >- (Cases_on `tr`
      >- (gvs[comp_bind_def, comp_return_def, AllCaseEqs()] >>
          strip_tac >> pairarg_tac >> gvs[] >>
          irule (SRULE [] (Q.INST [`tr` |-> `T`] suffix_singleton_path)) >>
          metis_tac[]) >>
      gvs[comp_bind_def, comp_return_def, AllCaseEqs()] >>
      strip_tac >> pairarg_tac >> gvs[] >>
      irule (SRULE [] (Q.INST [`tr` |-> `F`] suffix_singleton_path)) >>
      metis_tac[]) >>
  Cases_on `tr` >>
  gvs[compile_memory_to_storage_def, compile_memory_to_transient_def,
      comp_ignore_bind_def, comp_bind_def, comp_return_def, AllCaseEqs()] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`) topcopy_compile_loop_path >>
  disch_then (qspecl_then [`ctx`, `func`, `s`, `p`, `k`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> fs[store_copy_frame_def]
QED

Theorem assign_place_storage_suffix_mem:
  compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
    src F loc typ src_ty NONE mem_size sa = ((),sb) /\
  (typ = src_ty \/ is_bytestring_type typ /\ is_bytestring_type src_ty) /\
  copy_size = (if is_bytestring_type typ
               then type_memory_bytes cenv src_ty else mem_size) /\
  n = (if copy_size <= 32 then 1 else copy_size DIV 32) /\
  n < dimword (:256) /\ w2n p+32*n <= s.vs_alloca_next /\
  w2n p+32*n < dimword (:256) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME k /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name keys = SOME (tr,root,rtv) /\
  storage_subregion rtv path delta tv /\ k = root+n2w delta /\
  w2n root + type_slot_size rtv <= dimword (:256) /\
  w2n root+delta < dimword (:256) /\
  (!mid' name' keys' root' tv'.
    declared_storage_region cx mid' name' keys' = SOME (tr,root',tv') /\
    (root',tv') <> (root,rtv) ==>
    ranges_disjoint (w2n root) (type_slot_size rtv)
                    (w2n root') (type_slot_size tv')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n p) s.vs_memory /\
  val_footprint tv v <= 32*n /\ n <= type_slot_size tv /\
  write_storage_slot cx tr k tv v es = (res,es') ==>
  res = INL () /\
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es' t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `res = INL () /\ stmt_state_rel ctx func cenv cx es'
     (store_copy_prefix (if tr then LocTransient else LocStorage) p k s n)` by
    (irule suffix_write_state >> metis_tac[]) >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      store_copy_prefix (if tr then LocTransient else LocStorage) p k s n /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule suffix_buffer_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     metis_tac[]) >>
  simp[] >> qexists_tac `t` >> simp[] >>
  irule topcopy_normalized_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> fs[store_copy_normalize_def] >> metis_tac[]
QED

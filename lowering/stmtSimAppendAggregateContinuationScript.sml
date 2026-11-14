(* Aggregate Append after RHS evaluation, at a resolved storage slot. *)
Theory stmtSimAppendAggregateContinuation
Ancestors
  stmtSimAppendStorageCompose exprSimPopNestedBase
  stmtSimDefs gasOutcome gasSummary fragGasMode fragGasPath
  accountsRelProps loweringStateRelDefs exprLoweringProps
  stmtLoweringMono freshWrites varsExt stateFrame
  exprSimWordArgs loweringPosts stmtSimProps venomInst
  stmtSimStoreCopy valueEncodingProps vyperState
  exprLowering exprLoweringProps fragExec rich_list emitHelperProps emitHelper
  compileEnv stmtLowering context words list
  loweringHalt abiTupleProps externalEntryShape vyperStorageBackend venomState vyperValue

Theorem append_aggregate_staging_continuation:
  compile_alloc_buffer (type_memory_bytes cenv elem) sb = (buf,sc) /\
  compile_store_memory cenv raw buf.buf_operand elem elem sc = ((),sd) /\
  compile_dynarray_append cenv bop buf.buf_operand 1
    ((type_memory_bytes cenv elem+31) DIV 32) elem elem cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sd = ((),sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\ stmt_state_rel ctx func cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand bop s = SOME slot /\
  (!x. bop = Var x ==> not_fresh_at sb x) /\
  eval_operand raw s = SOME sw /\
  (!x. raw = Var x ==> not_fresh_at sb x) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\ value_has_type tv v /\
  val_footprint tv v <= type_memory_bytes cenv elem /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\ 0 < type_slot_size tv /\
  type_memory_bytes cenv elem = 32 * type_slot_size tv /\
  type_memory_bytes cenv elem < dimword (:256) /\ cap < dimword (:256) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!raw. storage_read_live cx tr raw slot (ArrayTV tv (Dynamic cap))) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!es0 s0 u cut (b:bytes32) len v0 writes ks res es1.
    stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv cut /\
    value_has_type tv v0 /\ val_in_memory tv v0 (w2n b) s0.vs_memory /\
    encode_value tv v0 = SOME writes /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    w2n b + 32 * type_slot_size tv <= dimword (:256) /\
    len = w2n (lookup_storage slot (get_storage cx es0 tr)) /\ len < cap /\
    store_copy_normalize s0 u =
      (if tr then tstore else sstore) slot (n2w (len+1))
        (FOLDL (\t i. (if tr then tstore else sstore)
          (slot+n2w (1+len*type_slot_size tv)+n2w i)
          (mem_word_at (w2n b+32*i) s0.vs_memory) t) s0 ks) /\
    (!x. not_fresh_at cut x ==> lookup_var x u = lookup_var x s0) /\
    append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v0 es0 = (res,es1) ==>
    res = INL () /\ stmt_state_rel ctx func cenv cx es1 u) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (ee,s)
    (stmt_post ctx func cx lctx cenv cenv sb sf ee s)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  strip_tac >>
  `cs_extends sb sc` by metis_tac[compile_alloc_buffer_extends] >>
  `compile_copy_memory buf.buf_operand raw (type_memory_bytes cenv elem) sc = ((),sd)` by
    gvs[compile_store_memory_def] >>
  `cs_extends sc sd` by
    (drule compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends sd sf` by metis_tac[compile_dynarray_append_labels, pairTheory.SND] >>
  `fn_has_code sb sd func /\ fn_has_code sd sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `0 < type_memory_bytes cenv elem` by decide_tac >>
  drule append_sparse_staging_frame >> disch_then drule >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK staged)` >>
  `storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient staged else contract_storage staged)
    slot (ArrayTV tv (Dynamic cap))` by
    (irule storage_range_agree_of_live >>
     conj_tac >- simp[] >>
     metis_tac [stmtSimStoreCopyStateTheory.stmt_state_selected_storage_agree]) >>
  drule nested_pop_array_header_load >> strip_tac >>
  `eval_operand bop staged = SOME slot` by
    (drule exprSimAbiEncodeArgsCountedLabelsTheory.abi_args_marked_path_labels >>
     strip_tac >> Cases_on `bop` >>
     qpat_x_assum `eval_operand _ s = SOME slot` mp_tac >>
     gvs[eval_operand_def]) >>
  `!x. bop = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sd x` by
    (gen_tac >> strip_tac
     >- (irule not_fresh_at_mono >> qexists_tac `sb` >>
         conj_tac
         >- (`ci_mono sb sc /\ ci_mono sc sd` by
               metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
             fs[ci_mono_def] >> decide_tac) >> simp[]) >>
     gvs[]) >>
  `~staged.vs_call_ctx.cc_static` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ staged` mp_tac >>
     simp[stmt_state_rel_def, state_rel_def]) >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[vyperTypingTheory.value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  `((type_memory_bytes cenv elem + 31) DIV 32) = type_slot_size tv` by simp[] >>
  drule append_storage_copy_suffix_path >>
  disch_then (drule_at (Pat `fn_has_code sd sf func`)) >>
  disch_then (drule_at (Pat `encode_value tv v = SOME writes`)) >>
  disch_then (drule_at (Pat `val_in_memory tv v (w2n w) staged.vs_memory`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (qspecl_then [`slot`, `ctx`] mp_tac) >>
  (impl_tac >-
    (simp[] >>
     conj_tac >- (simp[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
     conj_tac
     >- (strip_tac >>
         qspecl_then [`slot`, `w2n (lookup_storage slot (get_storage cx ee tr))`,
                      `type_slot_size tv`, `cap`] mp_tac append_sparse_destination_bound >>
         simp[wordsTheory.n2w_w2n] >> disch_then irule >> simp[] >>
         qpat_x_assum `w2n slot + type_slot_size _ <= _` mp_tac >>
         simp[type_slot_size_def, arithmeticTheory.MULT_COMM]) >>
     gvs[])) >>
  simp[LET_THM] >>
  Cases_on `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v ee` >>
  rename1 `_ = (res,ef)` >>
  Cases_on `w2n (lookup_storage slot (get_storage cx ee tr)) < cap`
  >- suspend "stored" >>
  suspend "full"
QED

Resume append_aggregate_staging_continuation[stored]:
  simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func staged 0 (OK fin)` >>
  `store_copy_normalize staged fin =
    (if tr then tstore else sstore) slot
      (n2w (w2n (lookup_storage slot (get_storage cx ee tr))+1))
      (FOLDL (\q i. (if tr then tstore else sstore)
        (slot+n2w (1+w2n (lookup_storage slot (get_storage cx ee tr))*type_slot_size tv)+n2w i)
        (mem_word_at (w2n w+32*i) staged.vs_memory) q) staged ks)` by
    (qpat_x_assum `store_copy_normalize staged fin = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     pure_rewrite_tac[GSYM wordsTheory.word_add_n2w,
       GSYM wordsTheory.word_mul_n2w, wordsTheory.n2w_w2n] >>
     simp_tac bool_ss [valueEncodingPropsTheory.mem_word_at_eq_mload,
       arithmeticTheory.ADD_COMM, wordsTheory.WORD_ADD_ASSOC]) >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sb` >> simp[] >>
     `ci_mono sb sc /\ ci_mono sc sd` by
       metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
     fs[ci_mono_def]) >>
  `res = INL () /\ stmt_state_rel ctx func cenv cx ef fin` by
    (first_x_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `store_copy_normalize _ _ = _`)) >>
     disch_then (drule_at (Pat `append_place _ _ _ _ = _`)) >>
     disch_then irule >> simp[] >>
     qexists_tac `sd` >> simp[]) >>
  `gas_marked_path F ctx func s 0 (OK fin)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl_tac [`res`, `ef`, `OK fin`] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >>
      metis_tac[append_storage_place_gas_obs]) >>
  disj1_tac >> simp[] >>
  `stmt_state_rel ctx func cenv cx (ef with gas_obs := []) fin` by
    metis_tac[stmt_state_rel_gas_obs] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      rewrite_tac[append_storage_copy_suffix_parts] >> strip_tac >>
      drule exprOpenPrimitivesTheory.emit_void_terminated >>
      Cases_on `tr` >> simp[is_terminator_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sd x` by
        (irule not_fresh_at_mono >> qexists_tac `sb` >> simp[] >>
         `ci_mono sb sc /\ ci_mono sc sd` by
           metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
         fs[ci_mono_def]) >> metis_tac[]) >>
  `fin.vs_allocas = staged.vs_allocas /\ fin.vs_memory = staged.vs_memory` by
    (qpat_x_assum `store_copy_normalize staged fin = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. (s.vs_allocas,s.vs_memory)``) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       SIMP_RULE std_ss [LET_THM] append_sparse_store_projections]) >>
  conj_tac >- metis_tac[] >>
  `ef.scopes = ee.scopes` by
    (drule vyperScopePreservationTheory.append_storage_place_scopes_immutables >> simp[]) >>
  `alloca_frame cenv ee sd staged cenv (ef with gas_obs := []) fin` by
    (irule alloca_frame_of_mem_frame >> simp[] >>
     qexistsl_tac [`ctx`, `cx`, `func`] >> simp[] >> gvs[]) >>
  irule alloca_frame_trans >>
  qexistsl_tac [`cenv`, `ee`, `staged`, `sd`] >> simp[] >>
  `ci_mono sb sc /\ ci_mono sc sd` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory, pairTheory.SND] >>
  fs[ci_mono_def] >> decide_tac
QED

Resume append_aggregate_staging_continuation[full]:
  simp[] >> strip_tac >>
  `cap <= w2n (lookup_storage slot (get_storage cx ee tr))` by decide_tac >>
  rename1 `gas_marked_path F ctx func staged 0 (Abort Revert_abort fin)` >>
  `gas_marked_path F ctx func s 0 (Abort Revert_abort fin)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  `res = INR (Error (RuntimeError "append full storage array"))` by
    (drule stmtSimAppendStorageTheory.append_storage_full >>
     disch_then (qspecl_then [`v`, `tv`] mp_tac) >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `ef`, `Abort Revert_abort fin`] >>
  conj_tac
  >- (simp[gas_marked_exec_def] >> metis_tac[append_storage_place_gas_obs]) >>
  simp[exit_result_def, stmt_exit_def, exprSimDefsTheory.expr_exit_def]
QED

Finalise append_aggregate_staging_continuation

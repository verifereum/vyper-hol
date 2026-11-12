(* Counted aggregate Append suffix and semantic postcondition. *)
Theory bodyMemAppendAggregateValuePath
Ancestors
  bodyMemAppendAggregatePath appendStorageAggregateRel bodyMemAssignTopCopySem
  stmtSimStoreCopy stmtSimAppendStorageCompose bodyMemAppendFacts
  words list rich_list valueEncodingProps venomState venomExecSemantics
  stmtSimDefs stmtSimProps exprSimProps loweringStateRelDefs compileEnv
  placeStoreStorage allocaHistory fragExec bodyMemAssignTopCopyCompiler emitHelper emitHelperProps venomInst
  exprSimDefs loweringPosts appendStorageRel exprLoweringProps stmtSimAppendStorage

Theorem append_aggregate_control_frame[local]:
  !H ctx func cenv cx es s V bb ix prev.
    stmt_state_rel H ctx func cenv cx es
      (s with <|vs_vars := V; vs_current_bb := bb;
                vs_inst_idx := ix; vs_prev_bb := prev|>) =
    stmt_state_rel H ctx func cenv cx es (s with vs_vars := V)
Proof
  rpt gen_tac >>
  `fmp_room ctx func
     (s with <|vs_vars := V; vs_current_bb := bb;
               vs_inst_idx := ix; vs_prev_bb := prev|>) =
   fmp_room ctx func (s with vs_vars := V)` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, immutable_base_zero_alt,
       lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def]
QED

Theorem append_aggregate_prefix_words[local]:
  w2n b+32*n < dimword (:256) ==>
  store_copy_prefix (if tr then LocTransient else LocStorage) b a s n =
    FOLDL (\t i. (if tr then tstore else sstore) (a+n2w i)
      (mem_word_at (w2n b+32*i) s.vs_memory) t) s (COUNT_LIST n)
Proof
  strip_tac >> simp[store_copy_prefix_def] >>
  irule listTheory.FOLDL_CONG >> simp[MEM_COUNT_LIST] >>
  rpt strip_tac >> rename1 `i < n` >>
  `w2n (b+n2w i*32w) = w2n b+32*i` by
    (`b + n2w i * 32w = n2w (w2n b + 32*i)` by
       simp[GSYM word_add_n2w, GSYM word_mul_n2w,
            arithmeticTheory.MULT_COMM, WORD_MULT_COMM] >>
     asm_rewrite_tac[] >>
     `w2n b + 32*i < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
  Cases_on `tr` >> simp[mem_word_at_eq_mload]
QED

Theorem append_storage_aggregate_success_post_mem[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  local_ptrs_reserved cenv sa /\
  store_copy_normalize s t =
    (if tr then tstore else sstore) slot
      (n2w (w2n (lookup_storage slot (get_storage cx es tr)))+1w)
      (store_copy_prefix (if tr then LocTransient else LocStorage)
        b (slot+1w+n2w (w2n (lookup_storage slot (get_storage cx es tr)))*n2w (type_slot_size tv))
        s (type_slot_size tv)) /\
  (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!slot' tv'.
    MEM (tr,slot',tv') (FST H) /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) /\
  w2n (lookup_storage slot (get_storage cx es tr)) < cap /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s.vs_memory /\ encode_value tv v = SOME writes /\
  w2n b + 32*type_slot_size tv < dimword (:256) ==>
  res = INL () /\ stmt_state_rel H ctx func cenv cx es' t
Proof
  strip_tac >>
  `w2n (lookup_storage slot (get_storage cx es tr)) =
   w2n (lookup_storage slot (get_storage cx es tr))` by simp[] >>
  drule_all stmt_state_rel_append_storage_aggregate >> strip_tac >>
  qpat_x_assum `w2n _ = w2n _` kall_tac >>
  `stmt_state_rel H ctx func cenv cx es' (store_copy_normalize s t)` by
    (asm_rewrite_tac [] >>
     drule append_aggregate_prefix_words >>
     disch_then (qspec_then `tr` assume_tac) >>
     gvs[GSYM word_add_n2w, GSYM word_mul_n2w, WORD_ADD_ASSOC]) >>
  conj_tac >- asm_rewrite_tac [] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ (store_copy_normalize _ _)` mp_tac >>
  pure_rewrite_tac [store_copy_normalize_def, append_aggregate_control_frame] >> strip_tac >>
  irule stmt_state_rel_reserved_frame >>
  qexistsl_tac [`t with vs_vars := s.vs_vars`, `sa`] >>
  simp[stateFrameTheory.state_frame_vars, lookup_var_def] >> metis_tac[]
QED

Theorem append_storage_aggregate_history[local]:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  fn_has_code sa sf func /\ alloca_history func s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = sf.cs_current_bb /\
  t.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  alloca_history func t
Proof
  strip_tac >> drule (iffLR append_storage_copy_suffix_parts) >>
  disch_then (qx_choosel_then
    [`len'`, `valid`, `data`, `offset`, `dst`, `fresh`, `u`,
     `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`] strip_assume_tac) >>
  `s7.cs_current_insts = []` by
    (drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
       topcopy_compile_certificate >>
     impl_tac >- (Cases_on `tr` >> simp[]) >> strip_tac >>
     qpat_x_assum `new_block _ _ = (_,s7)` mp_tac >>
     simp[new_block_def] >> strip_tac >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) sf.cs_current_insts` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
     rpt strip_tac >> gvs[] >> Cases_on `tr` >> simp[mk_inst_def]) >>
  fs[alloca_history_def, fn_has_code_def] >> rpt strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[IS_PREFIX_APPEND] >>
  strip_tac >> gvs[venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
  fs[EVERY_EL] >> metis_tac[]
QED

(* The suffix path does not depend on the horizon, so one path serves every
   horizon P admits. *)
Theorem append_storage_aggregate_value_path_mem:
  compile_dynarray_append cenv (Lit slot) op 1 (type_slot_size tv) dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME b /\ cap < dimword (:256) /\
  type_slot_size tv < dimword (:256) /\
  w2n b + 32*type_slot_size tv <= s.vs_alloca_next /\
  w2n b + 32*type_slot_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!(H:(bool # bytes32 # type_value) list # num list). P H ==>
    stmt_state_rel H ctx func cenv cx es s /\
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    (!slot' tv'.
      MEM (tr,slot',tv') (FST H) /\
      (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
      ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                      (w2n slot') (type_slot_size tv'))) /\
  P H0 /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s.vs_memory /\ encode_value tv v = SOME writes /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  fn_has_code sa sf func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s ==>
  ?r. gas_marked_path T ctx func s 0 r /\
    ((?t. r = OK t /\ res = INL () /\
      (!H. P H ==> stmt_state_rel H ctx func cenv cx es' t) /\
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t) \/
     (exit_result r /\ stmt_exit RetQ es' res r))
Proof
  strip_tac >>
  `(if tr then tload slot s else sload slot s) =
   lookup_storage slot (get_storage cx es tr) /\ ~s.vs_call_ctx.cc_static` by
    (qpat_assum `!H. P H ==> _` (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac >- (drule_all append_storage_header_agree_mem >> simp[]) >>
     qpat_x_assum `stmt_state_rel H0 _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  `eval_operand (Lit slot) s = SOME slot /\
   (!x. Lit slot = Var x \/ op = Var x ==> not_fresh_at sa x)` by
    simp[eval_operand_def] >>
  drule_all append_storage_aggregate_suffix_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (lookup_storage slot (get_storage cx es tr)) < cap`
  >- (`?t. gas_marked_path T ctx func s 0 (OK t) /\
        store_copy_normalize s t =
          (if tr then tstore else sstore) slot
            (n2w (w2n (lookup_storage slot (get_storage cx es tr)))+1w)
            (store_copy_prefix (if tr then LocTransient else LocStorage) b
              (slot+1w+n2w (w2n (lookup_storage slot (get_storage cx es tr)))*n2w (type_slot_size tv))
              s (type_slot_size tv)) /\
        (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
        t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        ~t.vs_halted /\ t.vs_memory = s.vs_memory /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
        (first_x_assum irule >> simp[]) >>
      `!H. P H ==> res = INL () /\ stmt_state_rel H ctx func cenv cx es' t` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. P H ==> _` (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         qpat_x_assum `!H. P H ==> _` kall_tac >>
         drule_all append_storage_aggregate_success_post_mem >> simp[]) >>
      `res = INL ()` by metis_tac[] >>
      `alloca_history func t` by (irule append_storage_aggregate_history >> metis_tac[]) >>
      qexists_tac `OK t` >> simp[stmt_lands_def] >> metis_tac[]) >>
  `cap <= w2n (lookup_storage slot (get_storage cx es tr))` by decide_tac >>
  drule append_storage_full >> strip_tac >>
  `?a t. gas_marked_path T ctx func s 0 (Abort a t)` by
    (first_x_assum irule >> metis_tac[]) >>
  qexists_tac `Abort a t` >>
  gvs[stmt_exit_def, exit_result_def, expr_exit_def]
QED

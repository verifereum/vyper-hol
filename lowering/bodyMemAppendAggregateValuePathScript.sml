Theory bodyMemAppendAggregateValuePath
Ancestors
  bodyMemAppendAggregatePath appendStorageAggregateRel bodyMemAssignTopCopySem
  stmtSimStoreCopy stmtSimAppendStorageCompose bodyMemAppendFacts
  words list rich_list valueEncodingProps venomState venomExecSemantics
  stmtSimDefs stmtSimProps exprSimProps loweringStateRelDefs compileEnv
  placeStoreStorage allocaHistory fragExec emitHelper emitHelperProps venomInst
  exprSimDefs loweringPosts appendStorageRel exprLoweringProps stmtSimAppendStorage
  fragGasPathFrameMem bodyMemAggregatePath

Theorem append_storage_aggregate_value_path_mem:
  compile_dynarray_append cenv (Lit slot) op 1 (type_slot_size tv) dt vt cap F
    (if tr then LocTransient else LocStorage) sa = ((),sf) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME b /\ cap < dimword (:256) /\
  type_slot_size tv < dimword (:256) /\
  w2n b + 32*type_slot_size tv <= s.vs_alloca_next /\
  w2n b + 32*type_slot_size tv < dimword (:256) /\
  evaluate_type (get_tenv cx) dt = SOME tv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!mid' n' subs' slot' tv'.
    declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n b) s.vs_memory /\ encode_value tv v = SOME writes /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s ==>
  ?r. gas_marked_path T ctx func s 0 r /\
    ((?t. r = OK t /\ res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t) \/
     (exit_result r /\ stmt_exit RetQ es' res r))
Proof
  strip_tac >>
  drule_all append_storage_header_agree_mem >> strip_tac >>
  `~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `eval_operand (Lit slot) s = SOME slot /\
   (!x. Lit slot = Var x \/ op = Var x ==> not_fresh_at sa x)` by
    simp[eval_operand_def] >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx es tr))` >>
  `len = w2n (if tr then tload slot s else sload slot s)` by
    simp[Abbr `len`] >>
  `len < cap ==>
   w2n (slot+1w+n2w len*n2w (type_slot_size tv)) +
      type_slot_size tv <= dimword (:256)` by
    (strip_tac >>
     `len * type_slot_size tv + type_slot_size tv <= cap * type_slot_size tv` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
     qpat_assum `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= _` mp_tac >>
     qpat_assum `len * type_slot_size tv + type_slot_size tv <= cap * type_slot_size tv` mp_tac >>
     qpat_assum `0 < type_slot_size tv` mp_tac >>
     rpt (pop_assum kall_tac) >>
     pure_rewrite_tac[vyperValueTheory.type_slot_size_def] >> rpt strip_tac >>
     `w2n slot + (1 + len * type_slot_size tv) < dimword (:256)` by
       decide_tac >>
     pure_rewrite_tac[wordsTheory.word_mul_n2w,
       wordsTheory.WORD_ADD_ASSOC, GSYM wordsTheory.word_add_n2w] >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >>
     decide_tac) >>
  `w2n b + type_memory_size tv < dimword (:256) /\
   w2n b + type_memory_size tv <= s.vs_alloca_next` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  drule_all append_storage_aggregate_suffix_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `len < cap`
  >- (qpat_x_assum `len < cap ==> ?t ks. _`
        (qx_choosel_then [`t`, `ks`] strip_assume_tac o UNDISCH) >>
      `store_copy_normalize s (t with vs_vars := s.vs_vars) =
        (if tr then tstore else sstore) slot (n2w (len+1))
          (FOLDL (\q i. (if tr then tstore else sstore)
            (slot+n2w (1+len*type_slot_size tv)+n2w i)
            (mem_word_at (w2n b+32*i) s.vs_memory) q) s ks)` by
        (qpat_x_assum `store_copy_normalize s t = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         pure_rewrite_tac[GSYM wordsTheory.word_add_n2w,
           GSYM wordsTheory.word_mul_n2w, wordsTheory.n2w_w2n] >>
         simp_tac bool_ss [stmtSimStoreCopyTheory.store_copy_normalize_def,
           valueEncodingPropsTheory.mem_word_at_eq_mload,
           arithmeticTheory.ADD_COMM, wordsTheory.WORD_ADD_ASSOC] >>
         rpt strip_tac >> fs[venom_state_component_equality]) >>
      `res = INL () /\
       stmt_state_rel ctx func cenv cx es' (t with vs_vars := s.vs_vars)` by
        (mp_tac (Q.INST [`u` |-> `t with vs_vars := s.vs_vars`,
           `sb` |-> `sa`, `len` |-> `len`, `b` |-> `b:bytes32`,
           `ks` |-> `ks`, `writes` |-> `writes`]
           (INST_TYPE [alpha |-> ``:256``] append_storage_copy_success_post)) >>
         (impl_tac >-
           (`len = w2n (lookup_storage slot (get_storage cx es tr))` by
              simp_tac bool_ss [Abbr `len`] >>
            `w2n b + 32 * type_slot_size tv <= dimword (:256)` by decide_tac >>
            asm_rewrite_tac[] >> rpt (pop_assum kall_tac) >>
            simp[lookup_var_def])) >>
         disch_then ACCEPT_TAC) >>
      `stmt_state_rel ctx func cenv cx es' t` by
        (irule stmt_state_rel_reserved_frame >>
         qexistsl_tac [`t with vs_vars := s.vs_vars`, `sa`] >>
         simp[stateFrameTheory.state_frame_vars, lookup_var_def] >>
         metis_tac[]) >>
      `alloca_inv s` by fs[stmt_state_rel_def] >>
      `alloca_history func t` by
        (irule fragGasPathFrameMemTheory.gas_path_mem_zero_history >>
         simp[] >>
          metis_tac[fragGasModeTheory.gas_marked_path_def,
           bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv]) >>
      qexists_tac `OK t` >> simp[stmt_lands_def]) >>
  `cap <= len` by decide_tac >>
  `cap <= w2n (lookup_storage slot (get_storage cx es tr))` by
    fs[Abbr `len`] >>
  drule append_storage_full >> strip_tac >>
  `?a t. gas_marked_path T ctx func s 0 (Abort a t)` by
    (qpat_x_assum `cap <= len ==> _` irule >> simp[]) >>
  qexists_tac `Abort a t` >>
  gvs[Abbr `len`, stmt_exit_def, exit_result_def, expr_exit_def]
QED

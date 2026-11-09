(* Counted live-slot stores with their normalized storage effect. *)
Theory storeSlotsCountedBase
Ancestors
  storeSlotsMemoryFootprint bodyMemAssignTopCopySuffix placeStoreSlots
  placeStoreCopyPath stmtSimStoreCopy storeSlotsMemoryPaths typedMemoryCopy
  context compileEnv fragExec fragGasMode venomState venomInst
  valueEncoding valueEncodingProps vyperTyping words arithmetic list rich_list
  vyperTypeSystem vyperValue exprLoweringProps emitHelperProps stmtLowering exprOperandVar
  bodyMemAssignTopCopyPaths bodyMemAssignTopCopyLoop fragExecMem emitHelper
  typedCopyDomain abiTypeBoundProps vyperEncodeDecode vyperStorageCoverage

val _ = diminish_srw_ss ["sizes"]

Theorem store_slots_copy_op_mem:
  compile_word_copy_loop_op src dst cnt LocMemory
    (if tr then LocTransient else LocStorage) F sa = (result,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand cnt s = SOME (n2w n) /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) /\
  w2n sw + 32*n <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32*j) s) q) s (COUNT_LIST n) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_alloca_next = s.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa (if tr then LocTransient else LocStorage) sw dw s n t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule store_slots_runtime_copy_path_mem >>
     Cases_on `tr` >> simp[] >> metis_tac[]) >>
  drule place_store_copy_frame_observations >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (fs[store_copy_frame_def] >> drule topcopy_normalize_allocations >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  fs[store_copy_frame_def, store_copy_prefix_def] >>
  irule FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by decide_tac >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    (pure_rewrite_tac[GSYM word_add_n2w, GSYM word_mul_n2w, n2w_w2n] >>
     wordsLib.WORD_DECIDE_TAC) >>
  Cases_on `tr` >> simp[w2n_n2w, LESS_MOD] >> gvs[]
QED

Theorem store_slots_bytes_entry_mem:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  compile_store_slots cenv src slot ty tr sa = ((),sb) /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields ty /\
   ?cap. tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[is_bytestring_type_def, evaluate_type_def, is_abi_dynamic_def]) >>
  drule_at (Pat `val_in_memory _ _ _ _`) store_slots_bytes_footprint >>
  disch_then (qspecl_then [`writes`, `cap`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count src sa = (cnt,sm)` >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_word_copy_loop_op _ _ _ _ _ _ sm = (res,sb)` >>
  drule_all bytes_count_mono_fresh >> strip_tac >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_word_copy_loop_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `w2n sw + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all store_slots_bytes_count_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "copy"
QED
Resume store_slots_bytes_entry_mem[copy]:
  markerLib.RESUME_TAC >> (
  `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sm x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  `u.vs_call_ctx = s.vs_call_ctx` by
    (fs[typed_copy_state_frame_def] >> gvs[venom_state_component_equality]) >>
  `w2n sw + 32 * (1 + word_size L) < dimword (:256) /\
   w2n sw + 32 * (1 + word_size L) <= u.vs_alloca_next` by gvs[] >>
  `~u.vs_call_ctx.cc_static` by simp[] >>
  `1 + word_size L < dimword (:256)` by decide_tac >>
  drule_all store_slots_copy_op_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t`, `COUNT_LIST (1 + word_size L)`] >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `u` >> simp[]) >>
  reverse conj_tac
  >- (conj_tac >- simp[MEM_COUNT_LIST] >>
      qpat_x_assum `store_copy_normalize _ _ = _` kall_tac >>
      fs[typed_copy_state_frame_def] >> gvs[venom_state_component_equality] >>
      rpt strip_tac >>
      `not_fresh_at sm x` by metis_tac[compiler_ci_mono_not_fresh] >>
      metis_tac[]) >>
  `store_copy_normalize s u = s` by
    (qpat_x_assum `!off len. typed_copy_state_frame _ _ _ _ _`
       (qspecl_then [`0`, `0`] mp_tac) >>
     simp[typed_copy_state_frame_def, store_copy_normalize_def,
          venom_state_component_equality]) >>
  `store_copy_normalize s t = store_copy_normalize s (store_copy_normalize u t)` by
    simp[NoAsms, store_copy_normalize_def] >>
  pop_assum SUBST1_TAC >> asm_rewrite_tac[] >>
  simp[store_slots_normalize_fold] >>
  irule FOLDL_CONG >> simp[] >> rpt strip_tac >>
  metis_tac[GSYM mem_word_at_eq_mload])
QED
Finalise store_slots_bytes_entry_mem

Theorem store_slots_singleton_mem[local]:
  emit_op MLOAD [src] sa = (op,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sm = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  w2n sw + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      (if tr then tstore else sstore) dw (mload (w2n sw) s) s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule_all emitted_insts_append >> strip_tac >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (fs[same_blocks_def, IS_PREFIX_APPEND3] >> simp[GSYM APPEND_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `Var out` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> decide_tac) >>
  `!x. dst = Var x ==> x <> out` by metis_tac[] >>
  `?t. run_inst_seq
     [mk_inst sa.cs_next_id MLOAD [src] [out];
      mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE)
        [dst; Var out] []] s = OK t /\
    store_copy_normalize s t =
      (if tr then tstore else sstore) dw (mload (w2n sw) s) s /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\ t.vs_halted = s.vs_halted` by
    (Cases_on `tr`
     >- (simp[NoAsms] >> irule (SRULE [] (Q.SPEC `LocTransient` topcopy_singleton_run)) >>
         metis_tac[]) >>
     simp[NoAsms] >> irule (SRULE [] (Q.SPEC `LocStorage` topcopy_singleton_run)) >>
     metis_tac[]) >>
  suspend "path"
QED
Resume store_slots_singleton_mem[path]:
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[] >>
     mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
                     `v` |-> `out`, `id` |-> `sa.cs_next_id`, `b` |-> `sw`]
       (SPEC_ALL body_mem_storage_singleton_mem_ok)) >>
     Cases_on `tr` >> simp[]) >>
  `gas_marked_path T ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule store_slots_emitted_seq_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[] >> Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `store_copy_normalize s t =
    (if tr then tstore else sstore) dw (mload (w2n sw) s) s` by
    (Cases_on `tr` >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
   t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
     Cases_on `tr` >>
     simp[store_copy_normalize_def, sstore_def, tstore_def,
          venom_state_component_equality]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[store_copy_normalize_def, lookup_var_def] >>
  fs[same_blocks_def, lookup_var_def] >> metis_tac[]
QED
Finalise store_slots_singleton_mem

Theorem store_slots_static_entry_mem:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src slot ty tr sa = ((),sb) /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typed_copy_memory_size >> metis_tac[]) >>
  `~vyper_is_dynamic tenv ty` by
    (drule_all abi_props_vyper_typed >> simp[]) >>
  `!j. MEM j (MAP FST writes) <=> j < type_slot_size tv` by
    (gen_tac >> eq_tac
     >- metis_tac[CONJUNCT1 encode_writes_bounded] >>
     strip_tac >> irule encode_value_live_written >> metis_tac[]) >>
  `type_memory_bytes cenv ty DIV 32 = type_slot_size tv` by
    simp[type_memory_size_slots] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def] >>
  Cases_on `type_slot_size tv = 1`
  >- (simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
      rename1 `emit_op MLOAD [src] sa = (loaded,sm)` >>
      `w2n sw + 32 <= s.vs_alloca_next` by fs[type_memory_size_slots] >>
      `!x. slot = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all store_slots_singleton_mem >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexistsl_tac [`t`, `[0]`] >> simp[]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  suspend "bulk"
QED
Resume store_slots_static_entry_mem[bulk]:
  markerLib.RESUME_TAC >> (
  rename1 `fn_has_code sa sb func` >>
  `type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * type_slot_size tv <= s.vs_alloca_next` by
    (fs[type_memory_size_slots] >> decide_tac) >>
  `?r. compile_word_copy_loop_op src slot (Lit (n2w (type_slot_size tv)))
    LocMemory (if tr then LocTransient else LocStorage) F sa = (r,sb)` by
    (Cases_on `tr` >>
     gvs[compile_memory_to_storage_def, compile_memory_to_transient_def,
         comp_ignore_bind_def, comp_bind_def, comp_return_def,
         compile_word_copy_loop_def, AllCaseEqs()]) >>
  `!x. src = Var x \/ slot = Var x \/ Lit (n2w (type_slot_size tv)) = Var x ==>
    not_fresh_at sa x` by (simp[] >> metis_tac[]) >>
  `eval_operand (Lit (n2w (type_slot_size tv))) s =
    SOME (n2w (type_slot_size tv))` by simp[eval_operand_def] >>
  drule_all store_slots_copy_op_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t`, `COUNT_LIST (type_slot_size tv)`] >> simp[MEM_COUNT_LIST])
QED
Finalise store_slots_static_entry_mem

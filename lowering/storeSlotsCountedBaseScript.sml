(* Counted live-slot stores with their normalized storage effect. *)
Theory storeSlotsCountedBase
Ancestors
  storeSlotsMemoryFootprint bodyMemAssignTopCopySuffix placeStoreSlots
  placeStoreCopyPath stmtSimStoreCopy storeSlotsMemoryPaths typedMemoryCopy
  context compileEnv fragExec fragGasMode venomState venomInst
  valueEncoding valueEncodingProps vyperTyping words arithmetic list rich_list
  vyperTypeSystem vyperValue exprLoweringProps emitHelperProps stmtLowering exprOperandVar

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

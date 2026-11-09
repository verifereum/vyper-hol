(* Source-preserving memory-safe calls for sparse bytestring stores. *)
Theory storeSlotsMemoryFootprint
Ancestors
  storeSlotsMemoryPaths placeStoreSlots exprOperandVar stmtLoweringMono
  typedMemoryCopy placeStoreCopyPath bodyMemAssignTopCopyPaths stmtSimStoreCopy
  context compileEnv emitHelperProps emitHelper exprLoweringProps
  fragGasMode fragExec venomState venomInst valueEncodingProps
  vyperTyping vyperValue finite_map list arithmetic words

Theorem bytes_count_mono_fresh:
  compile_bytestring_word_count src sa = (cnt,sm) ==>
  ci_mono sa sm /\ (!x. cnt = Var x ==> not_fresh_at sm x)
Proof
  simp[compile_bytestring_word_count_def, comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac typed_copy_emit_op_mono >> conj_tac
  >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  metis_tac[typed_copy_emit_op_fresh]
QED

Theorem store_slots_bytes_paths_mem[local]:
  compile_bytestring_word_count src sa = (cnt,sm) /\
  compile_word_copy_loop_op src dst cnt LocMemory loc ctor sm = (res,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  fn_has_code sa sb func /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mem_word_at (w2n sw) s.vs_memory = n2w L /\
  L + 63 < dimword (:256) /\ 1 + word_size L < dimword (:256) /\
  w2n sw + 32 * (1 + word_size L) <= s.vs_alloca_next /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_allocas = s.vs_allocas /\ t.vs_call_ctx = s.vs_call_ctx /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all bytes_count_mono_fresh >> strip_tac >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_word_copy_loop_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `w2n sw + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all store_slots_bytes_count_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `!x. src = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sm x` by
    metis_tac[compiler_ci_mono_not_fresh] >>
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_allocas = s.vs_allocas` by
    (fs[typed_copy_state_frame_def] >>
     gvs[venom_state_component_equality]) >>
  `?t. gas_marked_path T ctx func u 0 (OK t) /\
       store_copy_frame sm loc sw dw u (1 + word_size L) t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule store_slots_runtime_copy_path_mem >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule compiler_ci_mono_not_fresh >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_x_assum `!off len. typed_copy_state_frame _ _ _ _ _`
       (qspecl_then [`0`, `0`] mp_tac) >>
     simp[typed_copy_state_frame_def, store_copy_frame_def] >>
     fs[store_copy_frame_def] >> metis_tac[]) >>
  qexists_tac `t` >>
  drule_all place_store_copy_frame_observations >> strip_tac >>
  drule_all topcopy_frame_frontier >> strip_tac >>
  simp[] >> drule_all gas_marked_path_then >> simp[]
QED

Theorem store_slots_bytes_call_mem:
  is_bytestring_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ encode_value tv v = SOME writes /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  compile_store_slots cenv src dst dty tr sa = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_allocas = s.vs_allocas /\ t.vs_call_ctx = s.vs_call_ctx /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields dty /\
   ?cap. tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)` by
    (Cases_on `dty` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, evaluate_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[is_bytestring_type_def, evaluate_type_def, is_abi_dynamic_def]) >>
  drule_at (Pat `val_in_memory _ _ _ _`) store_slots_bytes_footprint >>
  disch_then (qspecl_then [`writes`, `cap`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  irule store_slots_bytes_paths_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_bytestring_word_count _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `L` >> Cases_on `tr` >>
  simp[] >> rpt conj_tac >> gvs[]
QED

(* Counted memory-safe address and member paths for sparse storage stores. *)
Theory storeSlotsCountedMembers
Ancestors
  storeSlotsCountedBase storeSlotsMemoryPaths placeStoreSlots
  context compileEnv fragExec fragGasMode typedMemoryCopy instMemFrontier stmtSimStoreCopy
  venomState venomInst venomExecSemantics emitHelperProps exprLoweringProps
  words arithmetic list rich_list valueEncoding valueEncodingProps

Theorem store_slots_lit_offset_path_mem:
  !ptr off sa op sb s w func ctx.
  compile_lit_byte_offset ptr off sa = (op,sb) /\
  eval_operand ptr s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      eval_operand op t = SOME (w + n2w off) /\
      t.vs_memory = s.vs_memory /\
      (!dst len. typed_copy_state_frame sa dst len s t) /\
      t.vs_alloca_next = s.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  map_every qx_gen_tac [`ptr0`, `off`, `sa`, `op`, `sb`, `s`, `w`, `func`, `ctx`] >>
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathMemTheory.gas_path_mem_rules,
           typed_copy_state_frame_def, typed_copy_frame_def,
           WORD_ADD_0, venom_state_component_equality]) >>
  Cases_on `ptr0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathMemTheory.gas_path_mem_rules,
           eval_operand_def, typed_copy_state_frame_def, typed_copy_frame_def,
           WORD_ADD_0, venom_state_component_equality]) >>
  simp[compile_lit_byte_offset_def, compile_with_byte_offset_def] >> strip_tac >>
  irule store_slots_emit_op_path_mem >>
  qpat_assum `emit_op ADD _ _ = _` (irule_at Any) >>
  gvs[is_terminator_def, below_frontier_no_ranges, step_inst_base_opcode_eqs,
      mk_inst_def, exec_pure2_def, eval_operand_def]
QED

Theorem store_slots_member_offset_run_mem:
  compile_lit_byte_offset src mo sa = (ms,a) /\
  compile_lit_byte_offset slot so a = (ds,b) /\
  compile_store_slots cenv ms ds ty tr b = ((),sc) /\
  (!src slot tr sa sb func s sw dw writes.
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
      t.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  encode_value tv v = SOME writes /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  val_in_memory tv v (w2n sw + mo) s.vs_memory /\
  w2n sw + mo + type_memory_size tv < dimword (:256) /\
  w2n sw + mo + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + so + type_slot_size tv <= dimword (:256) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) ((dw + n2w so) + n2w j)
        (mload (w2n sw + mo + 32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc` by
    metis_tac[ci_mono_compile_lit_byte_offset,
              cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots, pairTheory.SND] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sc func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `(!x. slot = Var x ==> not_fresh_at a x) /\
   (!x. ms = Var x ==> not_fresh_at a x) /\
   (!x. ms = Var x \/ ds = Var x ==> not_fresh_at b x)` by
    metis_tac[store_slots_lit_offset_fresh, typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_lit_byte_offset src _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac store_slots_lit_offset_path_mem) >>
  disch_then (qspecl_then [`s`, `sw`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q1` strip_assume_tac) >>
  `eval_operand slot q1 = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  qpat_assum `compile_lit_byte_offset slot _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac store_slots_lit_offset_path_mem) >>
  disch_then (qspecl_then [`q1`, `dw`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q2` strip_assume_tac) >>
  `eval_operand ms q2 = SOME (sw + n2w mo)` by
    metis_tac[typed_copy_state_frame_operand] >>
  `w2n (sw + n2w mo) = w2n sw + mo` by
    (irule typed_copy_offset_nonwrap >> decide_tac) >>
  `w2n (dw + n2w so) + type_slot_size tv <= dimword (:256)` by
    (simp[word_add_def, w2n_n2w] >>
     mp_tac (Q.INST [`x` |-> `so + w2n (dw:bytes32)`, `y` |-> `dimword (:256)`]
       arithmeticTheory.MOD_LESS_EQ) >> simp[] >> decide_tac) >>
  `q2.vs_call_ctx = s.vs_call_ctx` by
    (fs[typed_copy_state_frame_def, venom_state_component_equality]) >>
  `?t ks. gas_marked_path T ctx func q2 0 (OK t) /\
    store_copy_normalize q2 t =
      FOLDL (\q j. (if tr then tstore else sstore) ((dw + n2w so) + n2w j)
        (mload (w2n sw + mo + 32*j) q2) q) q2 ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at b x ==> lookup_var x t = lookup_var x q2) /\
    t.vs_allocas = q2.vs_allocas /\ t.vs_memory = q2.vs_memory /\
    t.vs_labels = q2.vs_labels /\ t.vs_call_ctx = q2.vs_call_ctx /\
    t.vs_alloca_next = q2.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts` by
    (first_x_assum (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
     disch_then (qspecl_then [`func`, `q2`, `sw + n2w mo`, `dw + n2w so`, `writes`] mp_tac) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  suspend "compose"
QED
Resume store_slots_member_offset_run_mem[compose]:
  `gas_marked_path T ctx func s 0 (OK q2)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `q1` >> simp[]) >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
     qexists_tac `q2` >> simp[]) >>
  `!dst len. typed_copy_state_frame sa dst len s q2` by
    metis_tac[typed_copy_state_frame_trans, typed_copy_state_frame_mono] >>
  `!x. not_fresh_at sa x ==> not_fresh_at b x` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qexistsl_tac [`t`, `ks`] >> simp[] >>
  reverse conj_tac
  >- (fs[typed_copy_state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  `store_copy_normalize s q2 = s` by
    (fs[typed_copy_state_frame_def, store_copy_normalize_def,
        venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `store_copy_normalize q2 t = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[store_slots_normalize_fold] >>
  simp[store_copy_normalize_def, mload_def]
QED
Finalise store_slots_member_offset_run_mem

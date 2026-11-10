(* Counted memory-safe sparse array stores. *)
Theory storeSlotsCountedArrays
Ancestors
  storeSlotsCountedElements placeStoreSlots context compileEnv fragGasMode
  stmtSimStoreCopy valueEncoding valueEncodingProps valueEncodingProofs
  vyperValue vyperTyping venomState words arithmetic list rich_list finite_map
  storeSlotsMemoryPaths typedMemoryCopy emitHelperProps exprLoweringProps
  instMemFrontier venomExecSemantics venomInst fragExec emitHelper memSafeRun
  fragGasSeqMem fragExecMem

Theorem store_slots_sarray_run_mem:
  !cenv ctx elem etv n sparse src slot tr sa sb func s sw dw writes.
    compile_store_slots cenv src slot (ArrayT elem (Fixed n)) tr sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    is_abi_dynamic cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
    type_memory_bytes cenv elem = type_memory_size etv /\
    (!v src slot tr sa sb func s sw dw writes.
      value_has_type etv v /\
      compile_store_slots cenv src slot elem tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory etv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size etv < dimword (:256) /\
      w2n sw + type_memory_size etv <= s.vs_alloca_next /\
      w2n dw + type_slot_size etv <= dimword (:256) /\
      encode_value etv v = SOME writes /\
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
    value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse)) /\
    encode_value (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse)) = SOME writes /\
    (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    val_in_memory (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse)) (w2n sw) s.vs_memory /\
    n < dimword (:256) /\
    w2n sw + type_memory_size (ArrayTV etv (Fixed n)) < dimword (:256) /\
    w2n sw + type_memory_size (ArrayTV etv (Fixed n)) <= s.vs_alloca_next /\
    w2n dw + type_slot_size (ArrayTV etv (Fixed n)) <= dimword (:256) /\
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_bytestring_type_def] >> strip_tac >>
  `!i. i < n ==>
    value_has_type etv (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)` by
    (rpt strip_tac >> Cases_on `ALOOKUP sparse i` >>
     simp[default_value_well_typed] >>
     fs[value_has_type_def] >> metis_tac[sparse_has_type_lookup]) >>
  `!i. i < n ==>
    val_in_memory etv (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)
      (w2n sw + i * type_memory_size etv) s.vs_memory` by
    (gvs[val_in_memory_sarray] >> rpt strip_tac >>
     Cases_on `ALOOKUP sparse i` >> simp[] >> metis_tac[kvs_in_memory_lookup]) >>
  drule store_slots_elements_run_mem >>
  disch_then (qspecl_then [`ctx`, `etv`,
    `\i. case ALOOKUP sparse i of NONE => default_value etv | SOME v => v`,
    `n`, `func`, `s`, `sw`, `dw`] mp_tac) >>
  (impl_tac >-
    (simp[eval_operand_def, type_memory_size_def, type_slot_size_def] >>
     reverse conj_tac
     >- (fs[type_memory_size_def, type_slot_size_def] >> metis_tac[]) >>
     gen_tac >> strip_tac >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_x_assum `!v src slot tr sa sb func s sw dw writes. _`
           (qspec_then `case ALOOKUP sparse r of NONE => default_value etv | SOME v => v` mp_tac) >>
         simp[] >> disch_then irule >> simp[] >> metis_tac[]) >>
     metis_tac[value_has_type_equiv])) >>
  strip_tac >> qexistsl_tac [`t`, `ks`] >> simp[] >>
  drule_all store_slots_sarray_support >> simp[ADD_COMM]
QED

Theorem store_slots_dyn_prefix_path_mem[local]:
  emit_op MLOAD [src] sa = (cnt,s1) /\
  emit_op ADD [src; Lit 32w] s1 = (data,s2) /\
  emit_op ADD [slot; Lit 1w] s2 = (dst,sc) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  w2n sw + 32 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p. gas_marked_path T ctx func s 0 (OK p) /\
    store_copy_normalize s p = s /\
    eval_operand cnt p = SOME (mload (w2n sw) s) /\
    eval_operand data p = SOME (sw + 32w) /\
    eval_operand dst p = SOME (dw + 1w) /\
    eval_operand slot p = SOME dw /\
    (!x. not_fresh_at sa x ==> lookup_var x p = lookup_var x s) /\
    p.vs_allocas = s.vs_allocas /\ p.vs_memory = s.vs_memory /\
    p.vs_labels = s.vs_labels /\ p.vs_call_ctx = s.vs_call_ctx /\
    p.vs_alloca_next = s.vs_alloca_next /\
    ~p.vs_halted /\ p.vs_current_bb = sc.cs_current_bb /\
    p.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >> imp_res_tac typed_copy_emit_op_mono >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sc` by gvs[ci_mono_def] >>
  `cs_extends s1 sc` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sc func` by
    metis_tac[fn_has_code_split] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [src] [out]) s =
    OK (update_var out (mload (w2n sw) s) s)` by
    (gen_tac >> irule step_MLOAD >> simp[eval_operands_def]) >>
  `!out. inst_mem_below_frontier (mk_inst sa.cs_next_id MLOAD [src] [out]) s /\
    inst_dload_in_section (mk_inst sa.cs_next_id MLOAD [src] [out]) s` by
    simp[below_frontier_MLOAD, eval_operands_def, inst_dload_in_section_def, mk_inst_def] >>
  drule (Q.INST [`opc` |-> `MLOAD`] store_slots_emit_op_path_mem) >>
  disch_then (qspecl_then [`mload (w2n sw) s`, `s`, `func`, `ctx`] mp_tac) >>
  simp[is_terminator_def] >>
  strip_tac >>
  rename1 `gas_marked_path T ctx func s 0 (OK u)` >>
  qpat_x_assum `!off len. typed_copy_state_frame sa off len s u`
    (qspecl_then [`0`,`0`] assume_tac) >>
  `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  suspend "adds"
QED

Resume store_slots_dyn_prefix_path_mem[adds]:
  `!out. step_inst_base (mk_inst s1.cs_next_id ADD [src; Lit 32w] [out]) u =
    OK (update_var out (sw + 32w) u)` by
    (gen_tac >> irule step_ADD >> simp[eval_operand_def]) >>
  `!out. inst_mem_below_frontier (mk_inst s1.cs_next_id ADD [src; Lit 32w] [out]) u /\
    inst_dload_in_section (mk_inst s1.cs_next_id ADD [src; Lit 32w] [out]) u` by
    simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def] >>
  qpat_assum `emit_op ADD [src; Lit 32w] s1 = _`
    (mp_then Any mp_tac store_slots_emit_op_path_mem) >>
  disch_then (qspecl_then [`sw + 32w`, `u`, `func`, `ctx`] mp_tac) >>
  simp[is_terminator_def] >> strip_tac >>
  rename1 `gas_marked_path T ctx func u 0 (OK w)` >>
  qpat_x_assum `!off len. typed_copy_state_frame s1 off len u w`
    (qspecl_then [`0`,`0`] assume_tac) >>
  `!x. slot = Var x ==> not_fresh_at s1 x` by
    (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `eval_operand slot w = SOME dw` by metis_tac[typed_copy_state_frame_operand] >>
  `!out. step_inst_base (mk_inst s2.cs_next_id ADD [slot; Lit 1w] [out]) w =
    OK (update_var out (dw + 1w) w)` by
    (gen_tac >> irule step_ADD >> simp[eval_operand_def]) >>
  `!out. inst_mem_below_frontier (mk_inst s2.cs_next_id ADD [slot; Lit 1w] [out]) w /\
    inst_dload_in_section (mk_inst s2.cs_next_id ADD [slot; Lit 1w] [out]) w` by
    simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def] >>
  qpat_assum `emit_op ADD [slot; Lit 1w] s2 = _`
    (mp_then Any mp_tac store_slots_emit_op_path_mem) >>
  disch_then (qspecl_then [`dw + 1w`, `w`, `func`, `ctx`] mp_tac) >>
  simp[is_terminator_def] >> strip_tac >>
  suspend "compose"
QED

Resume store_slots_dyn_prefix_path_mem[compose]:
  rename1 `gas_marked_path T ctx func w 0 (OK t)` >>
  qpat_x_assum `!off len. typed_copy_state_frame s2 off len w t`
    (qspecl_then [`0`,`0`] assume_tac) >>
  `!x. cnt = Var x ==> not_fresh_at s1 x` by metis_tac[typed_copy_emit_op_fresh] >>
  `!x. data = Var x \/ cnt = Var x \/ slot = Var x ==> not_fresh_at s2 x` by
    (imp_res_tac typed_copy_emit_op_fresh >>
     gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `eval_operand cnt w = SOME (mload (w2n sw) s)` by
    metis_tac[typed_copy_state_frame_operand] >>
  `eval_operand cnt t = SOME (mload (w2n sw) s) /\
   eval_operand data t = SOME (sw + 32w) /\ eval_operand slot t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `typed_copy_state_frame sa 0 0 s t` by
    metis_tac[typed_copy_state_frame_mono, typed_copy_state_frame_trans] >>
  qexists_tac `t` >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `u` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `w` >> simp[]) >>
  gvs[typed_copy_state_frame_def, store_copy_normalize_def, venom_state_component_equality]
QED
Finalise store_slots_dyn_prefix_path_mem

Theorem store_slots_emit_slot_path_mem[local]:
  emit_void (if tr then TSTORE else SSTORE) [dst;src] sa = ((),sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME w ==>
  gas_marked_path T ctx func s 0
    (OK (((if tr then tstore else sstore) dw w s)
      with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  reverse conj_tac >- simp[] >>
  irule store_slots_emitted_seq_path_mem >> conj_tac >- simp[] >>
  qexists_tac `sa` >> Cases_on `tr` >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_def, exec_write2_def, eval_operands_def,
       run_inst_seq_mem_ok_last, below_frontier_no_ranges,
       inst_dload_in_section_def]
QED

Theorem store_slots_dynarray_run_mem:
  !cenv ctx elem etv n l src slot tr sa sb func s sw dw writes.
    compile_store_slots cenv src slot (ArrayT elem (Dynamic n)) tr sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    type_memory_bytes cenv elem = type_memory_size etv /\
    (!v src slot tr sa sb func s sw dw writes.
      value_has_type etv v /\
      compile_store_slots cenv src slot elem tr sa = ((),sb) /\
      (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
      eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
      val_in_memory etv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size etv < dimword (:256) /\
      w2n sw + type_memory_size etv <= s.vs_alloca_next /\
      w2n dw + type_slot_size etv <= dimword (:256) /\
      encode_value etv v = SOME writes /\
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
    value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV l)) /\
    encode_value (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV l)) = SOME writes /\
    (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    val_in_memory (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV l)) (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size (ArrayTV etv (Dynamic n)) < dimword (:256) /\
    w2n sw + type_memory_size (ArrayTV etv (Dynamic n)) <= s.vs_alloca_next /\
    w2n dw + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword (:256) /\
    0 < type_slot_size etv /\ 0 < n /\
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, is_abi_dynamic_def,
       is_bytestring_type_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, AllCaseEqs()] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op MLOAD [src] sa = (cnt,s1)` >>
  rename1 `emit_op ADD [src; Lit 32w] s1 = (data,s2)` >>
  rename1 `emit_op ADD [slot; Lit 1w] s2 = (dst,sc)` >>
  rename1 `emit_void (if tr then TSTORE else SSTORE) [slot; cnt] se = ((),sb)` >>
  Cases_on `_0` >> imp_res_tac typed_copy_emit_op_mono >>
  `ci_mono sc se` by
    (mp_tac (cj 3 stmtLoweringMonoTheory.ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`,`data`,`dst`,`elem`,`cnt`,`tr`,`sc`] mp_tac) >> simp[]) >>
  `ci_mono se sb` by
    (mp_tac (Q.SPECL [`if tr then TSTORE else SSTORE`,`[slot; cnt]`,`se`]
      ci_mono_emit_void) >> simp[]) >>
  `cs_extends sa sc /\ cs_extends sc se /\ cs_extends se sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sc func /\ fn_has_code sc se func /\ fn_has_code se sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `w2n sw + 32 <= s.vs_alloca_next` by
    (fs[type_memory_size_def] >> decide_tac) >>
  drule_all store_slots_dyn_prefix_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path T ctx func s 0 (OK p)` >>
  suspend "elements"
QED

Resume store_slots_dynarray_run_mem[elements]:
  `mload (w2n sw) s = n2w (LENGTH l) /\
   elems_in_memory l (w2n sw + 32) etv s.vs_memory` by
    gvs[val_in_memory_dynarray, mem_word_at_eq_mload] >>
  `!i. i < LENGTH l ==> value_has_type etv (EL i l) /\
    IS_SOME (encode_value etv (EL i l)) /\
    val_in_memory etv (EL i l) (w2n sw + 32 + i * type_memory_size etv) p.vs_memory` by
    (gen_tac >> strip_tac >> conj_tac
     >- gvs[value_has_type_def, all_have_type_EVERY, EVERY_EL] >>
     conj_tac
     >- (irule store_slots_dyn_element_encoded >>
         gvs[Once vyperStorageTheory.encode_value_def, AllCaseEqs()] >> metis_tac[]) >>
     drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
     metis_tac[ADD_ASSOC]) >>
  `LENGTH l <= n /\ 0 < n` by gvs[value_has_type_def] >>
  `LENGTH l * type_slot_size etv <= n * type_slot_size etv /\
   LENGTH l <= LENGTH l * type_slot_size etv` by simp[] >>
  `w2n sw + 32 + LENGTH l * type_memory_size etv < dimword (:256) /\
   w2n sw + 32 + LENGTH l * type_memory_size etv <= p.vs_alloca_next /\
   w2n dw + 1 + LENGTH l * type_slot_size etv <= dimword (:256) /\
   LENGTH l < dimword (:256) /\ w2n sw + 32 < dimword (:256)` by
    (qpat_x_assum `w2n sw + type_memory_size _ < _` mp_tac >>
     qpat_x_assum `w2n sw + type_memory_size _ <= _` mp_tac >>
     qpat_x_assum `w2n dw + type_slot_size _ <= _` mp_tac >>
     pure_rewrite_tac[type_memory_size_slots, type_slot_size_def, LEFT_ADD_DISTRIB, MULT_ASSOC] >>
     rpt strip_tac >> pure_rewrite_tac[type_memory_size_slots, MULT_ASSOC] >> decide_tac) >>
  `0 < n * type_slot_size etv` by simp[] >>
  `w2n dw + 1 < dimword (:256)` by
    (qpat_x_assum `w2n dw + type_slot_size _ <= _` mp_tac >>
     pure_rewrite_tac[type_slot_size_def] >> decide_tac) >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 1w) = w2n dw + 1` by
    gvs[wordsTheory.word_add_def, wordsTheory.dimword_def] >>
  `!x. data = Var x \/ dst = Var x \/ cnt = Var x \/ slot = Var x ==>
       not_fresh_at sc x` by metis_tac[store_slots_dyn_prefix_fresh] >>
  suspend "loop"
QED

Resume store_slots_dynarray_run_mem[loop]:
  drule store_slots_elements_run_mem >>
  disch_then (qspecl_then [`ctx`, `etv`, `\i. EL i (l:value list)`,
    `LENGTH (l:value list)`, `func`, `p`, `sw + 32w`, `dw + 1w`] mp_tac) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (gen_tac >> strip_tac >> conj_tac
         >- (rpt gen_tac >> strip_tac >>
             qpat_x_assum `!v src slot tr sa sb func s sw dw writes. _`
               (qspec_then `EL r l` mp_tac) >> simp[] >>
             disch_then irule >> simp[] >> metis_tac[]) >> gvs[]) >>
     metis_tac[])) >> strip_tac >>
  suspend "header"
QED

Resume store_slots_dynarray_run_mem[header]:
  rename1 `gas_marked_path T ctx func p 0 (OK u)` >>
  `eval_operand slot u = SOME dw /\
   eval_operand cnt u = SOME (mload (w2n sw) s)` by
    (conj_tac
     >- (Cases_on `slot` >> gvs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `cnt` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by metis_tac[] >>
  drule_all store_slots_emit_slot_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "finish"
QED

Resume store_slots_dynarray_run_mem[finish]:
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func u 0 (OK t)` >>
  `store_copy_normalize u t =
    (if tr then tstore else sstore) dw (mload (w2n sw) s) u` by
    (Cases_on `tr` >>
     simp[Abbr `t`, store_copy_normalize_def, sstore_def, tstore_def,
          venom_state_component_equality]) >>
  `store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
      (mload (w2n sw + 32*j) s) q) s (MAP SUC ks ++ [0])` by
    (irule store_slots_dyn_fold_header >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  qexistsl_tac [`t`, `MAP SUC ks ++ [0]`] >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `p` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `u` >> simp[]) >>
  conj_tac >- (qpat_x_assum `store_copy_normalize s t = _` mp_tac >>
                 simp[Once ADD_COMM]) >>
  conj_tac >- suspend "support" >>
  suspend "frame"
QED

Resume store_slots_dynarray_run_mem[support]:
  drule store_slots_dynarray_encoding_support >> strip_tac >>
  simp[MEM_APPEND, MEM_MAP] >>
  qpat_x_assum `!k. MEM k ks <=> _` mp_tac >>
  BETA_TAC >> rpt strip_tac >>
  eq_tac >> strip_tac >> gvs[] >>
  metis_tac[ADD1, ADD_ASSOC]
QED

Resume store_slots_dynarray_run_mem[frame]:
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[] >>
  Cases_on `tr` >>
  simp[Abbr `t`, sstore_def, tstore_def, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED
Finalise store_slots_dynarray_run_mem

(* Same-type materialization uses no heterogeneous layout metadata. *)
Theory bodyFullAbiEncodeStoreExec
Ancestors
  logStoreDataOriginPtr bodyFullAllocGeneric typedCopyOriginPtrBytes
  typedMemoryCopy robustCopyTransportPtr representationCleanPtr
  valueCopy valueEncoding valueEncodingDefs exprSimProps context compileEnv
  bodyPtrDefs ptrDiscipline fragGasOriginPtr fragExec rich_list bodyFullPathHistory
  allocaHistory bodyFullAbiEncodeCopy assignTuplePtrCopyEndpoint
  emitHelper instMemFrontier memSafeRun unitTransformDefs contextCodegenRel

Theorem same_type_store_core[local]:
  compile_store_memory cenv (Var xs) (Var xd) ty ty sa = ((),sb) /\
  ~is_word_type ty /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (type_memory_size tv = 0 \/ w2n dw + type_memory_size tv <= s.vs_alloca_next) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory tv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytes" >>
  `compile_copy_memory (Var xd) (Var xs) (type_memory_size tv) sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_store_memory_def] >> metis_tac[]) >>
  Cases_on `type_memory_size tv = 0`
  >- suspend "bulk_zero" >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY
    [Var xd; Var xs; Lit (n2w (type_memory_size tv))] []` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
   sb.cs_blocks = sa.cs_blocks` by
    (qpat_x_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
     Cases_on `type_memory_size tv` >>
     simp[contextTheory.compile_copy_memory_def, emit_void_def, emit_inst_def,
          comp_bind_def, fresh_id_def, emit_def, comp_return_def, Abbr `inst`] >>
     strip_tac >> gvs[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN]) >>
  `w2n (n2w (type_memory_size tv):256 word) = type_memory_size tv` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  qabbrev_tac `sc = mcopy (w2n dw) (w2n sw) (type_memory_size tv) s` >>
  qabbrev_tac `tf = step_taint inst s sc tn` >>
  qexistsl_tac [`sc with vs_inst_idx := SUC s.vs_inst_idx`, `G`, `tf`] >>
  conj_tac >- suspend "bulk_path" >>
  `!mem. mem_agree_outside tf.t_mem sc.vs_memory mem ==>
     val_in_memory tv v (w2n dw) mem` by
    (simp[Abbr `tf`, Abbr `inst`, Abbr `sc`, NoAsms] >>
     mp_tac (Q.INST [`n` |-> `n2w (type_memory_size tv)`,
                      `dst` |-> `Var xd`, `src` |-> `Var xs`,
                      `count_op` |-> `Lit (n2w (type_memory_size tv))`]
                     mcopy_staged_robust_ptr |> Q.GENL [`a`, `b`, `id`]) >>
     simp[venomStateTheory.eval_operand_def] >>
     disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
     simp[val_footprint_le]) >>
  suspend "bulk_post"
QED

Resume same_type_store_core[bytes]:
  `compile_store_bytestring (Var xs) (Var xd) sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_store_memory_def]) >>
  drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >>
  gvs[] >> Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  FIRST [rename1 `BytesV bs` >> qabbrev_tac `len = LENGTH bs`,
         rename1 `StringV str` >> qabbrev_tac `len = STRLEN str`] >>
  `word_size len <= word_size n` by
    (irule word_size_monotone >> simp[Abbr `len`]) >>
  gvs[valueEncodingTheory.type_memory_size_def] >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next` by decide_tac >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by
    (qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _`
       (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, val_in_memory_def, Abbr `len`]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w len` by
    (rpt strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
     simp[val_in_memory_def, Abbr `len`]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  `mload (w2n sw) s = n2w len` by
    gvs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `ptr_covers G tn xs s (32 + 32 * word_size len) /\
   ptr_covers G tn xd s (32 + 32 * word_size len)` by
    (gvs[ptr_covers_def] >> conj_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  `len + 31 < dimword (:256)` by
    (`len + 31 < ((len + 31) DIV 32 + 1) * 32` by
       simp[GSYM arithmeticTheory.DIV_LE_X] >>
     qpat_x_assum `32 + 32 * word_size len < _` mp_tac >>
     pure_rewrite_tac[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule bodyCopyMemoryBaseTheory.compile_store_bytestring_body_mem_ok >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`dw`, `Var xd`, `Var xs`] >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  drule store_bytestring_run_exact >>
  disch_then (qspecl_then [`s`, `sw`, `dw`, `len`] mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, exprLoweringPropsTheory.same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  drule_all (SRULE [GSYM vfmConstantsTheory.word_size_def]
    (Q.INST [`n` |-> `32 + 32 * word_size len`]
      (SPEC_ALL compile_store_bytestring_origin_ptr_path))) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  gvs[] >>
  qexistsl_tac [`sf with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)`,
                `Gf`, `tnf`] >> simp[] >>
  (conj_tac >- suspend "value" >>
   conj_tac >- suspend "frame" >>
   conj_tac >- gvs[venomStateTheory.venom_state_component_equality] >>
   conj_tac >- gvs[venomStateTheory.venom_state_component_equality,
                   exprLoweringPropsTheory.same_blocks_def] >>
   conj_tac >- suspend "exterior" >>
   suspend "robust")
QED

Resume same_type_store_core[value]:
  markerLib.RESUME_TAC >> irule mcopy_val_in_memory >>
  simp[loweringPostsTheory.val_footprint_def, Abbr `len`, le_word_size_mul] >>
  qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _`
    (qspec_then `s.vs_memory` mp_tac) >>
  simp[mem_agree_outside_def, val_in_memory_def]
QED

Resume same_type_store_core[frame]:
  markerLib.RESUME_TAC >> simp[typed_copy_state_frame_def] >>
  (conj_tac >- gvs[venomStateTheory.venom_state_component_equality] >>
   conj_tac >- (simp[venomStateTheory.lookup_var_def] >>
                 gvs[venomStateTheory.lookup_var_def]) >>
   simp[typed_copy_frame_def] >> conj_tac
   >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
   simp[venomExecSemanticsTheory.mcopy_def,
        immutableMemoryFrameTheory.immutable_write_memory_capacity, arithmeticTheory.MAX_DEF])
QED

Resume same_type_store_core[exterior]:
  markerLib.RESUME_TAC >> rpt strip_tac >> simp[] >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

Resume same_type_store_core[robust]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  irule robust_val_in_memory_copy_transport >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `32 * word_size len + 32`, `w2n sw`, `tn.t_mem`] >>
  (conj_tac
   >- (rpt strip_tac >>
       qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
       simp[val_in_memory_def, Abbr `len`]) >>
   conj_tac >- (rpt strip_tac >> simp[] >> decide_tac) >>
   conj_tac >- simp[loweringPostsTheory.val_footprint_def, Abbr `len`, le_word_size_mul] >>
   simp[valueEncodingDefsTheory.mem_bytes_at_def, venomMemPropsTheory.mcopy_padded_read])
QED

Resume same_type_store_core[bulk_zero]:
  gvs[contextTheory.compile_copy_memory_def, comp_return_def] >>
  `val_footprint tv v = 0` by (drule val_footprint_le >> simp[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n sw`,
                   `tn.t_mem`, `tn.t_mem`] >>
     simp[mem_bytes_at_def, val_footprint_le]) >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[typed_copy_state_frame_def] >>
  conj_tac >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  gvs[mem_agree_outside_def, venomStateTheory.venom_state_component_equality]
QED

Resume same_type_store_core[bulk_path]:
  gen_tac >> simp[Abbr `tf`, Abbr `sc`, Abbr `inst`] >>
  drule_at (Pat `get_instruction _ _ = _`) abi_encode_mcopy_origin_path >>
  simp[venomStateTheory.eval_operand_def, op_taint_def] >>
  disch_then irule >> simp[] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, codegenRelTheory.sized_source_write_range_def,
       venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Resume same_type_store_core[bulk_post]:
  `tf.t_imm = tn.t_imm /\ tf.t_var = tn.t_var /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem))` by
    (unabbrev_all_tac >>
     mp_tac (Q.INST [`dst` |-> `Var xd`, `src` |-> `Var xs`,
                     `count_op` |-> `Lit (n2w (type_memory_size tv))`]
                    (SPEC_ALL typedCopyPtrTheory.mcopy_operand_ghost_frame) |>
             Q.GENL [`a`, `b`, `n`, `id`]) >>
     simp[venomStateTheory.eval_operand_def] >>
     disch_then (qspec_then `sa.cs_next_id` strip_assume_tac) >>
     conj_tac
     >- simp[step_taint_def, imm_taint_def, venomInstTheory.mk_inst_def] >>
     simp[] >> rpt strip_tac >> gvs[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `!mem. mem_agree_outside tf.t_mem _ mem ==> _`
        (qspec_then `sc.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
  conj_tac >- (simp[Abbr `sc`] >> irule typed_copy_mcopy_state_frame) >>
  simp[Abbr `sc`, venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def, op_taint_def]
QED

Finalise same_type_store_core

Theorem abi_encode_same_type_store_origin:
  compile_store_memory cenv (Var xs) (Var xd) ty ty sa = ((),sb) /\
  ~is_word_type ty /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (type_memory_size tv = 0 \/ w2n dw + type_memory_size tv <= s.vs_alloca_next) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory tv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    lookup_var xd t = SOME dw /\ alloca_history func t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all same_type_store_core >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >> conj_tac
  >- gvs[typed_copy_state_frame_def] >>
  metis_tac[body_full_path_alloca_history]
QED

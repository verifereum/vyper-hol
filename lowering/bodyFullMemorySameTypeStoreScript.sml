(* Same-layout stores retain one endpoint for all dead masks, even when
   source and destination overlap. Bytestrings read only their stored size. *)
Theory bodyFullMemorySameTypeStore
Ancestors
  bodyFullMemoryCopy bodyFullAllocGeneric bodyDeclMemoryCore
  bodyPtrIfExpCopyHeader representationCleanPtr reasonCopySourcePtr robustCopyTransportPtr
  exprSimBufferStore valueCopy valueCopyBytes typedMemoryCopy
  context compileEnv bodyPtrDefs fragGasOriginPtr bytesCopyCode fragExec
  contextCodegenRel exprLoweringProps
  valueEncoding valueEncodingDefs valueEncodingProps exprSimProps
  venomState venomExecSemantics finite_map pred_set list rich_list words
  arithmetic vfmConstants immutableMemoryFrame

Theorem body_full_memory_same_type_store_path:
  compile_store_memory cenv (Var xs) (Var xd) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  value_has_type tv v /\ val_wf tv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size tv) /\
  ptr_covers G tn xd s (type_memory_size tv) /\
  w2n sw + val_store_size tv v < dimword (:256) /\
  w2n dw + type_memory_size tv < dimword (:256) /\
  w2n sw + val_store_size tv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
    t.vs_prev_bb = s.vs_prev_bb /\ t.vs_current_bb = s.vs_current_bb /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size tv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytestring" >>
  `val_store_size tv v = type_memory_size tv` by suspend "flat_size" >>
  `compile_copy_memory (Var xd) (Var xs) (type_memory_size tv) sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  irule body_full_memory_copy_frame_path >> simp[] >>
  qexistsl_tac [`sw`,`xd`,`xs`] >> gvs[]
QED

Resume body_full_memory_same_type_store_path[flat_size]:
  metis_tac[bodyDeclMemoryCoreTheory.val_store_size_non_bytestring]
QED

Resume body_full_memory_same_type_store_path[bytestring]:
  `?len. mload (w2n sw) s = n2w len /\
    val_store_size tv v = 32 + 32 * word_size len` by
    metis_tac[buffer_typed_bytestring_header] >>
  `compile_store_bytestring (Var xs) (Var xd) sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  `len <= 32 * word_size len` by
    (rewrite_tac[word_size_def] >> qspec_then `32` mp_tac DIVISION >>
     (impl_tac >- simp[]) >>
     disch_then (qspec_then `len + 31` strip_assume_tac) >> decide_tac) >>
  `(!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn.t_mem)` by
    suspend "header" >>
  `eval_operand (Var xs) s = SOME sw /\ eval_operand (Var xd) s = SOME dw /\
   (!x. Var xs = Var x \/ Var xd = Var x ==> not_fresh_at sa x)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all body_typed_store_memory_mem_ok >> simp[]) >>
  `ptr_covers G tn xs s (val_store_size tv v) /\
   ptr_covers G tn xd s (val_store_size tv v)` by
    metis_tac[ptr_covers_mono] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    suspend "code" >>
  `len+31 < dimword (:256) /\ val_store_size tv v < dimword (:256)` by decide_tac >>
  `val_store_size tv v = 32 + 32 * ((len+31) DIV 32)` by simp[GSYM word_size_def] >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "finish"
QED

Resume body_full_memory_same_type_store_path[header]:
  drule_all bytestring_type_value >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  FIRST [drule robust_val_in_memory_bytes_clean,
         drule robust_val_in_memory_string_clean] >> simp[]
QED
Resume body_full_memory_same_type_store_path[code]:
  drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED
Resume body_full_memory_same_type_store_path[finish]:
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  drule_all buffer_store_bytestring_run >> strip_tac >>
  gvs[] >> rename1 `run_inst_seq (emitted_insts sa sb) s = OK sf` >>
  `!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv v (w2n dw) mem` by suspend "robust" >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   same_blocks sa sb` by metis_tac[bytesCopyCodeTheory.compile_store_bytestring_code] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by simp[] >>
  qexistsl_tac [`sf with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tnf`] >>
  simp[] >>
  conj_tac >- (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  conj_tac >- suspend "frame" >>
  conj_tac >- (gvs[venom_state_component_equality]) >>
  conj_tac >- (gvs[venom_state_component_equality]) >>
  conj_tac >- (gvs[venom_state_component_equality]) >>
  conj_tac >- (gvs[venom_state_component_equality, same_blocks_def]) >>
  rpt conj_tac
  >- suspend "exterior" >> gvs[lookup_var_def]
QED
Resume body_full_memory_same_type_store_path[robust]:
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- metis_tac[val_footprint_le_store_size] >>
  qexistsl_tac [`s.vs_memory`,`sf.vs_memory`,`val_store_size tv v`,`w2n sw`,
    `tn.t_mem`,`tnf.t_mem`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "copied_taint" >>
  conj_tac >- metis_tac[val_footprint_le_store_size] >>
  simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_same]
QED
Resume body_full_memory_same_type_store_path[frame]:
  simp[typed_copy_state_frame_def] >>
  conj_tac >- gvs[venom_state_component_equality] >>
  gvs[lookup_var_def,typed_copy_frame_def] >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[mcopy_def,immutable_write_memory_capacity,MAX_DEF]
QED
Resume body_full_memory_same_type_store_path[exterior]:
  qpat_x_assum `tnf.t_mem = _` SUBST1_TAC >>
  rw[EQ_IMP_THM] >> gvs[] >> decide_tac
QED

Resume body_full_memory_same_type_store_path[copied_taint]:
  qpat_x_assum `tnf.t_mem = _` SUBST1_TAC >>
  rpt strip_tac >> simp[] >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

Finalise body_full_memory_same_type_store_path

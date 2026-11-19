Theory bodyFullIntCallBufferedCopy
Ancestors
  bodySimFull bodyFullMemorySameTypeStore bodyFullMemoryStore
  reasonEndpointResourcesPtr externalNormalizePremises valueCopyBytes
  loweringStateRelDefs reasonCopySourcePtr typedMemoryCopy

Theorem intcall_widened_return_source_disjoint:
  return_buf_sep (SOME (bw,capacity)) cenv es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  eval_operand op s = SOME src /\ 0 < type_memory_size tv ==>
  w2n src + type_memory_size tv <= w2n bw \/ w2n bw + capacity <= w2n src
Proof
  strip_tac >>
  drule_all normalize_nonbytes_footprint >> strip_tac >>
  `type_memory_size tv <= val_footprint tv v` by simp[] >>
  drule_all (Q.INST [`n` |-> `type_memory_size tv`]
    (SPEC_ALL expr_val_at_region_prefix)) >>
  strip_tac
  >- (disj2_tac >>
      qpat_assum `return_buf_sep _ _ _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
      rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
      disch_then (fn th =>
        qpat_assum `FLOOKUP s.vs_allocas aid = _` (mp_tac o MATCH_MP th)) >>
      decide_tac) >>
  qpat_assum `return_buf_sep _ _ _ _`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [return_buf_sep_def]) >>
  disch_then drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* The result still uses the inner result's length, even when the enclosing
   function returns a larger bytestring type. *)
Theorem intcall_widened_bytes_return_copy:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256) /\
  type_memory_size stv <= type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `~is_word_type sty /\ ~is_word_type dty` by
    metis_tac[is_bytestring_word_type] >>
  `compile_store_memory cenv (Var xs) (Var xd) sty sty sa = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  `ptr_covers G tn xd s (type_memory_size stv)` by
    metis_tac[ptr_covers_mono] >>
  `w2n dw + type_memory_size stv < dimword (:256) /\
   w2n dw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  drule_all body_full_memory_same_type_store_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  conj_tac
  >- (mp_tac (Q.SPECL
        [`tenv`,`sty`,`dty`,`stv`,`dtv`,`v`,`w2n (dw:256 word)`,`t.vs_memory`]
        bytestring_val_in_memory_transfer) >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `mem` >> strip_tac >>
      mp_tac (Q.SPECL
        [`tenv`,`sty`,`dty`,`stv`,`dtv`,`v`,`w2n (dw:256 word)`,`mem`]
        bytestring_val_in_memory_transfer) >> simp[]) >>
  irule typed_copy_state_frame_subinterval >>
  qexistsl_tac [`w2n (dw:256 word)`,`type_memory_size stv`] >> simp[]
QED

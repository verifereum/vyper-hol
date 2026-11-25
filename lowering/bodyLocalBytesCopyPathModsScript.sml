(* A local bytes/string store writes the rounded live representation, not
   the destination's full capacity.  No source binding is installed here. *)
Theory bodyLocalBytesCopyPathMods
Ancestors
  bodyCopyMemoryBase bodyFullAllocGeneric bodyPtrIfExpBytesPost
  bodyPtrIfExpCopyHeader bytesCopyCode context exprLoweringProps
  exprSimBufferStore exprSimProps fragExec fragGasOriginPtr fragGasSeqPtr
  placeMemoryTypedPrimitive rich_list typedMemoryCopy valueCopyBytes
  valueCopy venomState vfmConstants vyperTyping words

Theorem local_bytes_copy_path_mods:
  compile_store_memory ce (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n sw) m) /\
  n = 32 + 32 * word_size len /\ n < dimword (:256) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  ptr_covers G tn xs s n /\ ptr_covers G tn xd s n /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    n <= type_memory_size stv /\ n <= type_memory_size dtv /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n dw) m) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + n) ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
    (lo <= w2n dw ==>
       mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
       !i. i < lo ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n <= type_memory_size stv /\ n <= type_memory_size dtv` by suspend "capacities" >>
  `compile_store_bytestring (Var xs) (Var xd) sa = ((),sb)` by
    fs[compile_store_memory_def] >>
  `len + 31 < dimword (:256)` by
    (`len + 31 < ((len+31) DIV 32 + 1)*32` by
       simp[GSYM arithmeticTheory.DIV_LE_X] >>
     fs[word_size_def] >> decide_tac) >>
  (* The header reads cleanly even when the payload contains tainted bytes. *)
  drule_all robust_bytestring_header >> strip_tac >>
  `eval_operand (Var xs) s = SOME sw /\ eval_operand (Var xd) s = SOME dw /\
   (!x. Var xs = Var x \/ Var xd = Var x ==> not_fresh_at sa x)` by
    (simp[eval_operand_def] >> rpt strip_tac >> gvs[]) >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next` by
    metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all compile_store_bytestring_body_mem_ok >> simp[]) >>
  drule bytesCopyCodeTheory.compile_store_bytestring_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    suspend "prefix" >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[GSYM word_size_def] >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `(sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    (drule_all buffer_store_bytestring_run >> strip_tac >> gvs[]) >>
  drule_all bytestring_copy_effects >> strip_tac >>
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
       val_in_memory dtv v (w2n dw) m` by suspend "destination" >>
  qabbrev_tac `t = sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)` >>
  `typed_copy_state_frame sa (w2n dw) n s t` by suspend "footprint" >>
  `(lo <= w2n dw ==>
       mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
       !i. i < lo ==> (i IN tnf.t_mem <=> i IN tn.t_mem))` by suspend "low_memory" >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  suspend "endpoint"
QED

Resume local_bytes_copy_path_mods[capacities]:
  conj_tac
  >- (qpat_x_assum `is_bytestring_type dty` kall_tac >>
      drule_all bytestring_type_value >> strip_tac >>
      gvs[value_has_type_def,valueEncodingTheory.type_memory_size_def] >>
      irule word_size_monotone >> simp[]) >>
  qpat_x_assum `is_bytestring_type sty` kall_tac >>
  drule_all bytestring_type_value >> strip_tac >>
  gvs[value_has_type_def,valueEncodingTheory.type_memory_size_def] >>
  irule word_size_monotone >> simp[]
QED

Resume local_bytes_copy_path_mods[prefix]:
  gvs[fn_has_code_def,same_blocks_def,rich_listTheory.IS_PREFIX_APPEND] >>
  simp[DROP_APPEND]
QED

Resume local_bytes_copy_path_mods[destination]:
  drule bytestring_copy_robust_destination >>
  disch_then (drule_at (Pat `!m. mem_agree_outside _ _ m ==> val_in_memory _ _ _ m`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `n = 32 + 32 * ((len+31) DIV 32)`)) >>
  disch_then (qspec_then `tnf` mp_tac) >> simp[]
QED

Resume local_bytes_copy_path_mods[footprint]:
  simp[typed_copy_state_frame_def,Abbr `t`,blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  conj_tac >- fs[venom_state_component_equality] >>
  simp[typed_copy_frame_def,mcopy_memory_length] >>
  rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> simp[]
QED

Resume local_bytes_copy_path_mods[low_memory]:
  strip_tac >> conj_tac
  >- (qpat_x_assum `typed_copy_state_frame _ _ _ s t` mp_tac >>
      simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
      strip_tac >> first_x_assum irule >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!i. ~(w2n dw <= i /\ i < w2n dw + n) ==> _` irule >>
  decide_tac
QED

Resume local_bytes_copy_path_mods[endpoint]:
  simp[Abbr `t`,blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  fs[venom_state_component_equality,same_blocks_def]
QED

Finalise local_bytes_copy_path_mods

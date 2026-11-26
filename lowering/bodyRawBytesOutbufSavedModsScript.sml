(* The input to the raw byte call is retained by the physical GAS/outbuf prefix. *)
Theory bodyRawBytesOutbufSavedMods
Ancestors
  stateRelProj bodyMemoryDefs vyperStorageFootprint rawCallOutbufCompile
  bodyPtrDefs freshWrites
  exprLoweringProps exprSafeOperand assignTuplePtrCopyLen
  representationCleanPtr memoryReadProps
  loweringStateRelDefs venomMemDefs venomState ptrDiscipline words list finite_map

Theorem raw_bytes_outbuf_old_bounds_mods:
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  s0.vs_alloca_next <= tk.vs_alloca_next ==>
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off + sz <= tk.vs_alloca_next) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    b + sz <= tk.vs_alloca_next)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then assume_tac) >>
  conj_tac
  >- (rpt strip_tac >> drule stmt_state_rel_local_ptrs_alloca >>
      simp[alloca_inv_def,alloca_next_valid_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  rpt strip_tac >> drule_all body_local_region_frontier >> decide_tac
QED

Triviality outbuf_compile_operands:
  compile_raw_call_outbuf M s6 = ((ov,op),sout) ==>
  safe_operand sout ov /\ safe_operand sout op
Proof
  strip_tac >> drule calldata_outbuf_compile >> strip_tac >>
  Cases_on `M = 0` >> gvs[]
  >- metis_tac[alloc_buffer_safe_operand] >>
  reverse conj_tac
  >- metis_tac[emit_op_safe_operand] >>
  irule safe_operand_mono >> rename1 `emit_op ADD _ sm = _` >>
  qexists_tac `sm` >> conj_tac
  >- (qspecl_then [`ADD`,`[buf.buf_operand; Lit 32w]`,`sm`] mp_tac ci_mono_emit_op >>
      simp[ci_mono_def]) >>
  metis_tac[alloc_buffer_safe_operand]
QED

Triviality outbuf_saved_operand:
  (!x. not_fresh_at s5 x ==>
    lookup_var x tout = lookup_var x tk /\
    op_taint tf (Var x) = op_taint tnK (Var x)) /\
  safe_operand s5 op ==>
  eval_operand op tout = eval_operand op tk /\ op_taint tf op = op_taint tnK op
Proof
  Cases_on `op` >> simp[safe_operand_def,eval_operand_def,op_taint_def]
QED

Theorem raw_bytes_outbuf_saved_input_mods:
  eval_operand addr tk = SOME (w2w (target:address)) /\
  eval_operand len tk = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var p) tk = SOME (n2w (b+32)) /\
  eval_operand value_op tk = SOME (n2w amount) /\
  EVERY (safe_operand s5) [addr;len;Var p;value_op] /\
  EVERY (\op. op_taint tnK op = {}) [addr;len;Var p;value_op] /\
  (bs <> [] ==> ptr_covers GK tnK p tk (LENGTH bs)) /\
  (!mem. mem_agree_outside tnK.t_mem tk.vs_memory mem ==>
    mem_bytes_at (b+32) (LENGTH bs) mem = bs) /\
  b+32+LENGTH bs <= tk.vs_alloca_next /\ b+32+LENGTH bs < dimword (:256) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  (!g. go = SOME g ==> safe_operand s5 g) /\ ci_mono s5 s6 /\
  compile_raw_call_outbuf M s6 = ((ov,op),sout) /\ op_taint tf gas = {} /\
  tout.vs_memory = tk.vs_memory /\ tk.vs_alloca_next <= tout.vs_alloca_next /\
  (!j. j IN tf.t_mem <=> j IN tnK.t_mem \/ (tk.vs_alloca_next <= j /\ j < ob+n)) /\
  (!x. not_fresh_at s5 x ==>
    lookup_var x tout = lookup_var x tk /\ FLOOKUP J x = FLOOKUP GK x /\
    op_taint tf (Var x) = op_taint tnK (Var x)) /\
  return_buf_frame d cenv sa tk /\ sa.cs_next_var <= s5.cs_next_var ==>
  eval_operand addr tout = SOME (w2w target) /\
  eval_operand len tout = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var p) tout = SOME (n2w (b+32)) /\
  eval_operand value_op tout = SOME (n2w amount) /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  b+32+LENGTH bs <= tout.vs_alloca_next /\
  read_memory (b+32) (LENGTH bs) tout = bs /\
  (!j. b+32 <= j /\ j < b+32+LENGTH bs ==> j NOTIN tf.t_mem) /\
  (bs <> [] ==> ptr_covers J tf p tout (LENGTH bs)) /\
  EVERY (\op. op_taint tf op = {}) [addr;len;Var p;gas;value_op] /\
  EVERY (safe_operand sout) [addr;len;Var p;gas;value_op;ov;op] /\
  (!x. MEM (Var x) [addr;len;Var p;gas;value_op;ov;op] ==> not_fresh_at sout x) /\
  return_buf_frame d cenv sa tout
Proof
  strip_tac >>
  `ci_mono s6 sout` by
    (qspecl_then [`M`,`s6`] mp_tac ci_mono_compile_raw_call_outbuf >> simp[]) >>
  `s5.cs_next_var <= sout.cs_next_var /\ s6.cs_next_var <= sout.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `safe_operand s6 gas` by
    (Cases_on `go` >> gvs[] >> metis_tac[emit_op_safe_operand]) >>
  `safe_operand sout ov /\ safe_operand sout op` by
    (drule outbuf_compile_operands >> simp[]) >>
  `!op. safe_operand s5 op ==>
    eval_operand op tout = eval_operand op tk /\ op_taint tf op = op_taint tnK op` by
    (gen_tac >> disch_tac >> irule outbuf_saved_operand >>
     qexists_tac `s5` >> simp[]) >>
  `read_memory (b+32) (LENGTH bs) tout = bs` by
    (simp[read_memory_eq_mem_bytes_at] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!j. b+32 <= j /\ j < b+32+LENGTH bs ==> j NOTIN tf.t_mem` by
    (drule robust_mem_bytes_at_clean >> disch_tac >> gen_tac >> strip_tac >>
     `j < tk.vs_alloca_next` by decide_tac >>
     qpat_assum `!i. _ ==> i NOTIN tnK.t_mem` (qspec_then `j` mp_tac) >> simp[]) >>
  `not_fresh_at s5 p` by fs[safe_operand_def] >>
  `(bs <> [] ==> ptr_covers J tf p tout (LENGTH bs))` by
    (disch_tac >> irule ptr_covers_lookup_frame >>
     qpat_assum `bs <> [] ==> _` (drule_then (irule_at Any)) >>
     qpat_assum `!x. not_fresh_at s5 x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `return_buf_frame d cenv sa tout` by
    (irule return_buf_frame_frame >> qpat_assum `return_buf_frame d cenv sa tk` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     `not_fresh_at s5 x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at s5 x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `safe_operand sout gas` by
    (irule safe_operand_mono >> qexists_tac `s6` >> simp[]) >>
  `EVERY (safe_operand sout) [addr;len;Var p;gas;value_op;ov;op]` by
    (fs[] >> rpt conj_tac >> irule safe_operand_mono >> qexists_tac `s5` >> simp[]) >>
  `b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
   b+32+LENGTH bs <= tout.vs_alloca_next` by decide_tac >>
  fs[] >> fs[safe_operand_def] >> rpt strip_tac >> gvs[]
QED

(* Recursive typed-store memory continuation: endpoint-normalized leaves. *)
Theory typedNormalizeRecursiveMem
Ancestors
  typedNormalizeSemanticMem typedNormalizeTupleSemanticMem typedNormalizeStructSemanticMem
  typedNormalizeStructMetadata typedNormalizeStructEntryMem
  typedNormalizeFrame typedMemoryCopy stmtSimReturn
  venomState compileEnv memContinuation typedCopyAgreement emitHelper arithmetic valueCopyBytes
  exprSimBufferStore exprSimDefs exprSimProps loweringPosts exprSimAggregateChildren exprLoweringProps
  context vyperTypeSystem vyperValue vyperTyping valueEncoding valueEncodingDefs

Theorem typed_store_word_mem_cont:
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `sty = dty` by metis_tac[typed_copy_word_widening] >> gvs[] >>
  `type_memory_size dtv = 32` by metis_tac[word_type_sizes] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  gvs[] >> drule_all normalize_word_window_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality,lookup_var_def,ADD_COMM] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem typed_store_bytestring_mem_cont:
  is_bytestring_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `val_in_memory dtv v (w2n sw) s.vs_memory` by
    metis_tac[bytestring_val_in_memory_transfer] >>
  `val_store_size stv v = val_store_size dtv v` by
    metis_tac[bytestring_val_store_size_eq] >>
  `val_store_size stv v <= type_memory_size stv /\
   val_store_size dtv v <= type_memory_size dtv /\
   val_footprint dtv v <= val_store_size dtv v` by
    metis_tac[val_store_size_le,val_footprint_le_store_size] >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `32 + 32 * word_size len < dimword(:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   val_footprint dtv v <= 32 + 32 * word_size len` by decide_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by suspend "bytes_code" >>
  drule_all normalize_bytestring_window_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality,lookup_var_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
Resume typed_store_bytestring_mem_cont[bytes_code]:
  `compile_store_bytestring src dst sa = ((),sb)` by
    gvs[compile_store_memory_typed_bytes] >>
  drule buffer_store_bytestring_shape >> simp[same_blocks_def]
QED
Finalise typed_store_bytestring_mem_cont

(* Remaining recursive interface (not an admission):
   compile_store_memory_typed_mem_cont will take the metadata consistency,
   acyclicity, field-size, widening, type evaluation, value typing/WF,
   operand freshness/evaluation, full-window disjointness, strict word bounds,
   code containment and initial-control premises of
   compile_store_memory_typed_run. In addition it requires both full type
   windows below s.vs_alloca_next, a zero-phi compiler prefix at sa, and an
   existing zero-phi block at sb.cs_current_bb.
   Its SAME witness t must satisfy mem_cont_sim ctx fn s t, nonhalted control
   at sb's endpoint, destination val_in_memory, exterior byte equality for the
   full destination window, the state-record frame of typed_store_word_mem_cont
   and preservation of all not_fresh_at sa variables.
   Rank induction quantifies compiler/runtime states, operands and source types
   universally; only the destination type_rank is bounded. Tuple/nominal
   semantic field adapters and fast-copy/empty wrappers precede that induction.
*)

Theorem typed_store_empty_mem_cont:
  acyclic_struct_metadata ce.ce_struct_fields /\ value_has_type dtv v /\
  type_widens_to tenv sty NoneT /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv NoneT = SOME dtv /\
  compile_store_memory_typed ce dst NoneT src sty sa = ((),sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!p k. p+k <= w2n dw \/ w2n dw+type_memory_size dtv <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := sa.cs_current_bb; vs_inst_idx := LENGTH sa.cs_current_insts;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[Once compile_store_memory_typed_def, is_word_type_def,
    is_bytestring_type_def, type_memory_bytes_def, compile_copy_memory_def,
    comp_return_def, evaluate_type_def, value_has_type_def] >>
  qexists_tac `s` >> simp[mem_cont_sim_refl, val_in_memory_def,
    venom_state_component_equality]
QED

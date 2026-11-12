(* Apply the Log suffix to the actual endpoint, hiding its arbitrary limit. *)
Theory stmtSimLogSuffixActual
Ancestors
  stmtSimLogSuffixFrame compileEnv loweringStateRelDefs context venomState finite_map pred_set
  ASCIInumbers list abiEncoderWindowContract allocaSiteResource venomMemDefs
  stmtSimLogTrace stmtSimLogDataRun abiEncoderAppend loweringHalt
  emitHelperProps fragExec exprLoweringProps stmtLoweringMono abiBuiltinAllocation
  abiEncoderAllocationShape compilerInstructionSuffix

Theorem log_finite_name_bound[local]:
  !names. FINITE names ==>
    ?bound:num. !n. bound <= n ==> STRING #"%" (toString n) NOTIN names
Proof
  ho_match_mp_tac FINITE_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `STRING #"%" (toString _) <> name` >>
  Cases_on `?k:num. name = STRING #"%" (toString k)`
  >- (pop_assum strip_assume_tac >> qexists_tac `MAX bound (SUC k)` >>
      simp[ASCIInumbersTheory.toString_11] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  qexists_tac `bound` >> rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem log_fresh_limit_exists:
  !s sb. ?limit_st. sb.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st s
Proof
  rpt gen_tac >> qspec_then `FDOM s.vs_vars` mp_tac log_finite_name_bound >>
  simp[] >> strip_tac >>
  qexists_tac `sb with cs_next_var := MAX sb.cs_next_var bound` >>
  simp[fresh_vars_wrt_def, arithmeticTheory.GREATER_EQ] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem log_success_suffix_actual_run:
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  log_eval_view ce args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs) |>]) t /\
    inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid a k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> qspecl_then [`s`, `sb`] strip_assume_tac log_fresh_limit_exists >>
  drule_all log_success_suffix_framed_run >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED

(* Resource packaging only: input validity is supplied by tuple preparation.
 * stmt_state_rel supplies alloca_inv and alloca_room. The two registrations
 * are the actual source/output ALLOCA results; their sizes may exceed the
 * windows used here. Fragment exclusion and size-32 reuse come from the
 * encoder's allocation sites, not from an instruction-ID interval budget. *)
Theorem log_encoder_window_pre_registered:
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av b cap s.vs_memory /\
  eval_operand src s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  FLOOKUP s.vs_allocas source_id = SOME (b,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,output_cap) /\
  cap <= source_cap /\ LENGTH (enc at av) <= output_cap /\
  source_id <> output_id /\
  source_id NOTIN frag_ids st en /\ output_id NOTIN frag_ids st en /\
  (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==> sz = 32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_window_pre ctx func st en dst src ei at av b cap d s
Proof
  strip_tac >>
  `b + source_cap <= s.vs_alloca_next /\
   d + output_cap <= s.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `venomMemDefs$regions_disjoint (b,source_cap) (d,output_cap)` by
    metis_tac[alloca_site_registered_disjoint] >>
  simp_tac bool_ss [abi_encoder_window_pre_def] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- decide_tac
  >- decide_tac
  >- (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
      simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz)` >>
  `inst.inst_id <> source_id /\ inst.inst_id <> output_id` by metis_tac[] >>
  `venomMemDefs$regions_disjoint (b,source_cap) (p,sz) /\
   venomMemDefs$regions_disjoint (d,output_cap) (p,sz)` by
    metis_tac[alloca_site_registered_disjoint] >>
  conj_tac >- metis_tac[] >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* The compiler trace is compile_log_data_trace (or compile_log_empty_trace).
 * Unlike scalar execution, its encoder stage may extend the CFG.  This
 * boundary extracts code for each actual stage without flattening that CFG. *)
Theorem log_aggregate_data_stage_code:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs (MAP SND xs) src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func ==>
  fn_has_code st s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\ cs_extends sm s3 /\ cs_extends s3 sb
Proof
  strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  `cs_extends s1 s2` by
    (mp_tac (cj 3 ci_mono_list_helpers) >>
     disch_then (qspecl_then [`ce`, `xs`, `src.buf_operand`, `0`, `s1`] mp_tac) >>
     simp[ci_mono_def]) >>
  drule cs_extends_abi_encode >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s4 sb` by
    (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `cs_extends sm s1` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `cs_extends sm s2` by (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends sm s3` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends sm s4` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s3 sb` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  rpt conj_tac >> metis_tac[fn_has_code_mid, cs_extends_refl]
QED

(* These are the two real allocation sites in compile_log_data_trace.  This
 * is code membership, not a claim that either site has executed. *)
Theorem log_aggregate_data_allocation_sites:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs (MAP SND xs) src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func ==>
  src.buf_size = cap /\ dst.buf_size = outcap /\
  src.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
  dst.buf_operand = Var (STRING #"%" (toString s2.cs_next_var)) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst s2.cs_next_id ALLOCA [Lit (n2w outcap)]
    [STRING #"%" (toString s2.cs_next_var)]) (fn_insts func) /\
  st.cs_next_id < s2.cs_next_id /\ s2.cs_next_id < s3.cs_next_id
Proof
  strip_tac >> drule_all log_aggregate_data_stage_code >> strip_tac >>
  imp_res_tac log_buffer_trace_code >>
  imp_res_tac abi_builtin_alloc_buffer_shape >>
  imp_res_tac emitted_insts_emit_op >>
  drule compile_log_store_data_aggregate_shape >> strip_tac >> simp[]
QED

(* Static site boundaries only; no runtime registration or reuse-size claim. *)
Theorem log_aggregate_data_encoder_sites:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs (MAP SND xs) src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func ==>
  st.cs_next_id NOTIN frag_ids s3 s4 /\
  s2.cs_next_id NOTIN frag_ids s3 s4 /\
  (!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids s3 s4 /\
    inst.inst_opcode = ALLOCA ==>
    inst.inst_operands = [Lit 32w] /\
    ?q. inst.inst_outputs = [q] /\ ~not_fresh_at s3 q)
Proof
  strip_tac >>
  drule_all log_aggregate_data_stage_code >> strip_tac >>
  drule_all log_aggregate_data_allocation_sites >> strip_tac >>
  conj_tac >- (irule encoder_fragment_prior_site_excluded >> decide_tac) >>
  conj_tac >- (irule encoder_fragment_prior_site_excluded >> decide_tac) >>
  rpt strip_tac >> drule_all encoder_function_alloca_shape >> simp[]
QED

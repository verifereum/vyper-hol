Theory bodyFullAbiDecodeComplexPrefix
Ancestors
  bodyPtrBopScalarOutcome
  bodyFullAbiDecodeInterface bodyFullAbiDecodeFiniteGuard
  bodyFullAbiDecodeBytesArithmetic abiDecodePtrPrims abiDecoderCoherence abiDecoderMemberInfos vyperABI valueEncoding
  abiDecoderReentry bodyPtrTypeBuiltinsBounds loweringStateRelDefs
  emitHelper compileEnv emitHelperProps exprLowering exprLoweringProps abiEncoder venomExecSemantics
  venomInst venomState words list rich_list finite_map

(* Runtime guard totality needs operand liveness, not global freshness. *)
Theorem abi_decode_complex_header_run[local]:
  emit_op ADD [pos;Lit (n2w static_sz)] sa = (e,sm) /\
  compile_abi_decode_range_check pos e hi sm = ((),sb) /\
  abi_decoder_operand_live sa.cs_next_var pos /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  eval_operand pos s = SOME (n2w off) /\
  eval_operand hi s = SOME (n2w h) /\
  off < dimword (:256) /\ static_sz < dimword (:256) /\ h < dimword (:256) ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ off+static_sz <= h)
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `!n w u. sa.cs_next_var <= n ==>
    eval_operand pos (update_var (STRING #"%" (toString n)) w u) = eval_operand pos u /\
    eval_operand hi (update_var (STRING #"%" (toString n)) w u) = eval_operand hi u` by
    (rpt strip_tac >> irule eval_operand_update_old >> qexists_tac `sa` >> simp[] >>
     rpt strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  `!w u. eval_operand (Lit w) u = SOME w` by simp[eval_operand_def] >>
  `!x w u. eval_operand (Var x) (update_var x w u) = SOME w` by
    simp[eval_operand_update_var] >>
  simp[Once run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def] >>
  Cases_on `w2n (n2w off + n2w static_sz : bytes32) < off \/
            w2n (n2w off + n2w static_sz : bytes32) > h`
  >- simp[] >>
  gvs[] >>
  `off + static_sz <= h` by
    (irule abi_decode_checked_add_bound >> gvs[word_add_n2w, w2n_n2w]) >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj] >>
  simp[Once run_inst_seq_def, Once step_inst_base_def,
       exec_pure2_def, exec_pure1_def, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj] >>
  simp[run_inst_seq_def, Once step_inst_base_def, WORD_AND_IDEM]
QED

Theorem abi_decode_coherent_dynamic_memory[local]:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    (is_dynamic (vyper_to_abi_type env ty) ==> 32 <= type_memory_size tv)
Proof
  `!tys tvs env.
    LIST_REL (\ty tv. is_dynamic (vyper_to_abi_type env ty) ==>
                       32 <= type_memory_size tv) tys tvs ==>
    (any_dynamic (vyper_to_abi_types env tys) ==>
       32 <= type_memory_size_list tvs)` by
    (Induct_on `tys` >- simp[] >>
     Cases_on `tvs` >> simp[] >> rpt strip_tac >>
     gvs[type_memory_size_def] >> res_tac >> decide_tac) >>
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `bt` >>
      gvs[type_memory_size_def] >> Cases_on `b` >>
      gvs[type_memory_size_def])
  >- simp[type_memory_size_def]
  >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
      gvs[type_memory_size_def, abi_decoder_header_def,
          vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      `type_memory_size tv <= n * type_memory_size tv` by
        (Cases_on `n` >> gvs[arithmeticTheory.MULT_SUC]) >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS])
  >- (rpt gen_tac >> strip_tac >> simp[type_memory_size_def] >>
      metis_tac[])
  >> rpt gen_tac >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  simp[type_memory_size_def, valueEncodingTypingTheory.type_memory_size_fields_zip] >>
  gvs[] >> metis_tac[]
QED

Theorem abi_decode_coherent_head_memory[local]:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_embedded_static_size ce.ce_struct_fields ty <= type_memory_size tv
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abiDecodeRangesTheory.abi_member_head_size_def] >>
  metis_tac[abi_decode_coherent_dynamic_memory]
QED

Theorem abi_decode_complex_schema[local]:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex dyn infos ==>
  ?env' sf' tys tvs.
    infos = abi_decoder_member_infos sf' ce tys /\
    LIST_REL (abi_decoder_coherent ce env' sf') tys tvs /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) tys)
Proof
  Cases_on `ty`
  >- (Cases_on `b` >> simp[type_to_abi_dec_info_def] >>
      Cases_on `b'` >> simp[type_to_abi_dec_info_def])
  >- (simp[abi_decoder_coherent_tuple_iff, abi_decoder_tuple_infos] >>
      rpt strip_tac >> gvs[] >>
      qexistsl_tac [`env`, `sf`, `l`, `tvs`] >> simp[type_memory_size_def] >>
      drule abi_decoder_member_infos_layout >> simp[])
  >- (Cases_on `b` >>
      simp[type_to_abi_dec_info_def, abi_decoder_fixed_array_infos,
           abi_decoder_coherent_array_iff] >>
      rpt strip_tac >> gvs[] >>
      qexistsl_tac [`env`, `sf`, `REPLICATE n t`, `REPLICATE n tv'`] >>
      simp[LIST_REL_REPLICATE_same, type_memory_size_def,
           abi_decoder_member_infos_def, GSYM REPLICATE_GENLIST,
           SUM_REPLICATE] >>
      drule abi_decoder_coherent_header >> simp[abi_decoder_header_def])
  >- (simp[abi_decoder_coherent_struct_iff] >> rpt strip_tac >>
      drule abi_decoder_struct_infos >>
      disch_then (qspec_then `ce` assume_tac) >>
      `MAP SND (MAP (\(name,ty,sz). (name,ty)) fields) =
            MAP (FST o SND) fields` by
        (simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
      gvs[] >>
      qexistsl_tac [`env \\ p`, `sf \\ nsid_to_string p`, `MAP (FST o SND) fields`, `tvs`] >>
      simp[type_memory_size_def] >>
      `LENGTH fields = LENGTH tvs` by
        (imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
      simp[valueEncodingTypingTheory.type_memory_size_fields_zip] >>
      drule abi_decoder_member_infos_layout >> simp[])
  >> simp[type_to_abi_dec_info_def]
QED

Theorem abi_decode_member_head_bound[local]:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  FOLDR (\(_,asz,_) acc. asz + acc) 0
    (abi_decoder_member_infos sf ce tys) <= SUM (MAP (type_memory_bytes ce) tys)
Proof
  Induct_on `tys` >- simp[abi_decoder_member_infos_def] >>
  Cases_on `tvs` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule abi_decode_coherent_head_memory >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> rpt strip_tac >>
  gvs[abi_decoder_member_infos_def]
QED

Theorem abi_decode_member_head_sum[local]:
  !tys. FOLDR (\(_,asz,_) acc. asz + acc) 0
    (abi_decoder_member_infos sf ce tys) =
    SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)
Proof
  Induct >> simp[abi_decoder_member_infos_def] >>
  gvs[abi_decoder_member_infos_def]
QED

(* Syntactic quotations from Interface; no new HOL predicates. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val owned_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
     h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
       h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

(* Exact bounded member antecedent, with the empty prefixes reduced. *)
val empty_member_entry = ``\dst src opc base_op hi elems env sf tys tvs live protected start finish s G tn d.
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
    elems = abi_decoder_member_infos sf ce tys /\ hi <> Lit 0w /\
    (?off h. eval_operand src s = SOME (n2w off) /\
      eval_operand hi s = SOME (n2w h) /\
      off+SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) <= h /\
      h <= LENGTH input_bytes) /\
    compile_abi_decode_complex_elems dst src opc base_op hi elems 0 0 start =
      ((),finish) /\
    eval_operand dst s = SOME (n2w d) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d d
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn``;

Theorem abi_decode_complex_prefix_joint:
  !finish.
  (^guarded_to_buf_entry) dst src opc base_op hi (DecComplex dyn infos)
    env sf ty tv live protected start finish s G tn d ==>
  (?t Gf tnf. !H. V H ==> gas_origin_ptr_path
    (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) \/
  (?env' sf' tys tvs e sm sb t Gf tnf.
    infos = abi_decoder_member_infos sf' ce tys /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) tys) /\
    emit_op ADD [src;Lit (n2w (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)))]
      start = (e,sm) /\
    compile_abi_decode_range_check src e hi sm = ((),sb) /\
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!x. not_fresh_at start x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (^empty_member_entry) dst src opc base_op hi infos env' sf' tys tvs live protected
      sb finish t Gf tnf d)
Proof
  BETA_TAC >> gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?off h. eval_operand src s = _ /\ _ /\ off < _ /\ h <= _`
    strip_assume_tac >>
  `type_to_abi_dec_info sf ce ty = DecComplex dyn infos` by metis_tac[] >>
  drule_all abi_decode_complex_schema >> strip_tac >>
  drule_all abi_decode_complex_bounded_split >> strip_tac >>
  `FOLDR (\(_,asz,_) acc. asz+acc) 0 infos < dimword (:256)` by
    (drule abi_decode_member_head_bound >>
     asm_rewrite_tac[] >> decide_tac) >>
  `h < dimword (:256)` by decide_tac >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `cs_extends start sb /\ cs_extends sb finish'` by
    (conj_tac
     >- (irule cs_extends_same_block >>
         conj_tac
         >- (qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
             qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
             simp[compile_abi_decode_range_check_def, comp_bind_def,
               comp_ignore_bind_def, emit_op_def, emit_void_def,
               fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
             rpt strip_tac >> gvs[]) >>
         simp[] >> gvs[inst_extends_def, IS_PREFIX_APPEND]) >>
     mp_tac (cj 2 externalEntryShapeTheory.compile_abi_decode_labels) >>
     disch_then (qspecl_then [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`] mp_tac) >>
     asm_rewrite_tac[] >> simp[]) >>
  `fn_has_code start sb fn /\ fn_has_code sb finish' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `?B. bop_scalar_seq {x | not_fresh_at start x}
    {src;hi;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))}
    (emitted_insts start sb) B` by
    (irule abi_decode_complex_header_scalar >>
     conj_tac >- simp[] >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!op. op IN {src;hi;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))} ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
     rpt strip_tac >> gvs[] >>
     simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  `allocas_from lo s` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_x_assum `!H. V H ==> _` drule >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  drule_all abi_decode_complex_header_run >> strip_tac
  >- (disj1_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >> simp[]) >>
  `start.cs_next_id <= sb.cs_next_id` by
    (qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[compile_abi_decode_range_check_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts start sb)` by
    (qpat_x_assum `EVERY (\i. (fresh_write_op _ \/ _) /\ _) _` mp_tac >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >>
     Cases_on `i.inst_opcode = ALLOCA` >>
     simp[freshWritesTheory.fresh_write_op_def]) >>
  `not_fresh_at start input` by
    (gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_all (BETA_RULE abi_decode_scalar_guard_success_joint) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `u.vs_labels = s.vs_labels` by
    (drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >> simp[] >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `u = _` kall_tac >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    eval_operand op u = eval_operand op s /\
    op_prov Gf op = op_prov G op /\
    op_taint tnf op = op_taint tn op` by
    (qpat_x_assum `!x. not_fresh_at start x ==> _` mp_tac >>
     qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac (srw_ss()) [not_fresh_at_def, ptrDisciplineTheory.op_taint_def] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  disj2_tac >>
  qexistsl_tac [`env'`, `sf'`, `tys`, `tvs`, `e`, `sm`, `sb`, `u`, `Gf`, `tnf`] >>
  `FOLDR (\(_,asz,_) acc. asz+acc) 0 infos =
     SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)` by
    (qpat_assum `infos = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[abi_decode_member_head_sum]) >>
  qpat_x_assum `FOLDR _ _ infos = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `local_ptrs_reserved ce sb` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
    abi_decoder_operand_live sb.cs_next_var op` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
  `?p. dst = Var p /\ ptr_covers Gf tnf p u (type_memory_size tv) /\
    FLOOKUP Gf p = SOME (output_base,output_cap)` by
    (qpat_x_assum `?p. dst = Var p /\ _` strip_assume_tac >>
     qexists_tac `p` >>
     `not_fresh_at start p` by
       (qpat_x_assum `abi_decoder_operand_live _ dst` mp_tac >>
        qpat_assum `dst = Var p` (fn th => rewrite_tac[th]) >>
        simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          not_fresh_at_def]) >>
     qpat_x_assum `!x. not_fresh_at start x ==> _` drule >>
     gvs[bodyPtrDefsTheory.ptr_covers_def]) >>
  `eval_operand dst u = SOME (n2w d) /\ op_taint tnf dst = {}` by
    metis_tac[] >>
  `op_taint tn (Var input) = {} /\
   abi_decoder_operand_live start.cs_next_var (Var input)` by metis_tac[] >>
  qpat_assum `type_memory_size tv = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_assum `dst = Var p`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_assum `opc = MLOAD`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_assum `base_op = Var input`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_assum `infos = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  asm_rewrite_tac[] >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`off`, `h`] >> simp[arithmeticTheory.LESS_MOD]) >>
  conj_tac
  >- (qexistsl_tac [`off`, `h`] >> simp[arithmeticTheory.LESS_MOD] >> decide_tac) >>
  qpat_x_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ (b+k <= d \/ d+_ <= b)) live` mp_tac >>
  pure_rewrite_tac [EVERY_MEM] >> strip_tac >>
  qx_gen_tac `entry` >> strip_tac >> first_x_assum drule >>
  PairCases_on `entry` >> simp[] >> rpt strip_tac >> decide_tac
QED

(* Compiler-only control layout for the slots fragment. *)
Theory bodyFullStoreSlotsStaticLayout
Ancestors
  aggregateCodeTrace aggregateTypedCopyRawShape bodyFullStoreSlotsStaticCode
  bodyFullStoreSlotsStaticControl pred_set
  exprSimAbiEncodeObliviousCode exprSimAbiGasBridge context compileEnv
  fragExec exprLoweringProps emitHelper list rich_list sorting venomExecSemantics
  venomInst venomWf

val layout_primitives = [code_trace_certified_emit_inst,
  code_trace_certified_emit_void, code_trace_certified_emit_op,
  code_trace_certified_return, code_trace_certified_fresh_var,
  code_trace_certified_fresh_label];

val layout_sequence = rpt (FIRST [
  irule code_trace_certified_reserve_label,
  irule code_trace_reserved_fresh_label,
  irule code_trace_reserved_new_block_bind,
  irule (SRULE [comp_ignore_bind_def] code_trace_reserved_new_block_bind),
  irule code_trace_certified_bind >> conj_tac,
  irule code_trace_certified_ignore_bind >> conj_tac,
  irule code_trace_reserved_bind_left >> conj_tac,
  irule code_trace_reserved_ignore_bind_left >> conj_tac,
  gen_tac] >> simp layout_primitives);

Theorem store_slots_primitive_trace[local]:
  (!src dst cnt tr. code_trace_certified
    (comp_ignore_bind
      (compile_word_copy_loop_op src dst cnt LocMemory
        (if tr then LocTransient else LocStorage) F) (comp_return ()))) /\
  (!src. code_trace_certified (compile_bytestring_word_count src)) /\
  (!src off. code_trace_certified (compile_lit_byte_offset src off))
Proof
  rpt conj_tac
  >- (rpt gen_tac >> Cases_on `tr` >>
      simp[compile_word_copy_loop_op_def, compile_word_copy_loop_base_def,
           word_scale_def, compile_ptr_load_def, compile_ptr_store_def,
           comp_ignore_bind_def, comp_bind_assoc] >>
      rewrite_tac[GSYM code_trace_reserved_empty] >> layout_sequence)
  >- (simp[compile_bytestring_word_count_def] >> layout_sequence) >>
  rpt gen_tac >> simp[compile_lit_byte_offset_def] >> IF_CASES_TAC >>
  simp layout_primitives >> Cases_on `src` >> simp layout_primitives
QED

Theorem store_slots_trace_family:
  (!cenv src dst ty tr.
    code_trace_certified (compile_store_slots cenv src dst ty tr)) /\
  (!cenv src dst members mo so tr.
    code_trace_certified
      (compile_store_slots_members cenv src dst members mo so tr)) /\
  (!cenv src dst elem cnt tr.
    code_trace_certified (compile_copy_elements_to_slots cenv src dst elem cnt tr))
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_slots_def, code_trace_certified_return]
  >- (rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
      layout_sequence >> simp[store_slots_primitive_trace]) >>
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  rewrite_tac[GSYM code_trace_reserved_empty] >> layout_sequence >>
  simp[code_trace_reserved_new_block_ignore]
QED

Resume store_slots_trace_family[dispatch]:
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields ty`
  >- (simp[] >> IF_CASES_TAC
      >- (Cases_on `tr` >> layout_sequence) >>
      Cases_on `tr` >>
      simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
           compile_word_copy_loop_def] >>
      metis_tac[store_slots_primitive_trace, COND_CLAUSES]) >>
  simp[] >> Cases_on `is_bytestring_type ty`
  >- (simp[] >> irule code_trace_certified_bind >>
      simp[store_slots_primitive_trace]) >>
  simp[] >> IF_CASES_TAC >- simp[code_trace_certified_emit_void] >>
  Cases_on `ty` >> gvs[code_trace_certified_emit_void]
  >- (rename1 `ArrayT elem bd` >> Cases_on `bd` >>
      gvs[code_trace_certified_emit_void] >> Cases_on `tr` >> layout_sequence)
QED

Finalise store_slots_trace_family

Theorem store_slots_fragment_syntax_shape:
  compile_store_slots cenv src dst ty tr sa = ((),sb) ==>
  cs_extends sa sb /\ frag_ops_free sa sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  (!bb. MEM bb (FRONT (emitted_blocks sa sb)) ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `code_trace_certified (compile_store_slots cenv src dst ty tr)` by
    simp[store_slots_trace_family] >>
  drule_all code_trace_certified_raw_shape >> strip_tac >>
  `code_action (\opc. T) (compile_store_slots cenv src dst ty tr)` by
    simp[store_slots_code_family] >>
  `code_step (\opc. T) sa sb` by gvs[code_action_def] >>
  drule code_step_extends >> strip_tac >> simp[] >> rpt strip_tac >>
  Cases_on `sa.cs_blocks = sb.cs_blocks`
  >- gvs[emitted_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (irule frag_relabel_front_nonphi >> metis_tac[]) >>
  Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def]
QED

Theorem store_slots_start_oblivious:
  frag_start_oblivious (compile_store_slots cenv src dst ty tr)
Proof
  irule code_trace_start_oblivious >>
  mp_tac (cj 1 store_slots_trace_family) >>
  simp[code_trace_certified_def, code_trace_parametric_def] >> metis_tac[]
QED

Theorem store_slots_fragment_control_layout:
  compile_store_slots cenv src dst ty tr sa = ((),sb) ==>
  EVERY (\i.
    (i.inst_opcode = JMP ==>
      ?l. i.inst_operands = [Label l] /\
        l IN {l | (?bb. MEM bb (FRONT (emitted_blocks sa sb)) /\ l = bb.bb_label) \/
                   l = sb.cs_current_bb}) /\
    (i.inst_opcode = JNZ ==>
      ?v l r. i.inst_operands = [v; Label l; Label r] /\
        l IN {l | (?bb. MEM bb (FRONT (emitted_blocks sa sb)) /\ l = bb.bb_label) \/
                   l = sb.cs_current_bb} /\
        r IN {l | (?bb. MEM bb (FRONT (emitted_blocks sa sb)) /\ l = bb.bb_label) \/
                   l = sb.cs_current_bb})) (frag_code sa sb) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  (!bb. MEM bb (FRONT (emitted_blocks sa sb)) ==>
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >> conj_tac
  >- (mp_tac (Q.ISPEC `compile_store_slots cenv src dst ty tr`
        (GEN_ALL (BETA_RULE frag_start_oblivious_target_closure))) >>
      (impl_tac
       >- (conj_tac >- simp[store_slots_start_oblivious] >>
           mp_tac (Q.SPEC `{}:string set`
             (BETA_RULE (cj 1 store_slots_weak_control_family))) >>
           simp[] >> metis_tac[])) >>
      disch_then drule >> simp[]) >>
  drule store_slots_fragment_syntax_shape >> simp[]
QED

Theorem store_slots_fragment_label_operand_target:
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  MEM i (frag_code sa sb) /\
  (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
  MEM (Label l) i.inst_operands ==>
  l = sb.cs_current_bb \/
  MEM l (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  rpt strip_tac >>
  imp_res_tac store_slots_fragment_jnz_operands >>
  drule store_slots_fragment_control_layout >>
  simp[EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  gvs[MEM_MAP] >> metis_tac[]
QED

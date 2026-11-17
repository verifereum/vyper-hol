(* Compiler-only control layout for the slots fragment. *)
Theory bodyFullStoreSlotsStaticLayout
Ancestors
  aggregateCodeTrace aggregateTypedCopyRawShape bodyFullStoreSlotsStaticCode
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

Theorem store_slots_fragment_final_label_fresh:
  compile_store_slots cenv src dst ty tr sa = ((),sb) ==>
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  strip_tac >>
  `code_trace_certified (compile_store_slots cenv src dst ty tr)` by
    simp[store_slots_trace_family] >>
  drule_all code_trace_certified_raw_shape >> simp[]
QED

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

(* One compiler-only diagnostic for the actual-function compatibility boundary.
   No machine execution is involved. *)
Theorem store_slots_nonempty_final_alias_diagnostic[local]:
  let ce = (ARB:compile_env) with ce_struct_fields := FEMPTY;
      sa = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
              cs_current_bb := "@dyn_exit_2";
              cs_current_insts := [mk_inst 17 SSTORE [Lit 0w; Var "%0"] []];
              cs_blocks := []; cs_data_sections := [] |>;
      sb = SND (compile_store_slots ce (Lit 0w) (Lit 0w)
                    (ArrayT (BaseT (UintT 256)) (Dynamic 1)) F sa);
      func = mk_raw_function "alias" sb.cs_blocks
  in
    compile_store_slots ce (Lit 0w) (Lit 0w)
      (ArrayT (BaseT (UintT 256)) (Dynamic 1)) F sa = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_insts <> [] /\
    ?i. MEM i (frag_code sa sb) /\ MEM i.inst_opcode [JMP;JNZ] /\
        MEM (Label sa.cs_current_bb) i.inst_operands
Proof
  EVAL_TAC >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
       EXISTS_OR_THM] >> EVAL_TAC
QED

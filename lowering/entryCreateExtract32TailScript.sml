(* The straight-line extraction starts at the offset's actual normal exit. *)
Theory entryCreateExtract32Tail
Ancestors
  bodyFullExtract32Suffix bodyFullHashKeccakFixed haltExitProj
  createSizeTypeBuiltinCode createSizeCutCode exprSimAbiGasBridge
  entryCreateAdminSequence entryCreatePathScope
  entryCreateSubscriptUncopiedMemory entryCreateFocusSpec entryCreateCompletedCut
  createMarkedPath createSizePrefixReplay abiEncoderProps exprLoweringProps relation
  bodyPtrDefs loweringPosts exprSimExtract32Read fragGasOriginPtr
  gasSummary fragExec fragGasOrigin instIdxIndep
  venomExecSemantics venomInstProofs venomState venomInst
  vyperContext vyperState vyperAST compileEnv list rich_list arithmetic

Triviality forget_edge_memory:
  gas_origin_edge T E C f s marks r ==> gas_origin_edge F E C f s marks r
Proof
  simp[gas_origin_edge_def] >> metis_tac[]
QED

(* An aborting straight run remains inside the suffix. Read the edges from
   its checked origin path; the final one starts at the pre-fault fetch. *)
Theorem extract_tail_abort_scope[local]:
  !code s. lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    LENGTH b.cs_current_insts = s.vs_inst_idx + LENGTH code /\
    (!j. j < LENGTH code ==>
       get_instruction bb (s.vs_inst_idx + j) = SOME (EL j code)) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) code /\
    (?t. run_inst_seq code s = Abort err t) /\
    gas_origin_path T E C f s marks (Abort err u) ==>
    create_operand_full_scope a b E C f s marks (Abort err u)
Proof
  qid_spec_tac `marks` >> Induct_on `code` >> simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (qpat_assum `!j. _ ==> get_instruction bb _ = _`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [EL,prim_recTheory.LESS_0])) >> simp[]) >>
  `s.vs_inst_idx <> LENGTH b.cs_current_insts` by decide_tac >>
  qpat_x_assum `gas_origin_path T _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_origin_path_cases]) >> gvs[]
  >- (
    rename1 `gas_origin_edge T E C f s left (OK mid)` >>
    `?v. step_inst_base h s = OK v /\ ~v.vs_halted /\
         mid = v with vs_inst_idx := SUC s.vs_inst_idx` by
      (qpat_assum `gas_origin_edge T E C f s left (OK mid)`
         (strip_assume_tac o REWRITE_RULE[gas_origin_edge_def]) >>
       gvs[exit_result_def, step_inst_non_invoke] >>
       qpat_x_assum `OK _ = step_inst_base _ _` (assume_tac o SYM) >>
       gvs[exit_result_def]) >>
    `mid.vs_current_bb = s.vs_current_bb` by
      (gvs[] >> metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
    `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
    `?t. run_inst_seq code mid = Abort err t` by
      (gvs[run_inst_seq_inst_idx, exec_result_map_def] >>
       qexists_tac `t with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]) >>
    `!j. j < LENGTH code ==>
       get_instruction bb (mid.vs_inst_idx + j) = SOME (EL j code)` by
      (rpt strip_tac >>
       qpat_assum `!k. _ ==> get_instruction bb _ = _`
         (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [ADD_CLAUSES,EL])) >>
       simp[ADD_CLAUSES]) >>
    `create_operand_full_scope a b E C f mid right (Abort err u)` by
      (first_x_assum irule >> fs[ADD_CLAUSES] >> metis_tac[]) >>
    `create_expr_prefix a b E C f s left mid` by
      (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
       simp[create_marked_edge_def, create_prefix_step_def] >>
       metis_tac[forget_edge_memory]) >>
    fs[create_operand_full_scope_def] >>
    metis_tac[create_expr_prefix_append,APPEND_ASSOC]) >>
  simp[create_operand_full_scope_def] >> qexistsl_tac [`[]`,`s`,`marks`] >>
  simp[create_expr_prefix_nil] >> decide_tac
QED

Theorem extract_tail_layout[local]:
  compile_extract32_load len data offset a = (raw,m) /\
  compile_clamp_basetype raw ty m = (op,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts a b)
Proof
  strip_tac >> drule_all extract32_tail_straight_noext >> strip_tac >>
  `create_cut_code {} a b` by metis_tac[extract32_tail_cut_code] >>
  fs[create_cut_code_def, frag_code_def, emitted_blocks_def, EVERY_MEM,
     is_ext_call_op_def, IS_PREFIX_APPEND] >>
  gvs[emitted_insts_def, DROP_APPEND] >> rpt strip_tac >>
  qpat_assum `!i. _ ==> _ /\ _ /\ ~is_ext_call_op _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `i.inst_opcode = _` (fn th =>
    qpat_x_assum `~is_ext_call_op _` (mp_tac o REWRITE_RULE [th,is_ext_call_op_def])) >>
  simp[]
QED

Theorem extract_tail_selected_scope[local]:
  fn_has_code a b f /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  create_operand_at a s /\ ~s.vs_halted /\
  ((?t. run_inst_seq (emitted_insts a b) s = OK t /\
        r = OK (t with vs_inst_idx := LENGTH b.cs_current_insts)) \/
   (?t j. run_inst_seq (emitted_insts a b) s = Abort Revert_abort t /\
          r = Abort Revert_abort (t with vs_inst_idx := j))) /\
  gas_origin_path T E C f s [] r ==>
  create_operand_full_scope a b E C f s [] r
Proof
  strip_tac
  >- (qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
      irule create_admin_sequence_scope >> simp[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  fs[create_operand_at_def] >>
  irule extract_tail_abort_scope >> gvs[] >>
  qexists_tac `emitted_insts a b` >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem create_extract32_selected_tail:
  extract32_suffix_ready (DF,lo,d,ctx,func) cenv cx st0 (src,off,bt)
    (es,sa,s0,G0,tn0) (st3,sb,op) (ee,s,G,tn)
    (bs,m,p,i,len,data,offset,raw,st4,srcop) ==>
  let e = TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off];
      vv = StackValue (BaseT bt) op;
      source = bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
        [expr_type src;expr_type off] [BytesV bs;IntV i])) (\v. return (Value v))
  in scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
       st3 sb source (ee,s,G,tn)
       (\H res ee' HG th t.
         create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e
           (es,sa,sb,s0,vv,G0,tn0) H res ee' HG th t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
       (create_operand_exit_post ctx cx) /\
     create_operand_cut st3 sb explicit ctx func (cx_tops cx) cx st0 source (ee,s)
Proof
  strip_tac >> drule extract32_suffix_landing >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`res`,`r`,`HG`,`th`]
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  qpat_x_assum `extract32_suffix_ready _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [extract32_suffix_ready_def]) >>
  drule_all extract_tail_layout >> strip_tac >>
  `create_operand_at st3 s` by simp[create_operand_at_def] >>
  simp[LET_DEF] >> reverse conj_tac
  >- (irule create_admin_sequence_cut >> fs[EVERY_MEM] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `gas_origin_path T explicit ctx func s [] r` by
    metis_tac[gas_origin_ptr_path_projections] >>
  `create_operand_full_scope st3 sb explicit ctx func s [] r` by
    (irule extract_tail_selected_scope >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `is_word_type (BaseT bt)` by metis_tac[extract32_suffix_result_word] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  irule nocopy_selector_scoped_landing >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`HG`,`r`,`res`,`th`] >> simp[] >> rpt strip_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[create_operand_vv_post_def, create_operand_exit_post_def,
       post_value_type_def, expr_type_def, contextTheory.vv_location_def] >>
  metis_tac[exit_result_def, exprSimDefsTheory.expr_exit_def, halt_exit_not_halt,
    stmt_state_rel_allocas_below_fmp, vv_post_def]
QED

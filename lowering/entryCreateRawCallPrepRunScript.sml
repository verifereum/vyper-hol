(* Scope at the very raw-run endpoints supplied to the raw-call preparation
   rules. The frame, provenance and horizon posts stay in the joint producers. *)
Theory entryCreateRawCallPrepRun
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  createMarkedPath createSizePrefixReplay
  rawCallOutbufCompile abiBuiltinAllocation generatedGasOrigin msgGasSim
  fragGasOrigin abiEncoderProps exprLoweringProps emitHelper emitHelperProps
  gasExplicitSites gasShadowUnit gasShadowState
  venomState venomInst venomExecSemantics arithmetic list pred_set relation

Theorem prep_emit_layout[local]:
  emit_op opc ops sa = (v,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_next_id = SUC sa.cs_next_id /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  ?i. emitted_insts sa sb = [i] /\
      i.inst_id = sa.cs_next_id /\ i.inst_opcode = opc
Proof
  strip_tac >> drule emit_op_extends >>
  drule emitted_insts_emit_op >>
  simp[same_blocks_def,mk_inst_def,ADD1] >> strip_tac >> strip_tac >> simp[]
QED

Theorem prep_emit_single_scope[local]:
  emit_op opc ops sa = (v,sb) /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  fn_has_code sa sb fn /\ create_operand_at sa s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  create_operand_full_scope sa sb E ctx fn s []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule prep_emit_layout >> strip_tac >>
  irule create_admin_sequence_scope >> simp[frag_ids_def]
QED

Theorem prep_emit_pair_scope[local]:
  emit_op opc1 ops1 sa = (v1,sm) /\ emit_op opc2 ops2 sm = (v2,sb) /\
  opc1 <> INVOKE /\ opc1 <> GAS /\ ~is_terminator opc1 /\
  opc2 <> INVOKE /\ opc2 <> GAS /\ ~is_terminator opc2 /\
  fn_has_code sa sb fn /\ create_operand_at sa s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  create_operand_full_scope sa sb E ctx fn s []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  qpat_assum `emit_op _ _ sa = _` (strip_assume_tac o MATCH_MP prep_emit_layout) >>
  qpat_assum `emit_op _ _ sm = _` (strip_assume_tac o MATCH_MP prep_emit_layout) >>
  drule_all emitted_insts_append >> strip_tac >>
  irule create_admin_sequence_scope >> simp[frag_ids_def,APPEND_ASSOC]
QED

Theorem raw_call_header_selected:
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (dp,s4) /\
  fn_has_code s2 s4 fn /\ ~s.vs_halted /\
  s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  run_inst_seq (emitted_insts s2 s4) s = OK t /\
  t4 = (t with vs_inst_idx := LENGTH s4.cs_current_insts) ==>
  create_operand_full_scope s2 s4 E ctx fn s [] (OK t4)
Proof
  strip_tac >> gvs[] >> irule prep_emit_pair_scope >>
  simp[create_operand_at_def] >>
  qexistsl_tac [`MLOAD`,`ADD`,`[data]`,`[data; Lit 32w]`,`s3`,`len`,`dp`] >>
  simp[is_terminator_def]
QED

Theorem raw_call_outbuf_selected:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  t7 = (u with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  create_operand_full_scope sa sb E ctx fn s [] (OK t7)
Proof
  strip_tac >> drule calldata_outbuf_compile >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  Cases_on `cap = 0` >> gvs[]
  >- (irule prep_emit_single_scope >> simp[create_operand_at_def] >>
      qexistsl_tac [`ALLOCA`,`[Lit 0w]`,`buf.buf_operand`] >>
      simp[is_terminator_def]) >>
  irule prep_emit_pair_scope >> simp[create_operand_at_def] >>
  rename1 `emit_op ADD [buf.buf_operand; Lit 32w] sm = (dp,sb)` >>
  qexistsl_tac [`ALLOCA`,`ADD`,`[Lit (n2w (((cap+31) DIV 32)*32+32))]`,
                `[buf.buf_operand; Lit 32w]`,`sm`,`buf.buf_operand`,`dp`] >>
  simp[is_terminator_def]
QED

Theorem prep_gas_single_scope[local]:
  emit_op GAS [] sa = (gas,sb) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ create_operand_at sa s /\
  (fn.fn_name,sa.cs_next_id) NOTIN E /\
  gas_prefix 1 s.vs_gas_readings = [gw] /\
  t = update_var (FST (fresh_var sa)) gw
        (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                  vs_inst_idx := LENGTH sb.cs_current_insts|>) ==>
  create_operand_full_scope sa sb E ctx fn s [F] (OK t)
Proof
  strip_tac >> drule_all emit_gas_placement_id >> strip_tac >>
  drule prep_emit_layout >> strip_tac >>
  fs[create_operand_at_def] >>
  `?w. gas_prefix 1 s.vs_gas_readings = [w] /\
       gas_path_mem_edge ctx fn s 1
         (OK (update_var (FST (fresh_var sa)) w
           (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                     vs_inst_idx := SUC s.vs_inst_idx|>)))` by
    (irule msg_gas_mem_edge >> simp[] >> qexists_tac `sa.cs_next_id` >> simp[]) >>
  `gas_path_mem_edge ctx fn s 1 (OK t)` by gvs[ADD1] >>
  `gas_origin_edge F E ctx fn s [(fn.fn_name,sa.cs_next_id) IN E] (OK t)` by
    (irule gas_mem_edge_origin >> simp[] >>
     conj_tac >- (qexists_tac `FST (fresh_var sa)` >> simp[]) >>
     qexists_tac `1` >> gvs[ADD1]) >>
  `gas_origin_edge F E ctx fn s [F] (OK t)` by gvs[] >>
  `t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[update_var_def] >>
  simp[create_operand_full_scope_def,create_expr_prefix_marked] >>
  irule RTC_SINGLE >> gvs[create_marked_edge_def,create_prefix_step_def,frag_ids_def]
QED

Theorem raw_call_optional_gas_selected:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  (case shadow_go of SOME g => (g,shadow_sa) |
     NONE => emit_op GAS [] shadow_sa) = (shadow_gas,shadow_sb) /\
  (IS_NONE go <=> IS_NONE shadow_go) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function fn shadow_fn /\
  MEM fn ctx.ctx_functions /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  fn_has_code sa sb fn /\ fn_has_code shadow_sa shadow_sb shadow_fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (case go of SOME _ => t = s |
     NONE => gas_prefix 1 s.vs_gas_readings = [gw] /\
       t = update_var (FST (fresh_var sa)) gw
         (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>)) ==>
  create_operand_full_scope sa sb (gas_explicit_sites ctx shadow_ctx) ctx fn s
    (case go of SOME _ => [] | NONE => [F]) (OK t)
Proof
  Cases_on `go` >> Cases_on `shadow_go` >> simp[] >> strip_tac >> gvs[]
  >- (drule_all compile_generated_gas_origin_path >> strip_tac >>
      irule prep_gas_single_scope >> simp[create_operand_at_def] >>
      metis_tac[]) >>
  simp[create_operand_full_scope_def,create_expr_prefix_marked]
QED

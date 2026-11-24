(* The installed straight stretches of an encoder array.  The run premise
   refers to the very instruction list emitted at the indicated cuts. *)
Theory entryCreateEncoderArrayLinear
Ancestors
  abiEncoderArrayPhases abiEncoderArrayCode abiDecoderIndexInit
  abiDecoderDynamicLoopSetup abiEncoderChildCode abiEncoderArrayTail abiEncoderArrayTailInit
  context compileEnv emitHelper
  entryCreateAdminSequence entryCreatePathScope entryCreateCompletedCut
  entryCreateFocusSpec entrySinkExtraction
  createExprSizeExitDefs abiEncoderProps exprLoweringProps
  emitHelperProps fragExec venomInst list rich_list arithmetic

Definition encoder_array_stretch_def:
  encoder_array_stretch x y <=>
    y.cs_current_bb = x.cs_current_bb /\ inst_extends x y /\
    EVERY (\i. i.inst_id IN frag_ids x y /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
      (emitted_insts x y)
End

Theorem encoder_array_stretch_prefix:
  encoder_array_stretch x y /\ fn_has_code x y fn /\
  a.cs_next_id <= x.cs_next_id /\ y.cs_next_id <= b.cs_next_id /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b) /\
  create_operand_at x s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts x y) s = OK raw ==>
  create_expr_prefix a b E C fn s [] (raw with vs_inst_idx := LENGTH y.cs_current_insts)
Proof
  strip_tac >>
  `create_operand_full_scope x y E C fn s []
    (OK (raw with vs_inst_idx := LENGTH y.cs_current_insts))` by
    (irule create_admin_sequence_scope >> fs[encoder_array_stretch_def, inst_extends_def]) >>
  irule create_expr_prefix_lift >>
  qexistsl_tac [`x`, `y`] >>
  fs[create_operand_full_scope_def] >>
  rpt strip_tac >> res_tac >> fs[frag_ids_def] >> decide_tac
QED

Theorem encoder_array_stretch_layout:
  (abi_encode_array_prefix src dst x = (out,y) ==> encoder_array_stretch x y) /\
  (abi_decode_index_init x = (ip,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_dynamic_init count_op asz x = (ptrs,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_tail_init count_op asz x = (dp,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_addresses ip src dst asz msz x = (coords,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_tail data dp x = (ops,y) ==> encoder_array_stretch x y) /\
  (abi_encode_child_suffix hd dp offset len x = (szop,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_static_exit src asz x = (szop,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_dynamic_exit src dp x = (szop,y) ==> encoder_array_stretch x y) /\
  (abi_encode_array_finish pp szop x = (out',y) ==> encoder_array_stretch x y)
Proof
  rpt conj_tac >>
  simp[abi_encode_array_prefix_def, abi_decode_index_init_def,
    abi_encode_array_dynamic_init_def, abi_encode_array_tail_init_def,
    abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def, abi_encode_array_tail_def,
    abi_encode_child_suffix_def, abi_encode_array_static_exit_def,
    abi_encode_array_dynamic_exit_def, abi_encode_array_finish_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[encoder_array_stretch_def, inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, frag_ids_def] >>
  decide_tac
QED

Theorem encoder_array_stretch_control:
  encoder_array_stretch x y /\ create_operand_at x s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts x y) s = OK raw ==>
  create_operand_at y (raw with vs_inst_idx := LENGTH y.cs_current_insts) /\
  ~raw.vs_halted
Proof
  simp[encoder_array_stretch_def, create_operand_at_def] >> strip_tac >>
  drule run_inst_seq_preserves_entry_control >>
  fs[EVERY_MEM] >> metis_tac[]
QED

(* Both exit alternatives are ordinary straight runs.  In particular the
   finish stretch starts from the normalized endpoint of the exit run. *)
Theorem encoder_array_exit_finish_scoped:
  (if active then abi_encode_array_dynamic_exit src dp exit_st
    else abi_encode_array_static_exit src asz exit_st) = (szop,loop_end) /\
  abi_encode_array_finish pp szop loop_end = (out,final) /\
  fn_has_code exit_st loop_end fn /\ fn_has_code loop_end final fn /\
  a.cs_next_id <= exit_st.cs_next_id /\ loop_end.cs_next_id <= b.cs_next_id /\
  a.cs_next_id <= loop_end.cs_next_id /\ final.cs_next_id <= b.cs_next_id /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
    i.inst_id NOTIN frag_ids a b) /\
  create_operand_at exit_st branch /\ ~branch.vs_halted /\
  create_expr_prefix a b E C fn start [] branch /\
  run_inst_seq (emitted_insts exit_st loop_end) branch = OK raw /\
  mid = (raw with vs_inst_idx := LENGTH loop_end.cs_current_insts) /\
  run_inst_seq (emitted_insts loop_end final) mid = OK fin ==>
  create_expr_prefix a b E C fn start [] (fin with vs_inst_idx := LENGTH final.cs_current_insts)
Proof
  strip_tac >>
  `encoder_array_stretch exit_st loop_end` by
    (Cases_on `active` >> fs[] >> metis_tac[encoder_array_stretch_layout]) >>
  `encoder_array_stretch loop_end final` by
    metis_tac[encoder_array_stretch_layout] >>
  `create_expr_prefix a b E C fn branch [] mid` by
    (gvs[] >> irule encoder_array_stretch_prefix >> metis_tac[]) >>
  `create_operand_at loop_end mid /\ ~mid.vs_halted` by
    (gvs[] >> metis_tac[encoder_array_stretch_control]) >>
  `create_expr_prefix a b E C fn mid [] (fin with vs_inst_idx := LENGTH final.cs_current_insts)` by
    (irule encoder_array_stretch_prefix >> metis_tac[]) >>
  metis_tac[create_expr_prefix_append, APPEND_NIL]
QED

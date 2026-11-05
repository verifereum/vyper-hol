Theory bodyPtrTypeBuiltinsScalarInput
Ancestors
  bodyPtrTypeBuiltinsScalarTransfer loweringSlice emitHelperProps
  fragGasPathPtr ptrSafeRun fragExec venomInst ptrDiscipline
  emitHelper compileEnv

(* Scalar reads are MLOAD producers even when the local address carries
   provenance.  Reuse the general Name normalization, not a Uint-only copy. *)
Theorem scalar_name_emitted_load:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann name) sa = (op, sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [Var p]
      [STRING #"%" (toString sa.cs_next_var)]] /\
  op = Var (STRING #"%" (toString sa.cs_next_var)) /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id MLOAD [Var p]
      [STRING #"%" (toString sa.cs_next_var)]]
Proof
  strip_tac >> drule_all lower_value_name_word >>
  strip_tac >> drule emitted_insts_emit_op >> simp[]
QED

(* Exact supplied normal edges: no assumption about G's address entries. *)
Theorem clearing_edge_output_none:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\
  ~MEM i.inst_opcode [ALLOCA; DALLOCA; PARAM; ADD; SUB; ASSIGN;
                     PHI; INVOKE] /\
  MEM x i.inst_outputs ==>
  FLOOKUP H x = NONE
Proof
  strip_tac >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, exit_result_def]
  >- (gvs[Once ghost_step_def] >> irule step_prov_output_none >>
      simp[] >> irule out_prov_clearing_none >> simp[]) >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >> gvs[exit_result_def]
QED

Theorem forward_edge_output_none:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [ADD; SUB; ASSIGN] /\
  EVERY (\op. op_prov G op = NONE) i.inst_operands /\
  MEM x i.inst_outputs ==>
  FLOOKUP H x = NONE
Proof
  strip_tac >>
  `!u. out_prov PG G i u = NONE` by
    (gen_tac >> irule out_prov_forward_none >> simp[]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI /\
   i.inst_opcode <> INVOKE` by gvs[is_terminator_def] >>
  qpat_x_assum `MEM i.inst_opcode _` kall_tac >>
  gvs[gas_path_ptr_edge_def, exit_result_def]
  >- (gvs[Once ghost_step_def] >> irule step_prov_output_none >> simp[]) >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >> gvs[exit_result_def]
QED

Theorem scalar_name_edge_none:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann name) sa = (op, sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) ==>
  op_prov H op = NONE
Proof
  strip_tac >> drule_all lower_value_name_word >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id MLOAD [Var p]
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[op_prov_def] >> irule clearing_edge_output_none >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`bb`, `mk_inst sa.cs_next_id MLOAD [Var p]
    [STRING #"%" (toString sa.cs_next_var)]`] >>
  simp[mk_inst_def, is_terminator_def]
QED

(* These consequences consume an already supplied safe edge.  Thus neither
   body_inv nor stmt_state_rel is needed to re-prove load safety/value here;
   step_name_word supplies the value separately when assembling simulation.
   In particular no absence premise is imposed on the local address p. *)
Theorem scalar_name_forward_edge_none:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann name) sa = (op, sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  gas_path_ptr_edge D lo ctx fn PG H ts t m H2 us (OK u) /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME move /\
  move.inst_opcode = ASSIGN /\ move.inst_operands = [op] /\
  MEM x move.inst_outputs ==>
  FLOOKUP H2 x = NONE
Proof
  strip_tac >>
  `op_prov H op = NONE` by (irule scalar_name_edge_none >> metis_tac[]) >>
  irule forward_edge_output_none >>
  goal_assum (drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`bb`, `move`] >> simp[]
QED

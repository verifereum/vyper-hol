(* Reachable initialization of the generated fixed-array counter. *)
Theory typedCopyArrayInitMemory
Ancestors typedCopyLoopPlacementMemory typedCopyLoopLayoutPtr typedCopyIndexMemory
  typedMemoryCopy exprOperandVar compileEnv
  stmtForRangeMemoryParts fragGasSeqMem fragGasPathMem fragExecMem exprLoweringProps
  venomExecSemantics venomInst venomState instMemFrontier memSafeRun
  ASCIInumbers words list rich_list finite_map arithmetic

Theorem typed_copy_counter_entry_path_mem[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ASSIGN [Lit 0w] [ctr];
     mk_inst (id+1) JMP [Label header] []] /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted ==>
  gas_path_mem ctx func s 0 (OK (jump_to header (update_var ctr 0w s)))
Proof
  strip_tac >>
  qabbrev_tac `code = [mk_inst id ASSIGN [Lit 0w] [ctr]]` >>
  qabbrev_tac `u = update_var ctr 0w s` >>
  `run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s` by
    simp[Abbr `code`, Abbr `u`, run_inst_seq_def, run_inst_seq_mem_ok_def,
      step_inst_base_opcode_eqs, exec_pure1_def, eval_operand_def,
      inst_dload_in_section_def, below_frontier_no_ranges, mk_inst_def] >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH pre + 1))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def, DROP_LENGTH_APPEND]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := LENGTH pre + 1) 0
    (OK (jump_to header (u with vs_inst_idx := LENGTH pre + 1)))` by
    (irule for_range_jump_at_zero_path_mem >>
     conj_tac >- simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+1) JMP [Label header] []`] >>
     simp[Abbr `u`, update_var_def, get_instruction_def, EL_APPEND_EQN,
       mk_inst_def, is_terminator_def, below_frontier_no_ranges,
       inst_dload_in_section_def, step_inst_base_opcode_eqs]) >>
  `jump_to header (u with vs_inst_idx := LENGTH pre + 1) = jump_to header u` by
    simp[jump_to_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Theorem typed_copy_sarray_header_init_path_mem:
  !ce dst dty src sty count sa sz func ctx s sw dw f stv dtv.
  ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
    ~is_abi_dynamic ce.ce_struct_fields dty) /\
  compile_copy_sarray_typed ce dst dty src sty count sa = ((),sz) /\
  fn_has_code sa sz func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < count ==> val_in_memory stv (f i)
    (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_index_inv sa ("%" ++ toString sa.cs_next_var)
      src dst sw dw f stv dtv count s 0 t /\
    t.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `compile_copy_sarray_typed ce dst dty src sty N sa = ((),sz)` >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    typed_copy_loop_slice_locations >>
  disch_then (qspecl_then [`sa`, `sz`] mp_tac) >>
  disch_then (qspecl_then
    [`HD sc.cs_blocks`, `HD sb.cs_blocks`, `HD sz.cs_blocks`] mp_tac) >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK (jump_to cond (update_var ctr 0w s)))` by
    (irule typed_copy_counter_entry_path_mem >>
     conj_tac >- simp[] >>
     qexistsl_tac [`HD sc.cs_blocks`, `sa.cs_next_id`, `sa.cs_current_insts`] >>
     gvs[]) >>
  `~not_fresh_at sa ctr` by
    simp[not_fresh_at_def, toString_inj] >>
  qabbrev_tac `t = jump_to cond (update_var ctr 0w s)` >>
  `typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t` by
    (simp[Abbr `t`, typed_copy_state_frame_def, typed_copy_frame_def,
      jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      venom_state_component_equality] >>
     rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  qexists_tac `t` >>
  simp[typed_copy_index_inv_def, typed_copy_index_prefix_zero,
    Abbr `t`, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

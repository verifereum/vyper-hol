Theory bodyPtrStructLitEmpty
Ancestors
  vyperState vyperInterpreter vyperAST exprSimHypsDefs vyperTypeSystem vyperValue exprLowering context
  vyperTypeInvariants compileEnv loweringStateRelDefs bodyPtrDefs loweringPosts valueEncoding valueEncodingDefs finite_map list
  exprSimAlloc bodyPtrStructLitAlloc exprPtrUnwrap emitHelper emitHelperProps exprLoweringProps fragExec fragGasPathPtr venomInst venomState

Theorem structlit_empty_typing:
  well_typed_expr env (StructLit ann sid []) ==>
  ann = StructT sid /\
  FLOOKUP env.type_defs sid = SOME (StructArgs [])
Proof
  simp[well_typed_expr_def] >>
  rpt strip_tac >> Cases_on `args` >> gvs[]
QED

Theorem structlit_empty_type_evaluates:
  FLOOKUP tenv sid = SOME (StructArgs []) ==>
  evaluate_type tenv (StructT sid) = SOME (StructTV [])
Proof
  simp[evaluate_type_def, type_slot_size_def]
QED

Theorem structlit_empty_fields_compile:
  compile_struct_lit cfn cenv ty [] buf off st = (buf, st)
Proof
  simp[compile_struct_lit_def, comp_return_def]
QED

Theorem structlit_empty_body_pre_typing:
  expr_body_pre cenv cx env (StructLit ann sid []) es ==>
  ann = StructT sid /\
  FLOOKUP env.type_defs sid = SOME (StructArgs [])
Proof
  simp[expr_body_pre_def] >>
  metis_tac[structlit_empty_typing]
QED

Theorem structlit_empty_buffer_compile:
  compile_alloc_buffer 0 =
  do op <- emit_op ALLOCA [Lit 0w];
     return <| buf_operand := op; buf_size := 0 |>
  od
Proof
  simp[compile_alloc_buffer_def]
QED

Theorem structlit_empty_unwrap:
  unwrap_value cenv (LocatedValue (StructT sid) (base_ptr buf)) st =
  (buf.buf_operand, st)
Proof
  simp[unwrap_value_def, base_ptr_def, is_word_type_def, comp_return_def]
QED

Theorem structlit_empty_ptr_mem_ok:
  FLOOKUP (get_tenv cx) sid = SOME (StructArgs []) ==>
  ptr_mem_ok cx (StructT sid) (StructV []) op G tn s
Proof
  strip_tac >> simp[ptr_mem_ok_def, structlit_empty_type_evaluates,
    val_in_memory_def, val_footprint_def, type_memory_size_def]
QED

Theorem structlit_empty_layout:
  expr_body_pre cenv cx env (StructLit ann sid []) es ==>
  get_struct_fields cenv.ce_struct_fields (nsid_to_string sid) = []
Proof
  strip_tac >> drule structlit_empty_body_pre_typing >> strip_tac >>
  gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
      env_context_consistent_def] >>
  gvs[sfields_tenv_consistent_def] >>
  first_x_assum (drule_at (Pat `FLOOKUP _ sid = _`)) >>
  simp[get_struct_fields_def] >>
  rpt strip_tac >> Cases_on `fields` >> gvs[]
QED

Theorem structlit_empty_compile:
  expr_body_pre cenv cx env (StructLit ann sid []) es ==>
  compile_expr cenv ty (StructLit ann sid []) sa =
  do buf <- compile_alloc_buffer 0;
     return (LocatedValue ann (base_ptr buf))
  od sa
Proof
  strip_tac >> drule structlit_empty_layout >> strip_tac >>
  drule structlit_empty_body_pre_typing >> strip_tac >>
  simp[Once compile_expr_def, expr_type_def, compile_struct_lit_def,
       comp_return_def, comp_bind_def]
QED

Theorem structlit_empty_lower_value:
  expr_body_pre cenv cx env (StructLit ann sid []) es ==>
  lower_value compile_expr cenv ty (StructLit ann sid []) sa =
  do buf <- compile_alloc_buffer 0;
     return buf.buf_operand
  od sa
Proof
  strip_tac >> drule structlit_empty_body_pre_typing >> strip_tac >>
  gvs[] >> drule structlit_empty_compile >> strip_tac >>
  Cases_on `compile_alloc_buffer 0 sa` >>
  asm_rewrite_tac[lower_value_def] >>
  simp[comp_bind_def, comp_return_def, structlit_empty_unwrap]
QED

Theorem structlit_empty_eval:
  eval_expr cx (StructLit ann (src,id) []) es =
  (INL (Value (StructV [])), es)
Proof
  simp[Once evaluate_def, return_def, bind_def, ignore_bind_def] >>
  simp[Once evaluate_def, return_def, bind_def]
QED

Theorem structlit_empty_alloc_code:
  compile_alloc_buffer 0 sa = (buf,sb) ==>
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ALLOCA [Lit 0w]
       [STRING #"%" (toString sa.cs_next_var)]]
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >> rpt strip_tac >> gvs[]
QED

Theorem structlit_empty_alloc_path:
  compile_alloc_buffer 0 sa = (buf,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)]) t)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule structlit_empty_alloc_code >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id ALLOCA [Lit 0w]
       [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 0w]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def] >>
     gvs[AllCaseEqs()]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all structlit_alloca_counted_edge >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  `~t.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
       venomExecSemanticsTheory.exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
     simp[update_var_def] >> rpt strip_tac >> gvs[] >>
     gvs[AllCaseEqs(), update_var_def]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  simp[] >> disch_then irule >> simp[gas_path_ptr_rules]
QED

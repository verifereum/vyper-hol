Theory bodyPtrStructLitEmpty
Ancestors
  vyperState vyperInterpreter vyperAST exprSimHypsDefs vyperTypeSystem vyperValue exprLowering context
  vyperTypeInvariants compileEnv bodyPtrDefs loweringPosts valueEncoding finite_map list

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

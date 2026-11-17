Theory bodyFullUnwrapCodeCtorSemantic
Ancestors
  exprPtrUnwrapCodeCopySemantic exprSimCopy entrySinkExtraction abiDecodeStaticProps
  bodyFieldMemoryProps exprSimVVFrame exprPtrUnwrapAllocation exprLoweringProps
  emitHelperProps compileEnv venomState venomInst fragExec instIdxIndep
  loweringPosts loweringHalt exprLowering context finite_map list rich_list

Theorem ctor_unwrap_straight[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t ==>
  dec_straight sm sb
Proof
  strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, compile_ensure_in_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `dec_straight sm sb` >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  drule unwrap_alloc_current_block >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule code_ctor_copy_insts >> strip_tac >>
  `ci_mono sm mid` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono mid sb` by metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
  fs[dec_straight_def, ci_mono_def, same_blocks_def,
    inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND, EVERY_APPEND,
    mk_inst_def, is_terminator_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[EVERY_APPEND, mk_inst_def, is_terminator_def] >>
  fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem ctor_code_copy_endpoint_post:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ ~is_word_type t /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    type_memory_bytes cenv t = type_memory_size ty) /\
  vv_post H ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sb z ==>
  expr_post H ctx func cenv cx e es sa sb s0 ee v op z
Proof
  strip_tac >>
  drule_all ctor_unwrap_straight >> disch_tac >>
  drule_all unwrap_ctor_code_copy_sim >>
  disch_then (qspecl_then [`H`, `ctx`, `e`, `s0`, `v`, `(\r. F)`] assume_tac) >>
  drule frag_exec_straight_run >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  drule_all unwrap_code_copy_shifted_run >> disch_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (fs[dec_straight_def, EVERY_MEM] >> metis_tac[]) >>
  fs[run_inst_seq_inst_idx] >> gvs[exec_result_map_def]
QED

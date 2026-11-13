Theory bodyFullLiteralEndpoint
Ancestors
  bodyFullLiteralBuffer bodyLiteralBufferMemory bodyFullUnwrapRun
  exprSimLiteralBuffer exprSimMemDefs loweringPosts vyperAST
  fragGasSeqPtr fragExecMem exprLoweringProps venomMemDefs context vyperState
  list rich_list

Theorem literal_bytelike_full_path:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  drule_all literal_bytelike_alloca_mem >> strip_tac >>
  drule_all literal_bytelike_seq_mem >> strip_tac >>
  drule_all literal_bytelike_mem_path >> strip_tac >>
  drule_all literal_bytelike_gas_path >> strip_tac >>
  drule literal_bytelike_counted_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    gvs[EVERY_MEM, FILTER_EQ_NIL] >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  reverse conj_tac >- metis_tac[] >>
  irule emitted_origin_ptr_path >> conj_tac >- simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]
QED

Theorem literal_bytelike_full_memory:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  post_value_type cenv (Literal ann l) = ann /\ ~is_word_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size (LENGTH bs) /\
  (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
    mem_bytes_at (a+32) (LENGTH bs) mem = bs ==> val_in_memory tv v a mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  vv_post H ctx func cenv cx (Literal ann l) es sa sb s es (Value v)
    (LocatedValue ann (base_ptr buf))
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ?w. eval_operand buf.buf_operand t = SOME w /\
    w2n w + (32 + 32 * word_size (LENGTH bs)) <= t.vs_alloca_next
Proof
  strip_tac >>
  drule_all literal_bytelike_alloca_mem >> strip_tac >>
  drule_all literal_bytelike_run >> strip_tac >> gvs[] >>
  `val_in_memory tv v (w2n w) t.vs_memory` by metis_tac[] >>
  conj_tac
  >- (irule (SRULE [expr_type_def]
        (Q.INST [`e` |-> `Literal ann l`] (SPEC_ALL literal_memory_vv_post))) >>
      goal_assum (drule_at Any) >> simp[expr_type_def] >>
      metis_tac[]) >>
  `alloca_inv t` by gvs[stmt_state_rel_def] >>
  gvs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> simp[]
QED

Theorem literal_bytelike_full_endpoint:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32 + 32 * word_size (LENGTH bs) < dimword (:256) /\
  post_value_type cenv (Literal ann l) = ann /\ ~is_word_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size (LENGTH bs) /\
  val_store_size tv v <= 32 + 32 * word_size (LENGTH bs) /\
  (!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv (Literal ann l)) =
    SOME rt ==> type_memory_size rt <= 32 + 32 * word_size (LENGTH bs)) /\
  (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
    mem_bytes_at (a+32) (LENGTH bs) mem = bs ==> val_in_memory tv v a mem) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s G' tn') ==>
  !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
    vv_post H ctx func cenv cx (Literal ann l) es sa sb s es (Value v)
      (LocatedValue ann (base_ptr buf))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    vv_store_bound cx ann (lowered_value_type cenv (Literal ann l)) es
      (Value v) (LocatedValue ann (base_ptr buf))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
    (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  drule_all literal_bytelike_full_path >> strip_tac >>
  drule_all literal_bytelike_full_memory >> strip_tac >>
  simp[] >>
  simp[vv_store_bound_def, base_ptr_def, read_result_def, return_def] >>
  rpt strip_tac >> gvs[] >> disj2_tac >>
  first_x_assum drule >> strip_tac >> decide_tac
QED

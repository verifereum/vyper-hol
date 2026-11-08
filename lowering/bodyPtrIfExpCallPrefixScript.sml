Theory bodyPtrIfExpCallPrefix
Ancestors bodyPtrIfExpCallShape bodyPtrIfExpAllocationSite fragGasSeqPtr
  compileEnv context exprLowering emitHelper fragExec venomInst fragGasPathPtr

(* Inversion at a distinct endpoint, independent of gas-count positivity. *)
Theorem ifexp_normal_path_first_edge[local]:
  gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\ s <> t ==>
  ?k m J uj u.
    n = k + m /\ gas_path_ptr_edge D lo ctx fn PG G tn s k J uj (OK u) /\
    gas_path_ptr D lo ctx fn PG J uj u m H un (OK t)
Proof
  strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [gas_path_ptr_cases]) >>
  simp[exit_result_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ifexp_empty_call_positions:
  compile_call cfn ce ret_ty ty (IntCall fid) [] dret sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) INVOKE
       [Label (internal_fn_label (ce.ce_func_ids (nsid_to_string fid))
         (nsid_to_string fid) (ce.ce_func_param_types (nsid_to_string fid))
         ce.ce_is_ctor); Var (STRING #"%" (toString sa.cs_next_var))] []]
Proof
  simp[compile_call_def, compile_multi_vvs_def, compile_stage_intcall_args_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ifexp_empty_call_path_cut:
  compile_call cfn ce ret_ty ty (IntCall fid) [] dret sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs /\
  gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?k m J uj u.
    n = k + m /\ gas_path_ptr_edge D lo ctx fn PG G tn s k J uj (OK u) /\
    gas_path_ptr D lo ctx fn PG J uj u m H un (OK t)
Proof
  strip_tac >> drule_all ifexp_empty_call_positions >> strip_tac >>
  irule ifexp_normal_path_first_edge >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem ifexp_empty_call_fetch:
  compile_call cfn ce ret_ty ty (IntCall fid) [] dret sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
        [STRING #"%" (toString sa.cs_next_var)])
Proof
  strip_tac >> drule_all ifexp_empty_call_positions >> strip_tac >>
  fs[fn_has_code_def] >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  simp[get_instruction_def, listTheory.EL_APPEND_EQN]
QED


Theorem ifexp_ptr_edge_nonterminator:
  gas_path_ptr_edge D lo ctx fn PG G tn s k J uj (OK u) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode ==>
  ?fuel t. step_inst fuel ctx inst s = OK t /\ ~t.vs_halted /\
    u = (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    k = gas_count_step fuel ctx inst s /\
    ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
    (J,uj) = ghost_step fuel ctx PG G tn inst s
Proof
  strip_tac >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_ptr_edge_def]) >>
  gvs[]
  >- (qexistsl [`fuel`,`t`] >> simp[]) >>
  qpat_x_assum `OK u = _` (assume_tac o SYM) >>
  fs[exit_result_def]
QED

Theorem ifexp_empty_call_semantic_prefix:
  compile_call cfn ce ret_ty ty (IntCall fid) [] dret sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs /\
  fn_has_code sa sb fn /\
  gas_path_ptr D lo ctx fn PG G tn s n H un (OK t) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?k m J uj u fuel a.
    n = k + m /\ gas_path_ptr_edge D lo ctx fn PG G tn s k J uj (OK u) /\
    gas_path_ptr D lo ctx fn PG J uj u m H un (OK t) /\
    step_inst fuel ctx
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
        [STRING #"%" (toString sa.cs_next_var)]) s = OK a /\
    ~a.vs_halted /\ u = (a with vs_inst_idx := SUC s.vs_inst_idx) /\
    k = gas_count_step fuel ctx
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
        [STRING #"%" (toString sa.cs_next_var)]) s /\
    ptr_safe_step D lo fuel ctx fn PG G tn
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
        [STRING #"%" (toString sa.cs_next_var)]) s /\
    (J,uj) = ghost_step fuel ctx PG G tn
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
        [STRING #"%" (toString sa.cs_next_var)]) s
Proof
  strip_tac >>
  drule_all ifexp_empty_call_path_cut >> strip_tac >>
  drule_all ifexp_empty_call_fetch >> strip_tac >>
  `~is_terminator (mk_inst sa.cs_next_id ALLOCA [Lit (n2w rbs)]
     [STRING #"%" (toString sa.cs_next_var)]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all ifexp_ptr_edge_nonterminator >> strip_tac >>
  qexistsl [`k`,`m`,`J`,`uj`,`u`,`fuel`,`t'`] >> simp[]
QED

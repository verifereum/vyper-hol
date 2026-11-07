Theory exprSimIfExpWidenedCounted
Ancestors
  placeTypedCopyRecursivePath exprSimCopy exprSimStorageCopy typedMemoryCopy
  valueEncoding valueEncodingTyping vyperTypeSystem venomState
  exprSimAlloc fragGasSeq fragGasMode context emitHelperProps venomExecSemantics
  compileEnv emitHelper fragExec exprLoweringProps venomInst gasCount fragGasPath
  exprSimUnwrap exprSimAggregateChildren exprLowering loweringPosts vyperState
  valueCopyBytes vyperAST

Theorem typed_copy_semantic_frame:
  typed_copy_state_frame sa b sz s t /\
  stmt_state_rel ctx semantic_func ce cx ee s /\
  local_ptrs_reserved ce sa /\
  MEM inst (fn_insts semantic_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb len. local_region ce ee.scopes s name lb len ==>
    b + sz <= lb \/ lb + len <= b) ==>
  stmt_state_rel ctx semantic_func ce cx ee t
Proof
  strip_tac >> irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >>
  gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  gvs[venom_state_component_equality, copy_static_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem typed_store_counted_semantic_frame:
  compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb execution_func /\ fn_inst_ids_distinct execution_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx semantic_func ce cx ee s /\ local_ptrs_reserved ce sa /\
  MEM inst (fn_insts semantic_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size dtv) /\
  (!name lb len. local_region ce ee.scopes s name lb len ==>
    w2n dw + type_memory_size dtv <= lb \/ lb + len <= w2n dw) ==>
  ?t. gas_marked_path F ctx execution_func s 0 (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    stmt_state_rel ctx semantic_func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `val_wf stv v /\ val_wf dtv v` by metis_tac[value_has_type_val_wf] >>
  drule_all compile_store_memory_typed_forward_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  irule typed_copy_semantic_frame >>
  goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  metis_tac[]
QED

Theorem literal_alloc_buffer_counted:
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel ctx semantic_func ce cx ee s /\
  fn_inst_ids_distinct semantic_func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts semantic_func) /\
  fn_has_code sa sm execution_func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx execution_func s 0 (OK u) /\
    stmt_state_rel ctx semantic_func ce cx ee u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all literal_alloc_buffer_run >>
  strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]] /\
   emitted_insts sa sm =
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `gas_path_edge ctx execution_func s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) tuple_straight_line_edge >>
     simp[mk_inst_def] >> disch_then irule >>
     simp[is_terminator_def] >> gvs[mk_inst_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (`step_inst 0 ctx
       (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
         [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     drule_at (Pat `step_inst _ _ _ _ = _`)
       venomInstProofsTheory.step_preserves_control_flow >>
     drule_at (Pat `step_inst _ _ _ _ = _`)
       venomInstProofsTheory.step_preserves_halted >>
     simp[mk_inst_def, is_terminator_def]) >>
  `gas_marked_path F ctx execution_func s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_marked_path_def] >>
     drule (cj 2 gas_path_rules) >>
     disch_then (qspecl_then
       [`0`, `OK (t with vs_inst_idx := SUC s.vs_inst_idx)`] mp_tac) >>
     simp[] >> disch_then irule >>
     irule (cj 1 gas_path_rules) >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := SUC s.vs_inst_idx`, `w`] >>
  gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
      local_region_def] >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem unwrap_value_physical_path:
  (post_value_type ce e <> expr_type e ==>
    ((?t op. vv = StackValue t op) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
       ~is_word_type t))) /\
  unwrap_value ce vv sm = (op,sb) /\
  local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> dxrule_all vv_post_materialise >> strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (gvs[] >> drule_all (SRULE [] unwrap_value_path) >>
      simp[gas_marked_path_def]) >>
  first_x_assum (drule_at Any) >> strip_tac >>
  gvs[unwrap_value_def, comp_return_def] >>
  qexists_tac `s` >>
  simp[gas_marked_path_def, cj 1 gas_path_rules] >>
  gvs[vv_post_def, expr_post_def, vv_holds_def, vv_at_def, vv_own_def,
      expr_val_at_def, expr_val_own_def, expr_val_rel_def,
      read_result_def, return_def]
  >- (first_assum MATCH_ACCEPT_TAC)
  >- (first_assum MATCH_ACCEPT_TAC) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[is_bytestring_word_type] >>
  simp[] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_changed_physical_unwrap_shape:
  compile_expr ce ty e sc = (vv,sa) /\
  post_value_type ce e <> expr_type e /\
  ~is_word_type (post_value_type ce e) ==>
  (?t op. vv = StackValue t op) \/
  (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
    ~is_word_type t)
Proof
  strip_tac >> Cases_on `e` >> gvs[post_value_type_def] >>
  rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
  gvs[post_value_type_def, expr_type_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def, compile_expr_body_def, expr_type_def,
       compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `return_buf` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[contextTheory.base_ptr_def, oneline lowered_value_type_def] >>
  qpat_x_assum `(if _ then _ else _) <> _` mp_tac >>
  IF_CASES_TAC >> gvs[]
QED

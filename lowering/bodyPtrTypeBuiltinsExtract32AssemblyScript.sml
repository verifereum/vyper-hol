Theory bodyPtrTypeBuiltinsExtract32Assembly
Ancestors
  extract32Certificate
  bodyPtrTypeBuiltinsExtract32Suffix bodyPtrTypeBuiltinsExtract32Read exprSimExtract32Post
  bodyPtrDefs loweringPosts exprBopSimProps vyperTypeSystem vyperAST
  valueEncoding integer_word words freshWrites exprLowering compileEnv
  assignTuplePtrLoadStep appendStorageGhostPtr exprSimExtract32Read venomState
  exprSimExtract32Run exprSimExtract32Value varsExt builtinBytes list
  augAssignPtrScalarCertificate pred_set rawCallBufferPtr
  storageCopyGasPath gasSummaryComposePtr fragGasPathPtr vyperState vyperContext
  exprSimDefs fragGasMode rich_list exprLoweringProps fragExec exprSimHash exprSimHashBoundary

Theorem extract32_offset_scalar_view:
  expr_post H ctx func cenv cx off es sa sb s0 ee (IntV i) op s /\
  expr_type off = BaseT (UintT k) /\
  evaluate_type (get_tenv cx) (expr_type off) = SOME (BaseTV (UintT k)) /\
  0 <= i /\ ptr_val_ok cx (post_value_type cenv off) (IntV i) op G tn s ==>
  eval_operand op s = SOME (n2w (Num i)) /\
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  `post_value_type cenv off = expr_type off` by
    (irule post_value_type_word >> simp[]) >>
  `expr_val_rel cx (expr_type off) (IntV i) op s` by gvs[expr_post_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule_all expr_val_rel_typed >>
  simp[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_def,
    integerTheory.INT_NOT_LT] >>
  gvs[ptr_val_ok_def]
QED

(* The callback's natural p need not be canonical: use the word address
   preserved by the offset post, rather than assuming n2w is injective. *)
Theorem extract32_saved_source_nonwrap:
  expr_post H ctx func cenv cx src es sa sm s0 es1 (BytesV bs) srcop s1 /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  expr_post H ctx func cenv cx off es1 sm sb s1 es2 v offop s2 /\
  (!z. srcop = Var z ==> not_fresh_at sm z) /\ (!l. srcop <> Label l) /\
  eval_operand srcop s2 = SOME w ==>
  LENGTH bs < dimword(:256) /\ w2n w + 32 + LENGTH bs < dimword(:256)
Proof
  strip_tac >> drule_all extract32_source_post_view >> strip_tac >>
  `eval_operand srcop s2 = SOME (n2w p)` by
    metis_tac[extract32_post_operand_kept] >>
  `p < dimword(:256)` by decide_tac >>
  gvs[w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem extract32_tail_ghost_frame:
  compile_extract32_load len data offset sc = (raw,sd) /\
  compile_clamp_basetype raw typ sd = (result,se) /\
  run_inst_seq (emitted_insts sc se) s = OK t /\
  ghost_inv H d cenv cx ee G tn s /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ sa.cs_next_var <= sc.cs_next_var /\
  (!x. not_fresh_at sc x ==> FLOOKUP HG x = FLOOKUP G x /\
    op_taint th (Var x) = op_taint tn (Var x)) /\
  th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
  th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm ==>
  ghost_inv H d cenv cx ee HG th (t with vs_inst_idx := j) /\
  ghost_kept cenv es sa G0 tn0 s0 HG th
Proof
  strip_tac >>
  `(t with vs_vars := s.vs_vars) = s /\
   (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)` by
    (irule (INST_TYPE [``:'a`` |-> ``:operand``] extract32_read_success_frame_any) >>
     qexistsl_tac [`comp_bind (compile_extract32_load len data offset)
       (\r. compile_clamp_basetype r typ)`, `result`, `se`] >>
     simp[comp_bind_def] >> irule extract32_read_bind >>
     simp[extract32_read_load, extract32_read_clamp_basetype]) >>
  conj_tac
  >- (irule ghost_inv_old_vars_frame_ptr >>
      qexistsl_tac [`G`,`s`,`sc`,`tn`] >> simp[lookup_var_def] >>
      qpat_x_assum `_ with vs_vars := _ = _` mp_tac >>
      simp[venom_state_component_equality] >> gvs[lookup_var_def]) >>
  irule ghost_kept_suffix_compose >> goal_assum (drule_at Any) >>
  simp[]
QED

Theorem extract32_tail_outcome_of_runs_ptr:
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw (BaseT bt) sm = (op,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  es.gas_obs = [] /\ inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s HG th /\
  (case evaluate_extract32 bs n bt of
    INL v => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      Q (INL (Value v)) es HG th (t with vs_inst_idx := LENGTH sb.cs_current_insts)
  | INR err => ?msg t. err = RuntimeError msg /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (vyperState$bind
      (lift_sum (evaluate_extract32 bs n bt)) (\v. return (Value v)))
    (es,s,G,tn) Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all extract32_tail_straight_noext >> strip_tac >>
  `same_blocks sa sb` by simp[same_blocks_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[storage_copy_code_prefix] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `isPREFIX sa.cs_current_insts sb.cs_current_insts`
       (mp_tac o MATCH_MP IS_PREFIX_LENGTH) >>
     simp[emitted_insts_def]) >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  Cases_on `evaluate_extract32 bs n bt`
  >- suspend "success" >> suspend "error"
QED

Resume extract32_tail_outcome_of_runs_ptr[success]:
  gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all extract32_tail_normal_ptr_path >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value x)`,`es`,`HG`,`th`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[lift_sum_def, bind_def, return_def] >> gvs[]
QED

Resume extract32_tail_outcome_of_runs_ptr[error]:
  gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all extract32_tail_abort_ptr_path >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `REPLICATE n' F` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`es`,`HG`,`th`,
    `Abort Revert_abort (t with vs_inst_idx := j)`] >>
  simp[lift_sum_def, bind_def, raise_def, expr_exit_def, exit_result_def]
QED

Finalise extract32_tail_outcome_of_runs_ptr

Theorem extract32_tail_post_of_run:
  expr_post H ctx func cenv cx src es sa sm s0 es1 (BytesV bs) srcop s1 /\
  expr_post H ctx func cenv cx off es1 sm sc s1 ee (IntV i) offop s /\
  compile_extract32_load len dp offop sc = (raw,sd) /\
  compile_clamp_basetype raw typ sd = (op,se) /\
  run_inst_seq (emitted_insts sc se) s = OK t /\
  eval_operand op t = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv ==>
  vv_post H ctx func cenv cx (TypeBuiltin ann Extract32 typ [src;off])
    es sa se s0 ee (Value v) (StackValue ty op) t
Proof
  strip_tac >>
  `(t with vs_vars := s.vs_vars) = s /\
   (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)` by
    (irule (INST_TYPE [``:'a`` |-> ``:operand``] extract32_read_success_frame_any) >>
     qexistsl_tac [`comp_bind (compile_extract32_load len dp offop)
       (\r. compile_clamp_basetype r typ)`, `op`, `se`] >>
     simp[comp_bind_def] >> irule extract32_read_bind >>
     simp[extract32_read_load, extract32_read_clamp_basetype]) >>
  `stmt_state_rel H ctx func cenv cx ee t` by
    (irule hash_readonly_state_rel >> qexistsl_tac [`s`,`sc`] >> gvs[expr_post_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_assum `_ with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  irule extract32_posts_to_vv_post_frame >>
  qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem extract32_saved_source_view:
  expr_post H ctx func cenv cx src es sa sm s0 es1 (BytesV bs) srcop s1 /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  expr_post H ctx func cenv cx off es1 sm sb s1 es2 v offop s2 /\
  (!z. srcop = Var z ==> not_fresh_at sm z) /\ (!l. srcop <> Label l) /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) srcop G tn s2 /\
  eval_operand srcop s2 = SOME (n2w p) /\
  eval_operand dataop s2 = SOME (n2w (p+32)) ==>
  ?q. eval_operand srcop s2 = SOME (n2w q) /\
    eval_operand dataop s2 = SOME (n2w (q+32)) /\
    val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) q s2.vs_memory /\
    LENGTH bs < dimword(:256) /\ q+32+LENGTH bs < dimword(:256)
Proof
  strip_tac >> drule_all extract32_saved_source_nonwrap >> strip_tac >>
  qexists_tac `w2n (n2w p:bytes32)` >> simp[] >>
  `n2w (w2n (n2w p:bytes32)+32):bytes32 = n2w (p+32)` by
    (rewrite_tac[GSYM word_add_n2w] >> simp[]) >> simp[] >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >> strip_tac >> first_x_assum irule >>
  simp[mem_agree_outside_def]
QED

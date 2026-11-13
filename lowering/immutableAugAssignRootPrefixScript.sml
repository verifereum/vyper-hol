(* Compilation and safe load prefix for a constructor immutable scalar. *)
Theory immutableAugAssignRootPrefix
Ancestors
  augAssignPlaceCompileMemory
  bodyDeclMemoryCounted allocaFootprint emitHelperProps exprLoweringProps
  exprLowering compileEnv venomState venomInst fragGasMode venomExecSemantics
  loweringStateRelDefs

Theorem immutable_augassign_root_compilation:
  stmt_env cenv lctx ret_ty
    (AugAssign ty (TopLevelNameTarget nsid) bop e) sa = (c,sf) /\
  fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
  FLOOKUP cenv.ce_module_vars nsid = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type nsid = SOME ty ==>
  c = cenv /\
  ?cur rhs result s1 s2 s3.
    emit_op MLOAD [Lit (n2w off)] sa = (cur,s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
    compile_binop bop cur rhs ty NONE
      (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
    emit_void MSTORE [Lit (n2w off);result] s3 = ((),sf) /\
    ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
    local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
    local_ptrs_reserved cenv s3 /\
    (!z. not_fresh_at sa z ==> not_fresh_at s1 z) /\
    (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
    (!z. not_fresh_at s2 z ==> not_fresh_at s3 z)
Proof
  strip_tac >> drule_all aug_place_compilation_mem >>
  simp[compile_get_target_ptr_def, comp_return_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem immutable_root_mload_path_mem[local]:
  emit_op MLOAD [Lit w] sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n w + 32 <= s.vs_alloca_next ==>
  gas_marked_path T ctx func s 0
    (OK (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s
      with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func
    (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s
      with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s)` by
    (`step_inst_base (mk_inst sa.cs_next_id MLOAD [Lit w]
        [STRING #"%" (toString sa.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s)` by
      (irule step_MLOAD >> simp[eval_operand_def]) >>
     simp[run_inst_seq_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (metis_tac[eval_operand_def, emit_mload_mem_ok]) >>
  conj_tac
  >- (simp[gas_marked_path_def] >>
      drule_at (Pat `run_inst_seq _ _ = _`) body_decl_zero_gas_path >> simp[]) >>
  irule bodyDeclMemoryCoreTheory.body_store_memory_history >> simp[] >>
  qexistsl [`s`, `sa`] >> fs[listTheory.EVERY_MEM]
QED

Theorem immutable_augassign_root_prefix_mem:
  emit_op MLOAD [Lit w] sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n w + 32 <= s.vs_alloca_next ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ alloca_history func u /\
    eval_operand op u = SOME (mload (w2n w) s) /\
    (!z. op = Var z ==> not_fresh_at sb z) /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
    (!l. op <> Label l)
Proof
  strip_tac >> drule_all immutable_root_mload_path_mem >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists `sa` >> simp[]) >>
  qexists `update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[]) >>
  drule emit_op_same_blocks >>
  simp[same_blocks_def, update_var_def, eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

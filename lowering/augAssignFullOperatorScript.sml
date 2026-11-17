(* Typed operator execution and joint resources share one actual endpoint. *)
Theory augAssignFullOperator
Ancestors
  augAssignFullOperatorExec augAssignFullOperatorNormal augAssignFullOperatorAbrupt
  augAssignFullScalarSuccess augAssignFullScalarAbort augAssignPtrCompiler
  fragGasFresh freshWrites varsExt bodyUnopFragMemory exprBopSimProps
  exprSimDefs loweringPosts bodyFullTargetDefs bodyPtrDefs ptrDiscipline
  venomExecSemantics venomState venomInst compileEnv finite_map pred_set list rich_list

Theorem augassign_operator_joint_success:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  type_bits ty MOD 8 = 0 /\ is_word_type ty /\
  (bop = Exp ==>
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==>
    (?i. v2 = IntV i /\ 0 <= i) \/
    (ty = BaseT (BytesT (Fixed 32)) /\ ?bs. v2 = BytesV bs /\ LENGTH bs = 32)) /\
  evaluate_type (get_tenv cx) ty = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type (get_tenv cx) t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  bop_result cx ty bop tys v1 v2 es = INL v /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fn_has_code sa sb func /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  (!l. x <> Label l /\ y <> Label l) /\
  eval_operand x s = SOME (typed_val_to_w256 tv1 v1) /\
  eval_operand y s = SOME (typed_val_to_w256 tv2 v2) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (!z. FST r = Var z ==> not_fresh_at sa z) /\
  eval_operand (FST r) s = SOME addr /\ target_ptr_ok cenv (PlaceR p) r G tn s
  ==>
  ?u G' tn'.
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn') /\
      stmt_state_rel H ctx func cenv cx es u /\
      storage_well_formed_on cx es (FST H) /\
      expr_val_rel cx ty v op u /\ eval_operand op u = SOME (typed_val_to_w256 tv1 v) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z u = SOME w) /\
      u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
      u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
      return_buf_frame d cenv sb u /\ alloca_history func u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' u /\
      ghost_kept_at lo cenv es sa G tn s G' tn' /\
      eval_operand (FST r) u = SOME addr /\
      eval_operand x u = SOME (typed_val_to_w256 tv1 v1) /\
      target_ptr_ok cenv (PlaceR p) r G' tn' u /\
      op_taint tn' x = {} /\ op_prov G' x = NONE /\
      op_prov G' op = NONE /\ op_taint tn' op = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
    UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt; GtE;
    Exp; Min; Max; In; NotIn]` by metis_tac[typed_binop_scalar_member_ptr] >>
  `straight_fresh (compile_binop bop x y ty bl el)` by
    metis_tac[compile_binop_straight_fresh_ptr] >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (qpat_assum `writes_fresh _ _` mp_tac >>
     simp_tac std_ss [writes_fresh_def, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >>
     simp[fresh_write_op_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by metis_tac[writes_fresh_mem_ok] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0 /\
        expr_val_rel cx ty v op t0` by suspend "execution" >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand op t0 = SOME (typed_val_to_w256 tv1 v)` by
    metis_tac[expr_val_rel_typed] >>
  drule_all compile_binop_clean_certificate_ptr >> strip_tac >>
  `?G' tn'.
    (!D lo explicit. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z))` by suspend "uniform" >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G'`, `tn'`] >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  conj_tac >- (first_x_assum irule >> gvs[ghost_inv_at_def]) >>
  irule augassign_operator_normal_resources >> simp[] >>
  goal_assum (drule_at (Pat `straight_fresh _`)) >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Resume augassign_operator_joint_success[execution]:
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s) = SOME (typed_val_to_w256 tv1 v1) /\
   eval_operand y (drop_fresh sa s) = SOME (typed_val_to_w256 tv2 v2)` by
    metis_tac[eval_operand_drop_fresh] >>
  `expr_res_ok (bop_result cx ty bop tys v1 v2 es)` by simp[expr_res_ok_def] >>
  drule_all augassign_typed_execution >> gvs[] >> metis_tac[]
QED

Resume augassign_operator_joint_success[uniform]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    gvs[EVERY_MEM] >>
  drule_all augassign_scalar_success_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!D lo explicit. _` (qspecl_then [`D`, `lo'`, `explicit`] mp_tac) >>
      simp[LENGTH_APPEND]) >>
  simp[] >> rpt strip_tac >>
  `~MEM z (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb)))` by
    (qpat_assum `writes_fresh _ _` mp_tac >>
     simp_tac std_ss [writes_fresh_def, EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >> metis_tac[]
QED

Finalise augassign_operator_joint_success


Theorem augassign_operator_joint_error:
  well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn /\
  type_bits ty MOD 8 = 0 /\ is_word_type ty /\
  (bop = Exp ==>
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==>
    (?i. v2 = IntV i /\ 0 <= i) \/
    (ty = BaseT (BytesT (Fixed 32)) /\ ?bs. v2 = BytesV bs /\ LENGTH bs = 32)) /\
  evaluate_type (get_tenv cx) ty = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type (get_tenv cx) t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  bop_result cx ty bop tys v1 v2 es = INR (Error (RuntimeError msg)) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fn_has_code sa sb func /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  (!l. x <> Label l /\ y <> Label l) /\
  eval_operand x s = SOME (typed_val_to_w256 tv1 v1) /\
  eval_operand y s = SOME (typed_val_to_w256 tv2 v2) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s)
  ==>
  ?u G' tn'.
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort u,G',tn') /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      allocas_from lo u /\ lo <= u.vs_alloca_next /\
      expr_exit (INR (Error (RuntimeError msg))) (Abort Revert_abort u) /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail)
        (INR (Error (RuntimeError msg))) gt (Abort Revert_abort u)) /\
      halt_exit H cx ee (INR (Error (RuntimeError msg))) (Abort Revert_abort u) /\
      (ctx_has_dalloca ctx ==>
        !v. (Abort Revert_abort u = Halt v \/
             ?ir. Abort Revert_abort u = IntRet ir v) ==> allocas_below_fmp v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
    UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt; GtE;
    Exp; Min; Max; In; NotIn]` by metis_tac[typed_binop_scalar_member_ptr] >>
  `straight_fresh (compile_binop bop x y ty bl el)` by
    metis_tac[compile_binop_straight_fresh_ptr] >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (qpat_assum `writes_fresh _ _` mp_tac >>
     simp_tac std_ss [writes_fresh_def, EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >>
     simp[fresh_write_op_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by metis_tac[writes_fresh_mem_ok] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `?t0. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) =
        Abort Revert_abort t0` by suspend "execution" >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  simp[vars_ext_result_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort abort_state` >>
  drule_all compile_binop_clean_certificate_ptr >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    gvs[EVERY_MEM] >>
  drule_all augassign_scalar_abort_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`abort_state with vs_inst_idx := j`, `G'`, `tn'`] >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  conj_tac >- (first_x_assum irule >> gvs[ghost_inv_at_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA)
    (emitted_insts sa sb)` by gvs[EVERY_MEM] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by gvs[ghost_inv_at_def] >>
  drule_all (SRULE [] (Q.INST [`res` |-> `INR (Error (RuntimeError msg))`]
    (SPEC_ALL augassign_operator_abrupt_resources))) >>
  disch_then (fn th => simp[th, expr_exit_def, stmt_exit_ptr_def]) >>
  irule haltExitProjTheory.halt_exit_not_halt >> simp[]
QED

Resume augassign_operator_joint_error[execution]:
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa s) = SOME (typed_val_to_w256 tv1 v1) /\
   eval_operand y (drop_fresh sa s) = SOME (typed_val_to_w256 tv2 v2)` by
    metis_tac[eval_operand_drop_fresh] >>
  `expr_res_ok (bop_result cx ty bop tys v1 v2 es)` by simp[expr_res_ok_def] >>
  drule_all augassign_typed_execution >> gvs[] >> metis_tac[]
QED

Finalise augassign_operator_joint_error

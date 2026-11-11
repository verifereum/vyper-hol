(* Memory-checked, read-only len suffix. *)
Theory bodyMemBiLenPath
Ancestors
  bodyMemBiLenSafety exprSimLen exprSimSource exprSimProps exprSimHypsDefs
  exprSimDefs loweringPosts list fragExec exprSimHyps exprSimWordBuiltins
  exprBopLowering exprLowering exprLoweringProps builtinSimple emitHelper
  compileEnv accountsRelProps valueEncoding venomExecSemantics venomInst
  venomState vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeBuiltins vyperValue vyperTyping vyperStorage builtinProps
  vyperTypeInvariants context freshWrites loweringSlice emitHelperProps
  exprSimUnwrap exprSimCopy vyperTypeExprResult vyperTypeExprSoundness
  vyperExprNoControl gasContext gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath exprSimBopRestWordLoadPath
  fragGasSeqMem fragGasPathMem fragExecMem allocaHistoryFragment allocaHistory
  words rich_list finite_map exprSimBopRestWordLayout
  stmtSimAppendStorageCompose stateFrame

Theorem len_ptr_load_path_mem:
  compile_ptr_load ctor imm loc addr sa = (op,sb) /\
  loc <> LocCalldata /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand op t = SOME value /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
      eval_operand op u = SOME value /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!i. MEM i (emitted_insts sa sb) ==> ~MEM x i.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x) /\
      alloca_history func u /\ u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all rest_word_ptr_load_code >> strip_tac >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  drule_all rest_word_ptr_load_run_frame >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by simp[] >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, venom_state_component_equality]
QED

Theorem len_vv_path_mem:
  !env ctx func cenv cx e es sa sm sb s0 es' tv vv op tvt t.
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of SOME l => l | NONE => LocMemory) sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    is_sized_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,es') tv (Type (expr_type e)) /\
    (!v. read_result cx tv es' = (INL v,es') ==> value_has_type tvt v) /\
    fn_has_code sm sb func /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv t /\
    fn_inst_ids_distinct func /\ alloca_history func t /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' tv vv t ==>
    ?t' n. gas_path_mem ctx func t 0 (OK t') /\
      t'.vs_current_bb = sb.cs_current_bb /\
      t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      result_array_length cx tv es' = (INL n,es') /\
      vv_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e]) es
        sa sb s0 es' (Value (IntV (&n)))
        (StackValue (BaseT (UintT 256)) op) t' /\
      alloca_history func t' /\ t'.vs_alloca_next = t.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' t /\
   vv_holds cenv cx (expr_type e) tv vv es' t` by fs[vv_post_def] >>
  drule_all vv_holds_sized_length_success >> strip_tac >>
  drule_all vv_holds_len_header >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule len_load_mem_ok >> metis_tac[]) >>
  drule len_vv_not_calldata >> strip_tac >>
  gvs[compile_builtin_len_def] >>
  `(cenv.ce_is_ctor /\ cenv.ce_imm_alloca <> NONE ==>
    eval_operand (THE cenv.ce_imm_alloca) t = SOME 0w)` by
    (fs[stmt_state_rel_def, immutable_base_zero_def] >>
     Cases_on `cenv.ce_imm_alloca` >> gvs[]) >>
  drule rest_word_ptr_load_run >>
  disch_then (qspecl_then [`n2w n`, `t`, `0w`, `w`] mp_tac) >>
  impl_tac
  >- (simp[] >>
      Cases_on `vv_location vv` >> gvs[ptr_load_val_def] >>
      Cases_on `x` >> gvs[ptr_load_val_def] >>
      Cases_on `cenv.ce_is_ctor` >> gvs[ptr_load_val_def, WORD_ADD_0]) >>
  strip_tac >> rename1 `run_inst_seq _ t = OK u` >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  drule_all len_ptr_load_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem _ _ t 0 (OK t')` >>
  `!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
          lookup_var x t' = SOME w` by
    (drule rest_word_ptr_load_fresh >> strip_tac >>
     fs[EVERY_MEM, lookup_var_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es' t'` by
    (`stmt_state_rel ctx func cenv cx es'
        (t' with vs_inst_idx := t.vs_inst_idx)` suffices_by
       simp[stmt_state_rel_inst_idx] >>
     `state_frame (t' with vs_inst_idx := t.vs_inst_idx) = state_frame t` by
       (qpat_assum `t' = _` (fn th => pure_once_rewrite_tac[th]) >>
        simp[state_frame_def]) >>
     qpat_x_assum `t' = _` kall_tac >>
     irule stmt_state_rel_reserved_frame >>
     qexistsl [`t`, `sm`] >> pure_asm_rewrite_tac[] >>
     simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  qexists_tac `t'` >> simp[] >>
  irule len_vv_post_load >> simp[] >>
  qexistsl [`t`, `sm`, `tv`, `vv`] >> simp[] >>
  qpat_x_assum `t' = _` (fn th => pure_once_rewrite_tac[th]) >> simp[]
QED

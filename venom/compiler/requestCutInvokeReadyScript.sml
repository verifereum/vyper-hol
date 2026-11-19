Theory requestCutInvokeReady
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNormCursors cfgNormSupplySim
  dftWf o1PassContract unitShapeDefs o1ScheduleDecompHelpers venomWfProps
  stackPlanTypes venomWf venomInst contextCodegenRel venomExecProofs venomExecSemantics venomState finite_map list

Theorem supply_cursor_use_defined:
  wf_ssa fn /\ wf_function fn /\ supply_prefix_defined fn s /\
  active_inst fn inst s /\ inst.inst_opcode <> PHI /\
  MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars
Proof
  strip_tac >>
  qpat_x_assum `active_inst fn inst s` (strip_assume_tac o REWRITE_RULE[active_inst_def]) >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `def_available_at fn bb (SOME inst) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  qpat_x_assum `def_available_at _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [def_available_at_def]) >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
        metis_tac[wf_fn_block_inst_ids_distinct] >>
      `j = s.vs_inst_idx` by
        metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP] >>
      fs[supply_prefix_defined_def] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  `def_bb.bb_label <> bb.bb_label` by metis_tac[same_label_same_block] >>
  fs[supply_prefix_defined_def, supply_entry_defined_def, strict_dom_vars_defined_def] >>
  metis_tac[]
QED

Theorem cfg_norm_joint_cursor_supply:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved) q8
    (JointConfig stk PG G tn fn inst s oms om hs h) ==>
  MEM fn C9.ctx_functions /\ wf_ssa fn /\ wf_function fn /\
  EVERY label_positions_ok (fn_insts fn) /\ active_inst fn inst s /\
  supply_prefix_defined fn s
Proof
  strip_tac >> Cases_on `q8` >>
  fs[cfg_norm_joint_cursors_def] >>
  `MEM fn C9.ctx_functions` by
    (qpat_assum `MAP (FST o SND) schedules = _` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  rename1 `MEM (sf,fn,rounds) schedules` >>
  `?u. LAST rounds = (u,fn,NONE)` by
    (qpat_x_assum `EVERY _ schedules` (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
     disch_then (qspec_then `(sf,fn,rounds)` mp_tac) >> simp[] >> metis_tac[]) >>
  `wf_ssa fn /\ wf_function fn /\ EVERY label_positions_ok (fn_insts fn) /\
   active_inst fn inst s /\ supply_prefix_defined fn s` by
    (drule cfg_norm_cursors_last >> strip_tac >>
     metis_tac[supply_norm_inv_def, pairTheory.PAIR_EQ]) >>
  simp[]
QED

Theorem request_cut_stopped_invoke_ready:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved) q8
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape C9 /\ inst.inst_opcode = INVOKE ==>
  ?callee_name ops callee args ent.
    decode_invoke inst = SOME (callee_name,ops) /\
    lookup_function callee_name C9.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME ent
Proof
  strip_tac >> drule cfg_norm_joint_cursor_supply >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `o1_fn_shape C9 fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `?name ops. inst.inst_operands = Label name :: ops /\ MEM name (ctx_fn_names C9)` by
    (fs[o1_fn_shape_def, fn_invoke_ok_def] >> metis_tac[]) >>
  `EVERY (\op. ~is_label_operand op) ops` by
    (`label_positions_ok inst` by metis_tac[EVERY_MEM] >>
     qpat_x_assum `label_positions_ok inst` mp_tac >>
     simp[label_positions_ok_def]) >>
  `!v. MEM (Var v) ops ==> v IN FDOM s.vs_vars` by
    (rpt strip_tac >> irule supply_cursor_use_defined >>
     qexistsl_tac [`fn`,`inst`] >> simp[]) >>
  `IS_SOME (eval_operands ops s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
     Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_DEF] >>
     IF_CASES_TAC >> fs[EVERY_MEM] >> metis_tac[is_label_operand_def]) >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C9.ctx_functions)` by
    fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  `?callee. MEM callee C9.ctx_functions /\ callee.fn_name = name` by
    (fs[ctx_fn_names_def, MEM_MAP] >> metis_tac[]) >>
  `lookup_function name C9.ctx_functions = SOME callee` by
    metis_tac[lookup_function_member_iff] >>
  `o1_fn_shape C9 callee` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `~NULL callee.fn_blocks` by fs[o1_fn_shape_def, wf_function_def, fn_has_entry_def, NULL_EQ] >>
  simp[decode_invoke_def, setup_callee_def]
QED

Theory loweringCallOpcodes
Ancestors list pair vyperAST exprLowering compileEnv context venomInst
  loweringShapeDefs loweringShapeProps exprCallbackContracts supportedExprTraverse
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks
  loweringCallArgsOpcodes loweringExtCallOpcodes builtinSystem

Theorem call_callback_child_supported:
  MEM child (call_callback_children args d) /\
  ~supported_expr_exists R (Call ann target args d) ==>
  ~supported_expr_exists R child
Proof
  strip_tac >> fs[supported_expr_exists_def] >>
  Cases_on `MEM child args`
  >- metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  Cases_on `MEM child (case d of NONE => [] | SOME x => [x])`
  >- (Cases_on `d` >> gvs[supported_expr_exists_def]) >>
  `?topic_expr. MEM topic_expr args /\ MEM child (raw_log_topic_exprs topic_expr)` by
    (fs[call_callback_children_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `~supported_expr_exists R topic_expr` by
    metis_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  Cases_on `topic_expr` >> gvs[raw_log_topic_exprs_def] >>
  qmatch_asmsub_rename_tac `raw_log_topic_exprs (Builtin topic_ann bi es)` >>
  Cases_on `bi` >>
  gvs[raw_log_topic_exprs_def, supported_expr_exists_def] >>
  metis_tac[supported_exprs_exists_every, EXISTS_MEM]
QED

Theorem opcode_every_intcall:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\ P INVOKE /\
  (!e ty st. MEM e args ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_call cfn ce rt ty (IntCall id) args d st)))
Proof
  strip_tac >>
  qabbrev_tac `info = ce.ce_func_info (nsid_to_string id)` >>
  PairCases_on `info` >>
  qpat_x_assum `Abbrev _`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `!ops n st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (emit_multi_op INVOKE ops n st)))` by
    simp[every_state_insts_emit_multi_op, mk_inst_def] >>
  simp[compile_call_def] >> rpt strip_tac >>
  rpt (FIRST [pairarg_tac >> gvs[], IF_CASES_TAC >> gvs[], CASE_TAC >> gvs[]]) >>
  metis_tac[UNDISCH opcode_every_alloc_buffer,
    UNDISCH opcode_every_stage_intcall_args,
    UNDISCH opcode_every_store_multi_results,
    opcode_every_emit_op, opcode_every_emit_void, SND]
QED

Theorem opcode_every_extcall:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\ P RETURNDATACOPY /\
  (!e ty st. MEM e args ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_call cfn ce rt ty
        (ExtCall static skip (name,tys,ret) kws) args d st)))
Proof
  strip_tac >> Cases_on `args`
  >- (simp[compile_call_def] >> rpt strip_tac >> pairarg_tac >> gvs[] >>
      `P INVALID` by simp[] >> metis_tac[opcode_every_emit_inst, SND]) >>
  rename1 `h::t` >>
  `!e ety. MEM e (h::t) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn ce ety e st)))` by
    (rpt gen_tac >> strip_tac >> ho_match_mp_tac every_state_insts_lower_value >>
     simp[UNDISCH opcode_every_unwrap_value]) >>
  `!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_ext_call_args cfn ce (DROP (LENGTH tys) t)
        (MAP (lowered_value_type ce) (TAKE (LENGTH tys) t))
        (TAKE (LENGTH tys) t) st)))` by
    (ho_match_mp_tac (Q.SPECL [`TAKE (LENGTH tys) t`,
       `MAP (lowered_value_type ce) (TAKE (LENGTH tys) t)`, `cfn`, `ce`,
       `DROP (LENGTH tys) t`] (UNDISCH opcode_every_ext_call_args)) >>
     rpt strip_tac >>
     first_x_assum irule >> metis_tac[rich_listTheory.MEM_TAKE, MEM]) >>
  `!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_ext_call_kwargs cfn ce ret kws (DROP (LENGTH tys) t) st)))` by
    (ho_match_mp_tac (Q.SPECL [`DROP (LENGTH tys) t`, `kws`, `cfn`, `ce`, `ret`]
       (UNDISCH opcode_every_ext_call_kwargs)) >> rpt strip_tac >>
     first_x_assum irule >> metis_tac[rich_listTheory.MEM_DROP_IMP, MEM]) >>
  simp[compile_call_def] >> rpt strip_tac >>
  rpt (FIRST [pairarg_tac >> gvs[], IF_CASES_TAC >> gvs[], BasicProvers.FULL_CASE_TAC >> gvs[]]) >>
  `P GAS` by simp[] >>
  metis_tac[opcode_every_external_call_kwargs, opcode_every_emit_op, SND]

QED

Theorem opcode_every_send:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\
  (!e ty st. MEM e args ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_call cfn ce rt ty (Send gas) args d st)))
Proof
  strip_tac >>
  `!e ety. MEM e (args) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn ce ety e st)))` by
    (rpt gen_tac >> strip_tac >> ho_match_mp_tac every_state_insts_lower_value >>
     simp[UNDISCH opcode_every_unwrap_value]) >>
  simp[compile_call_def] >> rpt strip_tac >>
  rpt (FIRST [pairarg_tac >> gvs[], IF_CASES_TAC >> gvs[],
    BasicProvers.FULL_CASE_TAC >> gvs[]]) >>
  `P INVALID /\ P CALL /\ P ASSERT` by simp[] >>
  metis_tac[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst, SND]

QED

Theorem opcode_every_raw_revert_data[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_raw_revert data st)))
Proof
  strip_tac >> simp[compile_raw_revert_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_inst])])
QED

Theorem opcode_every_raw_revert:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\
  (!e ty st. MEM e args ==> EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_call cfn ce rt ty RawRevert args d st)))
Proof
  strip_tac >>
  `!e ety. MEM e (args) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn ce ety e st)))` by
    (rpt gen_tac >> strip_tac >> ho_match_mp_tac every_state_insts_lower_value >>
     simp[UNDISCH opcode_every_unwrap_value]) >>
  simp[compile_call_def] >> rpt strip_tac >>
  rpt (FIRST [pairarg_tac >> gvs[], BasicProvers.FULL_CASE_TAC >> gvs[]]) >>
  `P INVALID` by simp[] >>
  metis_tac[UNDISCH opcode_every_raw_revert_data, opcode_every_emit_inst, SND]

QED

Theorem opcode_every_raw_log:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\
  (!e ty st. MEM e (args ++ FLAT (MAP raw_log_topic_exprs args)) ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_call cfn ce rt ty RawLog args d st)))
Proof
  strip_tac >>
  `!e ety. MEM e (args ++ FLAT (MAP raw_log_topic_exprs args)) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn ce ety e st)))` by
    (rpt gen_tac >> strip_tac >> ho_match_mp_tac every_state_insts_lower_value >>
     simp[UNDISCH opcode_every_unwrap_value]) >>
  `!topic_expr. MEM topic_expr args ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_multi_exprs cfn ce (raw_log_topic_exprs topic_expr) st)))` by
    (rpt gen_tac >> strip_tac >>
     ho_match_mp_tac (Q.SPECL [`raw_log_topic_exprs topic_expr`, `cfn`, `ce`]
       (MATCH_MP (UNDISCH opcode_every_multi_exprs)
         (Q.GENL [`ce`, `vv`, `st`] (UNDISCH opcode_every_unwrap_value)))) >>
     rpt strip_tac >> first_x_assum irule >>
     simp[MEM_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  simp[compile_call_def] >> rpt strip_tac >>
  rpt (FIRST [pairarg_tac >> gvs[], IF_CASES_TAC >> gvs[],
    BasicProvers.FULL_CASE_TAC >> gvs[]]) >>
  `P INVALID /\ P MLOAD /\ P ADD /\ P MSTORE /\ P LOG` by simp[] >>
  metis_tac[UNDISCH opcode_every_alloc_buffer,
    opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst, SND]

QED

Theorem opcode_every_call:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) /\
  P INVOKE /\ P RETURNDATACOPY /\
  ~expr_shape_root (Call ann target args d) /\
  (!e ty st. MEM e (call_callback_children args d) ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn ce ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_call cfn ce rt ty target args d st)))
Proof
  strip_tac >> Cases_on `target` >> gvs[expr_shape_root_def] >>
  all_tac >~ [`compile_call _ _ _ _ (ExtCall _ _ signature _) _ _ _`] >-
    (PairCases_on `signature` >> ho_match_mp_tac opcode_every_extcall >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     gvs[call_callback_children_def] >> metis_tac[MEM_APPEND]) >>
  FIRST [ho_match_mp_tac opcode_every_intcall, ho_match_mp_tac opcode_every_extcall,
    ho_match_mp_tac opcode_every_send, ho_match_mp_tac opcode_every_raw_log,
    ho_match_mp_tac opcode_every_raw_revert] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[call_callback_children_def] >> metis_tac[MEM_APPEND]
QED

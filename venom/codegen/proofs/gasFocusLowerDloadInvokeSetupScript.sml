(* Pointwise correlated call setup at one selected source/target caller. *)
Theory gasFocusLowerDloadInvokeSetup
Ancestors
  lowerDloadReturnInvokePush lowerDloadReturnInvokeArguments
  lowerDloadReturnInvokeStack lowerDloadSafetyArguments lowerDloadSafetyEntry
  lowerDloadReturnStable lowerDloadReturnAlignment lowerDloadLiveAllocation
  venomExecSemantics venomState venomInst finite_map list pred_set
  ptrDiscipline contextCodegenRel o1ContractLowerDload venomExecProofs
  o1PassContract unitShapeDefs lowerDloadOracleCallAssembly o1LowerDloadShared
  lowerDloadSafetyRelation lowerDloadSafetyAmbient

Theorem ld_focus_invoke_correlated_setup:
  o1_ctx_shape C /\
  (!g. MEM g C.ctx_functions ==>
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  taint_ok fn tn inst s /\
  s.vs_gas_readings = t.vs_gas_readings /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct ==>
  ?callee argsS cs.
    lookup_function nm C.ctx_functions = SOME callee /\ callee.fn_name = nm /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    calleeT = FST (lower_dload_function_supply (Sigma nm) callee) /\
    cs.vs_current_bb = ct.vs_current_bb /\ cs.vs_prev_bb = ct.vs_prev_bb /\
    ld_memory lo A (tn with t_var := FEMPTY) cs ct /\
    ld_nonghost (tn with t_var := FEMPTY) cs ct /\
    ld_vars P A <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
      lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
      lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
    (!a. MEM (SOME a) (MAP (op_prov f.lf_H) ops) ==> a IN FDOM A) /\
    (!j a. j < LENGTH ops /\ EL j (MAP (op_prov f.lf_H) ops) = SOME a ==>
      j IN P nm) /\
    cs.vs_gas_readings = ct.vs_gas_readings /\
    cs.vs_gas_readings = s.vs_gas_readings /\
    ct.vs_gas_readings = t.vs_gas_readings
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  `MEM fn C.ctx_functions /\ ld_vars P A f` by gvs[ld_sync_def] >>
  `MEM inst (fn_insts fn)` by
    metis_tac[ld_sync_source, ld_active_inst_member] >>
  `fn_invoke_ok (ctx_fn_names C) fn` by
    (gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `MEM nm (ctx_fn_names C)` by
    (qpat_x_assum `fn_invoke_ok _ _` mp_tac >> simp[fn_invoke_ok_def] >>
     disch_then (qspec_then `inst` mp_tac) >>
     gvs[decode_invoke_def, AllCaseEqs()]) >>
  `?callee. lookup_function nm C.ctx_functions = SOME callee` by
    (Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
     drule lookup_function_not_mem >> gvs[ctx_fn_names_def]) >>
  `MEM callee C.ctx_functions /\ callee.fn_name = nm` by
    (conj_tac >- metis_tac[lookup_function_MEM] >>
     qpat_x_assum `lookup_function nm C.ctx_functions = SOME callee` mp_tac >>
     simp[lookup_function_def] >> disch_then (mp_tac o MATCH_MP FIND_P) >> simp[]) >>
  `calleeT = FST (lower_dload_function_supply (Sigma nm) callee)` by
    metis_tac[optionTheory.SOME_11] >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> strip_tac >> metis_tac[o1_fn_shape_components]) >>
  `opaque_use_ok fn` by fs[fn_shape_ok_def] >>
  `f.lf_src.vs_labels = f.lf_tgt.vs_labels` by metis_tac[ld_sync_labels] >>
  `opaque_use_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
   taint_ok f.lf_fn tn inst f.lf_src /\
   eval_operands ops f.lf_tgt = SOME argsT` by metis_tac[] >>
  drule_all ld_invoke_arguments_related >> strip_tac >>
  `fn_labels callee = fn_labels calleeT` by
    (gvs[] >> metis_tac[lower_dload_function_supply_labels, pairTheory.PAIR]) >>
  drule_all ld_setup_source_exists >>
  disch_then (qspec_then `s` (qspec_then `argsS` strip_assume_tac)) >>
  drule ld_sync_memory >> strip_tac >>
  drule_all ld_setup_pair_effect >>
  disch_then (strip_assume_tac o SRULE []) >>
  `cs.vs_gas_readings = s.vs_gas_readings /\
   ct.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[ld_setup_callee_gas_readings] >>
  qexistsl_tac [`callee`,`argsS`,`cs`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule ld_setup_pair_vars >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ld_arguments_live >>
      qexistsl_tac [`f.lf_H`,`ops`] >> simp[] >>
      metis_tac[ld_global_selected, MEM, finite_mapTheory.FRANGE_FLOOKUP]) >>
  rpt strip_tac >> irule ld_arguments_permission >>
  qexistsl_tac [`A`,`a`,`ops`,`f`,`inst`] >> simp[] >>
  drule ld_sync_ptr_ok >> simp[] >> strip_tac >> gvs[fn_ptr_ok_def]
QED

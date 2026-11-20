Theory gasFocusInitialNativeRoot
Ancestors
  dftGasFromListLookup dftGasFromListTraceDefs frameJointTrace frameJointTransition
  venomExecSemantics venomInst venomState list arithmetic

Theorem focus_initial_native_root:
  wf_function fn /\ ctx.ctx_entry = SOME nm /\
  lookup_function nm ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  entry = (root_base with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  enters_block fn entry u /\ active_inst fn inst u /\ 0 < N ==>
  !q. q = JointConfig [] [] FEMPTY entry_taint fn inst u [] FEMPTY []
            [OriginInitial entry; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst u)] ==>
  !T. T = dftGasFromListTraceDefs$trace_blocks [] 0 N ctx fn entry ==>
    joint_initial root_base ctx q /\ joint_trace root_base ctx q [] [] q /\
    dftGasFromListTraceDefs$trace_context N ctx root_base = T /\
    (?tail. T = (([],1,inst.inst_id),fn,inst,u)::tail) /\
    0 < LENGTH T /\ EL 0 T = (([],1,inst.inst_id),fn,inst,u) /\
    TAKE 0 T = [] /\ LENGTH (TAKE 0 T) = 0 /\
    dftGasFromListTraceDefs$trace_gas (TAKE 0 T) = []
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  rpt strip_tac >> pure_rewrite_tac [LET_THM] >>
  `joint_initial root_base ctx
     (JointConfig [] [] FEMPTY entry_taint fn inst u [] FEMPTY []
       [OriginInitial entry; OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst u)])` by
    (gvs[] >> irule joint_initial_rules >> metis_tac[]) >>
  `?tail. trace_blocks [] 0 N ctx fn entry =
      (([],1,inst.inst_id),fn,inst,u)::tail` by
    (drule_all entered_active_lookup >> strip_tac >>
     Cases_on `N` >> gvs[] >>
     simp[Once trace_defs] >> simp[Once trace_defs]) >>
  gvs[joint_trace_def, joint_chain_def, trace_context_def,
      trace_function_def, trace_gas_def]
QED

(* Assemble a single entry-to-revert certificate before projecting execution. *)
Theory calldataNoneEntryAssembly
Ancestors
  calldataNoneFallbackJoint calldataNoneSelectedChecks entryJointRevertExit
  fragGasOriginPtrLoop e2eDefs vyperLoweringCorrect vyperCalldata vyperValue
  vyperCompiler moduleLowering moduleLoweringProps compileEnv fragExec
  fragGasOriginPtr fragGasPathMem fragGasPathPtr ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState words list finite_map

Theorem none_entry_reject_from_selected:
  !tops rpolicy unit am tx vs func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    (!name tys.
      4 <= LENGTH vs.vs_call_ctx.cc_calldata /\
      FIND (\(n,ts). abi_method_id (type_env tops) n ts =
        cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) =
        SOME (name,tys) ==>
      ?tvs m pay opened checked p G tn.
        OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs /\
        m = 4 + SUM (MAP tv_abi_size tvs) /\
        fn_entry_label func = SOME "__entry" /\
        entry_prov func
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0|>) FEMPTY = FEMPTY /\
        entry_taint_vars func
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0|>) entry_taint = entry_taint /\
        (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (OK p,G,tn)) /\
        p.vs_call_ctx = vs.vs_call_ctx /\
        compile_entry_checks m pay opened = ((),checked) /\
        fn_has_code opened checked func /\ fresh_vars_wrt opened p /\
        ~p.vs_halted /\ p.vs_current_bb = opened.cs_current_bb /\
        p.vs_inst_idx = LENGTH opened.cs_current_insts /\
        allocas_from 0 p /\ (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp p) /\
        m < dimword (:256) /\ LENGTH p.vs_call_ctx.cc_calldata < dimword (:256) /\
        (!t H u.
          (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
            (p,G,tn) [] (OK t,H,u)) /\
          m <= LENGTH p.vs_call_ctx.cc_calldata /\
          vars_pc_only p t /\ fresh_vars_wrt checked t /\ ~t.vs_halted /\
          t.vs_current_bb = checked.cs_current_bb /\
          t.vs_inst_idx = LENGTH checked.cs_current_insts /\
          t.vs_call_ctx = p.vs_call_ctx /\ t.vs_allocas = p.vs_allocas /\
          allocas_from 0 t /\
          u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
          u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
          calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE ==>
          ?z H' u'. z.vs_returndata = [] /\
            !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
              (t,H,u) [] (Abort Revert_abort z,H',u'))) ==>
    fn_entry_label func = SOME "__entry" /\
    ?s G' tn'. s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `e = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` >>
  `?s G' tn'. fn_entry_label func = SOME "__entry" /\
    entry_prov func e FEMPTY = FEMPTY /\
    entry_taint_vars func e entry_taint = entry_taint /\
    s.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
      (e,FEMPTY,entry_taint) [] (Abort Revert_abort s,G',tn')` by
    (drule calldata_dispatch_none_cases >>
     disch_then (DISJ_CASES_THEN2 (CONJUNCTS_THEN ASSUME_TAC)
       (qx_choosel_then [`name`,`tys`]
         (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN ASSUME_TAC))))
     >- (drule_all none_fallback_entry_joint >>
         disch_then (qx_choosel_then [`fn`,`z`,`H`,`u`] strip_assume_tac) >>
         `fn = func` by fs[] >>
         qexistsl_tac [`z`,`H`,`u`] >> fs[Abbr `e`]) >>
     qpat_x_assum `!name tys. _ ==> _` (qspecl_then [`name`,`tys`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choosel_then [`tvs`,`m`,`pay`,`opened`,`checked`,`p`,`G`,`tn`]
       strip_assume_tac) >>
     `4 <= LENGTH p.vs_call_ctx.cc_calldata` by simp[] >>
     drule_all (Q.INST [`PG` |-> `[]`] selected_checks_reject_or_continue) >>
     disch_then (qspecl_then [`tn`,`G`] (DISJ_CASES_THEN2
       (qx_choosel_then [`z`,`H`,`u`] strip_assume_tac)
       (qx_choosel_then [`t`,`H`,`u`] strip_assume_tac)))
     >- (qexistsl_tac [`z`,`H`,`u`] >> simp[] >> rpt gen_tac >>
         irule gas_origin_ptr_path_trans >> qexistsl_tac [`G`,`p`,`tn`] >> simp[]) >>
     `calldata_decode_args vs.vs_call_ctx.cc_calldata tvs 0 = NONE` by
       (`~(LENGTH vs.vs_call_ctx.cc_calldata < 4 + SUM (MAP tv_abi_size tvs))` by
          (qpat_assum `m <= LENGTH p.vs_call_ctx.cc_calldata` mp_tac >>
           qpat_assum `p.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
           qpat_assum `m = 4 + SUM (MAP tv_abi_size tvs)` SUBST1_TAC >>
           rewrite_tac[arithmeticTheory.NOT_LESS]) >>
        qpat_x_assum `_ = NONE \/ ?tvs. _` mp_tac >> simp[]) >>
     qpat_x_assum `!t H u. _ ==> _` (qspecl_then [`t`,`H`,`u`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choosel_then [`z`,`H'`,`u'`] strip_assume_tac) >>
     qexistsl_tac [`z`,`H'`,`u'`] >> simp[] >> rpt gen_tac >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`G`,`p`,`tn`] >> simp[] >>
     irule gas_origin_ptr_path_trans >> qexistsl_tac [`H`,`t`,`u`] >> simp[]) >>
  simp[] >> qexistsl_tac [`s`,`G'`,`tn'`] >> simp[Abbr `e`] >>
  irule entry_joint_revert_exit >> simp[]
QED

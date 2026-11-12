(* Coverage at a call boundary, given a restored related source point. *)
Theory fmpStageCoverFrameCall
Ancestors
  fmpStageCoverInv fmpStageCoverCall fmpStageFmpSteps fmpStageRel
  ptrDiscipline contextCodegenRel ctxLookupAgreeHelpers
  o1ContractSimplifyCfgSrcFrame o1PassLift o1PassContract
  passSimulationDefs venomExecSemantics venomState venomInst
  venomWf unitTransformDefs finite_map words list

Theorem fmp_cov_call_point:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ~s.vs_halted /\ ivk.inst_opcode = INVOKE /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' /\ active_inst fn' ti t /\
  ti.inst_opcode = INVOKE /\ decode_invoke ti = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  eval_operands ops t = SOME args /\ setup_callee callee' args t = SOME cs /\
  enters_block callee' cs t1 /\ active_inst callee' ti1 t1 ==>
  ?stk1 PG1 G1 tn1 fn1 inst1 s1.
    frame_reachable vs C stk1 PG1 G1 tn1 fn1 inst1 s1 /\
    active_inst fn1 inst1 s1 /\ ~s1.vs_halted /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      stk1 PG1 G1 tn1 fn1 s1 lo t1 ((t,lo)::ts) /\
    lookup_function fn1.fn_name C'.ctx_functions = SOME callee' /\
    fmp_cov_stack C' stk1 ((t,lo)::ts)
      (<| cf_fn := fn'; cf_inst := ti; cf_state := t; cf_params := PG';
          cf_prov := G'; cf_tvar := tn'.t_var |> :: stk')
Proof
  rpt strip_tac >>
  drule_all fmp_stage_back_call >> strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`fmp0` |-> `w2n vs'.vs_initial_fmp`, `raw0` |-> `w2n fmp`,
     `ivk'` |-> `ti`] fmp_stage_invoke_call)) >> strip_tac >>
  gvs[] >>
  `t1' = t1` by
    (gvs[enters_block_def] >> metis_tac[]) >>
  gvs[] >>
  `frame_reachable vs C
     (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
         cf_prov := G; cf_tvar := tn.t_var |> :: stk)
     (MAP (op_prov G) ops') FEMPTY (tn with t_var := FEMPTY) callee inst s1` by
    (irule frame_reachable_call >> metis_tac[]) >>
  `~s1.vs_halted` by
    (`vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
      !nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
       (fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def,
           o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
        metis_tac[lookup_function_MEM]) >>
     drule_all scfg_frame_reachable_entry_root >> strip_tac >>
     drule supply_frame_reach_not_halted >>
     fs[fn_entry_state_def]) >>
  `callee.fn_name = nm` by
    (metis_tac[lookup_function_selected_name]) >>
  qexistsl
    [`<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
         cf_prov := G; cf_tvar := tn.t_var |> :: stk`,
     `MAP (op_prov G) ops'`, `FEMPTY`, `tn with t_var := FEMPTY`,
     `callee`, `inst`, `s1`] >>
  simp[fmp_cov_stack_def]
QED

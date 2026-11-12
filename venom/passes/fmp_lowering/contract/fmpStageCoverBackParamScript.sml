(* Source PARAM progress, conditional on the source call-arity boundary. *)
Theory fmpStageCoverBackParam
Ancestors
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProofs venomInstProofs callLayoutDefs
  venomWf unitShapeDefs list rich_list words finite_map
  passSimulationDefs stackPlanTypes fmpAnalysisProps simplifyCfgMergeRuns

Theorem frame_param_bounds[local]:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  o1_ctx_shape C /\
  (!stk0 PG0 G0 tn0 caller inv st name ops callee.
    frame_reachable vs C stk0 PG0 G0 tn0 caller inv st /\
    active_inst caller inv st /\ inv.inst_opcode = INVOKE /\
    inv.inst_operands = Label name::ops /\
    lookup_function name C.ctx_functions = SOME callee ==>
    LENGTH (fn_user_param_insts callee) <= LENGTH ops) ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH s.vs_params /\
  EVERY (\f. LENGTH (fn_user_param_insts f.cf_fn) <=
             LENGTH f.cf_state.vs_params) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- (rpt strip_tac >> simp[] >>
      `o1_fn_shape C fn /\ fn.fn_name = name` by
        (fs[o1_ctx_shape_def, EVERY_MEM] >>
         metis_tac[venomInstTheory.lookup_function_MEM, fmpAnalysisPropsTheory.lookup_function_name]) >>
      `entry_fn_no_params fn` by fs[o1_fn_shape_def] >>
      `fn_user_param_insts fn = []` suffices_by simp[] >>
      fs[fn_user_param_insts_def, FILTER_EQ_NIL, EVERY_MEM,
         entry_fn_no_params_def, fn_entry_insts_def, venomInstTheory.fn_insts_def,
         fn_insts_blocks_MEM, venomInstTheory.is_param_opcode_def,
         venomInstTheory.entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[] >>
      metis_tac[venomInstTheory.is_param_opcode_def])
  >- (rpt strip_tac >> drule_all step_preserves_params >> strip_tac >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      drule_all scfg_terminator_jump >> strip_tac >>
      fs[enters_block_def] >>
      drule eval_phis_only_updates_vs_vars >> strip_tac >>
      gvs[venomInstTheory.jump_to_def] >> metis_tac[])
  >- (rpt strip_tac >> FAIL_TAC "call")
  >> rpt strip_tac >> cheat
QED

Theory fmpStageFmpStepsCallAssemble
Ancestors
  fmpStageRunnerFacts fmpStageFmpStepsCallArgs fmpStageFmpStepsCallEntry fmpStageFmpStepsCallPush
  fmpStageCallArity fmpStageOpBase fmpAnalysisProps
  fmpStageRel o1PassContract venomExecSemantics venomInst venomState list finite_map
  venomOperandProps arithmetic

Theorem fmp_call_setup_push[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function callee.fn_name C'.ctx_functions = SOME callee' /\
  fmp_frame_rel sm fmp0 raw0 (w2n s.vs_fmp) lo lo F
    callee callee' PGc FEMPTY FEMPTY s1 t1 /\
  first_block_no_phi callee /\ first_block_no_phi callee' /\
  setup_callee callee args s = SOME cs /\
  setup_callee callee' argst t = SOME ct /\
  enters_block callee cs s1 /\ enters_block callee' ct t1 /\
  ~s.vs_halted ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F
    (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
        cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    PGc FEMPTY (tn with t_var := FEMPTY) callee s1 lo t1 ((t,lo)::ts)
Proof
  strip_tac >> irule fmp_stage_call_push >>
  `s1 = cs /\ t1 = ct` by metis_tac[fmp_call_setup_entry] >>
  `s.vs_halted = t.vs_halted` by fs[fmp_stage_rel_def] >>
  gvs[setup_callee_def]
QED

Theorem fmp_stage_invoke_call_from_match:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ~s.vs_halted /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\ C.ctx_entry <> SOME nm /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t /\
  (?callee' infos_c ctx_c runner_c extra.
    lookup_function nm C'.ctx_functions = SOME callee' /\
    fmp_stage_lowered infos_c ctx_c runner_c callee callee' /\
    ~fn_is_context_entry ctx_c callee /\
    decode_invoke ivk' = SOME (nm,ops ++ extra) /\
    ((extra = [] /\ fmp_stage_root infos_c ctx_c callee = NONE) \/
     (?r. extra = [Var r] /\ lookup_var r t = SOME (n2w lo)))) ==>
  ?ops' callee' args' cs' t1.
    decode_invoke ivk' = SOME (nm,ops') /\
    lookup_function nm C'.ctx_functions = SOME callee' /\
    eval_operands ops' t = SOME args' /\
    setup_callee callee' args' t = SOME cs' /\
    enters_block callee' cs' t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F
      (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
          cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
      lo t1 ((t,lo)::ts)
Proof
  strip_tac >>
  drule_all fmp_stage_invoke_arguments >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function callee /\ first_block_no_phi callee` by
    (imp_res_tac lookup_function_MEM >>
     fs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[]) >>
  drule_all fmp_stage_lowered_shape >> strip_tac >>
  qpat_x_assum `first_block_no_phi _ ==> _` drule >> strip_tac >>
  `LENGTH args = LENGTH (fn_user_param_insts callee)` by
    metis_tac[fmp_stage_invoke_arity] >>
  `callee.fn_name = nm` by metis_tac[lookup_function_name] >>
  `?zs. eval_operands extra t = SOME zs /\
    (!rl rp. fmp_stage_root infos_c ctx_c callee = SOME (rl,rp) ==>
       zs = [n2w lo])` by
    (gvs[] >> simp[eval_operands_def, eval_operand_def]) >>
  `eval_operands (ops ++ extra) t = SOME (ys ++ zs)` by
    simp[eval_operands_append] >>
  `?ct. setup_callee callee' (ys ++ zs) t = SOME ct` by
    (Cases_on `callee'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, setup_callee_def]) >>
  `enters_block callee' ct ct` by metis_tac[fmp_call_setup_entry] >>
  `cs.vs_params = args /\ ct.vs_params = ys ++ zs` by
    metis_tac[setup_callee_frame] >>
  `fmp_params_rel sm (MAP (op_prov G) ops) cs ct` by
    (irule fmp_params_rel_append >> simp[] >> metis_tac[]) >>
  `!rl rp. fmp_stage_root infos_c ctx_c callee = SOME (rl,rp) ==>
     LENGTH args < LENGTH (ys ++ zs) /\ EL (LENGTH args) (ys ++ zs) = n2w lo` by
    (rpt strip_tac >> `zs = [n2w lo]` by metis_tac[] >>
     simp[EL_APPEND_EQN]) >>
  `fmp_frame_rel sm fmp0 raw0 (w2n s.vs_fmp) lo lo F
    callee callee' (MAP (op_prov G) ops) FEMPTY FEMPTY s1 ct` by
    (irule fmp_call_frame_entry >>
     gvs[fmp_stage_rel_def] >>
     qpat_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >>
     goal_assum $ drule_at Any >> goal_assum $ drule_at Any >>
     goal_assum $ drule_at Any >> simp[LENGTH_APPEND] >>
     qpat_assum `fmp_stage_lowered _ _ _ callee callee'` (irule_at Any) >>
     goal_assum $ drule_at Any >> simp[]) >>
  qexistsl [`ops ++ extra`, `callee'`, `ys ++ zs`, `ct`, `ct`] >>
  simp[] >> irule fmp_call_setup_push >> metis_tac[]
QED

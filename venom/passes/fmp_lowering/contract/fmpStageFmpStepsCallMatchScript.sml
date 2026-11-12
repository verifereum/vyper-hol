Theory fmpStageFmpStepsCallMatch
Ancestors
  fmpStageFmpStepsCallMatchCore fmpStageFmpStepsCallRootPosition
  fmpStageRel contextCodegenRel

Theorem fmp_call_match:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) /\
  C.ctx_entry <> SOME nm /\
  lookup_function nm C.ctx_functions = SOME callee /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t ==>
  ?callee' infos_c ctx_c runner_c extra.
    lookup_function nm C'.ctx_functions = SOME callee' /\
    fmp_stage_lowered infos_c ctx_c runner_c callee callee' /\
    ~fn_is_context_entry ctx_c callee /\ ivk'.inst_opcode = INVOKE /\
    decode_invoke ivk' = SOME (nm,ops ++ extra) /\
    wf_function callee /\ first_block_no_phi callee /\
    ((extra = [] /\ fmp_stage_root infos_c ctx_c callee = NONE) \/
     (?runner. extra = [Var runner] /\ lookup_var runner t = SOME (n2w lo) /\
       IS_SOME (fmp_stage_root infos_c ctx_c callee)))
Proof
  strip_tac >> mp_tac fmp_call_match_conditional >>
  impl_tac >- (simp[] >> metis_tac[fmp_call_invoke_past_root]) >>
  simp[]
QED

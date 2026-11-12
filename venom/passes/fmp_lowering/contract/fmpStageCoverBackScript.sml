(*
 * Backward progress for FmpLowering's coverage (fmpStageCoverage).  The
 * coverage runs over the target's reachable states, but the stage's step
 * lemmas go forward from a source step that terminates.  These lemmas
 * give that source step from the target's: at a related point the source
 * step does not fail, and the call, block entry and return the target
 * takes have source counterparts.
 *
 * TOP-LEVEL:
 *   fmp_stage_src_defined      - source operands are defined at a point
 *   fmp_stage_back_kept        - a kept instruction's source step terminates
 *   fmp_stage_back_fmp_ops     - DALLOCA and RETPC_PARAM never fail
 *   fmp_stage_back_entry       - the context entry's block can be entered
 *   fmp_stage_back_block_entry - a jump's target block can be entered
 *   fmp_stage_back_call        - an INVOKE can enter its callee
 *   fmp_stage_back_ret         - a RET returns into its caller
 *)
Theory fmpStageCoverBack
Ancestors
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  unitTransformDefs passSimulationDefs venomExecSemantics venomState venomInst
  simplifyCfgAvailability o1ContractSimplifyCfgSrcFrame
  finite_map words list

Theorem fmp_stage_src_defined:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  IS_SOME (lookup_var v s)
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
   !nm f. lookup_function nm C.ctx_functions = SOME f ==> wf_function f` by
    (fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def,
        o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  irule scfg_frame_operand_defined >>
  fs[o1_fn_shape_def, make_ssa_input_ok_def] >> metis_tac[]
QED

Theorem fmp_stage_back_kept:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  terminates (step_inst k' C' inst t) ==>
  terminates (step_inst k C inst s)
Proof
  cheat
QED

Theorem fmp_stage_back_fmp_ops:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [DALLOCA; RETPC_PARAM] ==>
  terminates (step_inst k C inst s)
Proof
  cheat
QED

Theorem fmp_stage_back_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  ?s1 inst.
    enters_block fn
      (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := 0 |>) s1 /\
    active_inst fn inst s1
Proof
  cheat
QED

Theorem fmp_stage_back_block_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn bi sb /\ active_inst fn bi sb /\
  MEM bi.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst k C bi sb = OK (jump_to lbl sb) /\
  MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  ?s1 inst. enters_block fn (jump_to lbl sb) s1 /\ active_inst fn inst s1
Proof
  cheat
QED

Theorem fmp_stage_back_call:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE ==>
  ?nm ops callee args cs s1 inst.
    decode_invoke ivk = SOME (nm,ops) /\ C.ctx_entry <> SOME nm /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1
Proof
  cheat
QED

Theorem fmp_stage_back_ret:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\
  active_inst fn rinst s /\ ~s.vs_halted /\ rinst.inst_opcode = RET /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T (f::stk) PG G tn fn s lo t
    ((tc,lc)::ts) /\
  lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc' /\
  active_inst fc' ivk' tc /\
  step_inst k' C' rinst t = IntRet ret' t_end /\
  bind_outputs ivk'.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state tc t_end)) = SOME t' ==>
  ?ret s_end s' inst'.
    step_inst k C rinst s = IntRet ret s_end /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
      SOME s' /\
    active_inst f.cf_fn inst'
      (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  cheat
QED

(*
 * Backward progress for FmpLowering's coverage across function
 * boundaries: the context entry's first block can be entered, a reachable
 * INVOKE enters its (non-entry) callee, and a RET the target takes returns
 * into the source caller (see fmpStageCoverBack for the setting).
 *
 * TOP-LEVEL:
 *   fmp_stage_back_entry - the context entry's block can be entered
 *   fmp_stage_back_call  - an INVOKE can enter its callee
 *   fmp_stage_back_ret   - a RET returns into its caller
 *)
Theory fmpStageCoverCall
Ancestors
  fmpStageCoverBack
  fmpStageOpBase fmpStageRel o1PassContract ptrDiscipline contextCodegenRel
  unitTransformDefs passSimulationDefs venomExecSemantics venomState venomInst
  simplifyCfgAvailability o1ContractSimplifyCfgSrcFrame
  finite_map words list

(* Why it holds: the entry fn is wf_function with first_block_no_phi,
   and the initial state is o1_initial_state_ok. *)
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

(* Why it holds: callee_first (o1PassContract) orders callees strictly
   before callers (list_precedes), so every active or saved frame's
   function is the entry or precedes it, and an INVOKE of the entry would
   make it precede itself.  INVOKE args hold no Labels, so eval_operands
   reduces to fmp_stage_src_defined; setup_callee needs nonempty blocks
   (wf_function); the callee's first block has no PHIs. *)
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

(* Why it holds: the source RET has nonempty, defined operands, so it
   returns IntRet; the target steps the same rinst, so the value lists
   have equal length.  The target INVOKE's outputs add [runner] only when
   the callee publishes its fmp, which no row-3 callee does (pre_fmp_ops
   excludes RETFMP and DRET), so the binds succeed together. *)
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

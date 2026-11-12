(* Internal return assembly: current callee effects, restored caller locals. *)
Theory o1LowerDloadJointReturnBoundary
Ancestors
  o1LowerDloadJointReturn o1LowerDloadJointRestore o1LowerDloadJointPop
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadShared
  o1LowerDloadMapEvolution o1LowerDloadEnvironment o1LowerDloadOpaque
  ptrDiscipline venomExecSemantics venomState contextCodegenRel
  finite_map list pred_set

Theorem ld_joint_boundary_return:
  ld_joint_boundary vs C C' lo D (f::stk) PG G tn fn rinst s t
    n a (ofr::U) B HP H sites X (caller'::ts) /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn rinst s /\ rinst.inst_opcode = RET /\
  step_inst fuel C rinst s = IntRet ir s_end /\
  bind_outputs f.cf_inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state f.cf_state s_end)) = SOME s1 /\
  active_inst f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
  active_inst f.cf_fn f.cf_inst f.cf_state /\ f.cf_inst.inst_opcode = INVOKE /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.cf_fn.fn_blocks) /\
  s.vs_call_ctx.cc_address = f.cf_state.vs_call_ctx.cc_address ==>
  ?jr t1 fn'. step_inst fuel C' rinst t = IntRet jr t /\
    jr.iret_values = ir.iret_values /\ jr.iret_adopt_fmp = NONE /\
    ir.iret_adopt_fmp = NONE /\
    lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fn' /\
    active_inst fn' f.cf_inst caller' /\
    bind_outputs f.cf_inst.inst_outputs jr.iret_values
      (adopt_return_fmp jr (merge_callee_state caller' t)) = SOME t1 /\
    ld_joint_boundary vs C C' lo D stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s1 with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t1 with vs_inst_idx := SUC caller'.vs_inst_idx)
      n ofr.of_owner U (DRESTRICT B {id | FST id <> a}) ofr.of_params
      (DRESTRICT ofr.of_prov (COMPL (set f.cf_inst.inst_outputs)))
      (DRESTRICT sites {id | FST id <> a})
      (DRESTRICT X {id | FST id <> a}) ts
Proof
  (* P4a in progress *) cheat
QED

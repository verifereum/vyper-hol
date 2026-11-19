(* Fixed-filling static rows for the first MakeSSA stage.  These use no
   whole-run source invariant: headroom is transported as a frame predicate. *)
Theory gasFocusMakeSsaStatic
Ancestors
  o1ContractMakeSsa o1ContractMakeSsaSrc o1PassContract ptrDiscipline
  unitMemInv lowerDloadDefs venomPassSchedule list o1PassLift
  contextRawReachable venomInst venomWf venomFnScheduleRunner
  makeSsaDefs makeSsaCurrentProps makeSsaCurrentSim
  o1ContractMakeSsaReplay o1ContractMakeSsaSrcOpcodes makeSsaCurrentLockstep
  o1FrameLockstep stateFrame venomState option

Theorem make_ssa_focus_static_rows:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv dload_headroom_ok C vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fmp_free_ctx C /\ callee_first names C.ctx_functions ==>
  mem_inv dload_headroom_ok C' vs /\
  EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\
  fmp_free_ctx C' /\ callee_first names C'.ctx_functions
Proof
  strip_tac >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions` by
    (rw[EVERY_MEM] >> drule_all o1ContractMakeSsaSrcTheory.make_ssa_src_stage_fn >> strip_tac >>
     drule make_ssa_current_fn_metadata >>
     fs[EVERY_MEM, fn_static_layout_eq_def]) >>
  metis_tac[o1ContractMakeSsaSrcTheory.make_ssa_src_stage_headroom, o1ContractMakeSsaSrcTheory.make_ssa_src_stage_fmp_free,
            o1ContractMakeSsaSrcTheory.make_ssa_src_stage_callee_first]
QED

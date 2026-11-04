Theory concretizeAnalysisIncomingDemand
Ancestors
  frameIncomingArgument concretizeAnalysisScanCoverage concretizeAnalysisWriteSafety
  concretizeAnalysisLivenessPaths concretizeAnalysisLivenessTransfer
  frameOriginHistory frameOriginReachable frameAllocationOwnership
  o1PassContract ptrDiscipline concretizeMemLocDefs basePtrDefs cfgAnalysis
  venomExecSemantics contextCodegenRel venomInst venomWf finite_map list pred_set

(* The ML interface is instruction-local; semantic ancestry is not unfolded here. *)
Theorem active_invoke_argument_generators:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  MEM (Var u) ops /\ Allocation aid IN bp_bases bpr u /\
  (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel fn) bpr mems sizes pallocas
    (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) ==>
  MEM (Allocation aid) (ml_lookup la (s.vs_current_bb,s.vs_inst_idx)) /\
  MEM (Allocation aid) (ml_lookup us (s.vs_current_bb,s.vs_inst_idx))
Proof
  strip_tac >>
  `inst.inst_operands = Label nm :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `ml_operand_gen (Allocation aid) bpr inst` by
    (simp[ml_operand_gen_def] >> qexists_tac `Var u` >>
     gvs[bp_bases_find_base_allocas]) >>
  gvs[active_inst_def] >> metis_tac[ml_production_invoke_generators]
QED

Theorem joint_incoming_production_argument:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  o1_ctx_shape ctx /\ ptr_discipline lo ctx vs0 /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY all_reachable ctx.ctx_functions /\
  ~ctx_has_dalloca ctx /\ FLOOKUP om v = SOME (OriginParameter p,site) ==>
  ?k aid u nm ops.
    k < LENGTH stk /\ k < LENGTH oms /\
    (EL k stk).cf_inst.inst_opcode = INVOKE /\
    decode_invoke (EL k stk).cf_inst = SOME (nm,ops) /\
    active_inst (EL k stk).cf_fn (EL k stk).cf_inst (EL k stk).cf_state /\
    MEM (Var u) ops /\ FLOOKUP (EL k oms) u = SOME (OriginLocal aid,site) /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site /\
    Allocation aid IN bp_bases
      (bp_analyze_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
        (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn) u /\
    (!mems sizes pallocas la us.
      (!name. OL alloc_to (mems name)) /\ OL alloc_to pallocas /\
      ml_iterate_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
        (bp_analyze_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
          (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn)
        mems sizes pallocas (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn
        FEMPTY FEMPTY = (la,us) ==>
      MEM (Allocation aid) (ml_lookup la
        ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx)) /\
      MEM (Allocation aid) (ml_lookup us
        ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx)))
Proof
  strip_tac >> drule_all joint_incoming_argument >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >>
  `MEM (EL k stk).cf_fn ctx.ctx_functions` by
    (drule origin_frame_erasure >> strip_tac >>
     drule_all frame_allocation_ownership >> simp[EVERY_EL] >> metis_tac[]) >>
  `EVERY wf_function ctx.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `wf_function (EL k stk).cf_fn /\ all_reachable (EL k stk).cf_fn /\
   ssa_form (EL k stk).cf_fn` by metis_tac[EVERY_MEM] >>
  `Allocation aid IN bp_bases
      (bp_analyze_fuel (concretize_memloc_fuel (EL k stk).cf_fn)
        (cfg_analyze (EL k stk).cf_fn) (EL k stk).cf_fn) u` by
    (fs[ptr_discipline_def] >> metis_tac[origin_frame_saved_production_coverage]) >>
  qexistsl_tac [`k`,`aid`,`u`,`nm`,`ops`] >> simp[] >>
  metis_tac[active_invoke_argument_generators]
QED

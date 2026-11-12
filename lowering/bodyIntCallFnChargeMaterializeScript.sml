(* Whole-instruction-stream charge of parameter materialization. *)
Theory bodyIntCallFnChargeMaterialize
Ancestors
  bodyIntCallResource intCallCallee loweringShapeDefs exprLoweringProps
  moduleLowering compileEnv venomInst list rich_list finite_map words

Theorem materialize_internal_params_state_charge:
  !caps ce st ce' st'.
    materialize_internal_params ce caps st = (ce',st') /\
    ALL_DISTINCT (MAP FST caps) /\
    (!nm off sz. MEM nm (MAP FST caps) /\
       FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==>
       sz < dimword (:256)) ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts st'))) =
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts st))) +
    internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all materialize_internal_params_charge >> strip_tac >>
  drule intCallCalleeTheory.materialize_internal_params_shape >> strip_tac >>
  simp[state_insts_def, all_blocks_def, FILTER_APPEND_DISTRIB,
       MAP_APPEND, SUM_APPEND] >>
  gvs[FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND] >> decide_tac
QED

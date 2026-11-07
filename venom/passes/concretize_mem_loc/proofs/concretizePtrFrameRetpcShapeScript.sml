(*
 * The frame-relation return-PC shape (every RET and PHI of every input
 * function) under the stage contract's hypotheses. The paired-prefix
 * producers take it as a premise; ptr_stage_paired_bridge supplies only
 * the reachable-code form unitShapeDefs$retpc_shape_ok.
 *)
Theory concretizePtrFrameRetpcShape
Ancestors
  o1PassContract ptrDiscipline unitMemInv stackPlanGen concretizeMemLocDefs
  venomPassDispatcher cfgWf unitShapeDefs frameRel venomWf venomInst list

(* The full-function writer condition controls PHIs even when the
   reachable-code view removes some of their incoming operands. *)
Theorem full_retpc_shape_to_frame[local]:
  fn_inst_wf fn /\ all_reachable fn /\
  unitShapeDefs$retpc_shape_ok fn ==>
  frameRel$retpc_shape_ok fn
Proof
  strip_tac >>
  fs[frameRelTheory.retpc_shape_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      `MEM inst (fn_insts (reachable_fn fn))` by
        (fs[fn_insts_def, MEM_fn_insts_blocks_iff,
            all_reachable_def, MEM_reachable_fn_insts] >>
         `inst.inst_opcode <> PHI` by simp[] >>
         metis_tac[reachable_inst_fields]) >>
      fs[unitShapeDefsTheory.retpc_shape_ok_def] >>
      metis_tac[reachable_retpc_var]) >>
  rpt strip_tac >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  `LENGTH inst.inst_outputs = 1` by gvs[inst_wf_def] >>
  `?z. MEM z inst.inst_outputs` by
    (Cases_on `inst.inst_outputs` >> fs[]) >>
  `retpc_var fn z` by
    (fs[retpc_var_def] >> metis_tac[copy_phi_var_rules]) >>
  fs[unitShapeDefsTheory.retpc_shape_ok_def] >>
  qpat_x_assum `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs /\ _ ==> _`
    (qspecl_then [`inst`, `z`] mp_tac) >> simp[]
QED

Theorem ptr_stage_frame_retpc_shape:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom ==>
  EVERY frameRel$retpc_shape_ok C.ctx_functions
Proof
  strip_tac >>
  fs[o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
  irule full_retpc_shape_to_frame >>
  fs[o1_fn_shape_def, fn_shape_ok_def] >> metis_tac[]
QED

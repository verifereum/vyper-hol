Theory concretizePtrPairedJumpSchema
Ancestors
  concretizePtrPairedRoot concretizePtrPairedPrefixProbe concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrMixedPhi concretizeStepStructure concretizeStepShape
  concretizeStepCallChecks concretizeStepRetpc concretizeStageShape
  venomExecSemantics venomWf unitShapeDefs ptrDiscipline finite_map list
  concretizePtrDemandWriteExclusion stackPlanGen unitMemInv

(* Audit only: parse and typecheck a proposed obligation. This asserts no
   theorem, introduces no constant and registers no oracle. *)
val _ = type_of ``
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = JMP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts a.po_fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp a.po_fn) (Allocation inst.inst_id))) /\
  active_inst at.po_fn at.po_inst at.po_state /\
  is_terminator at.po_inst.inst_opcode /\
  step_inst fuel Ct at.po_inst at.po_state = OK t_jump /\
  ~t_jump.vs_halted /\ enters_block at.po_fn t_jump t_entry /\
  active_inst at.po_fn it t_entry /\
  bt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn t_jump at.po_prov)
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry ==>
  ?s_jump b B TG' bb n delta snapshots.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    TG' = entry_prov a.po_fn s_jump TG /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
      ((H ++ [(tokens,registry,B,PT,TG',saved,entries)]) ++ snapshots) calls ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n b).po_inst /\
    (ptr_gap_scan bb n b).po_prov = b.po_prov /\
    (ptr_gap_scan bb n b).po_taint = b.po_taint
``;

(* C1.5.90.67.23 certificate audit, 2026-11-06.
   This is a typechecked question, NOT an asserted or proved theorem.
   In particular there is no independent historical transport premise. *)
val _ = type_of ``
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  w < EL q done /\ q < LENGTH done ==>
  pa+k NOTIN range_bytes
    (step_writes (EL q ht).po_inst (EL q ht).po_state
      (EL (SUC q) ht).po_state)
``;

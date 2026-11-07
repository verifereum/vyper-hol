(* Parse the frozen statement in the family's ancestor environment and compare
   kernel terms, including theory-qualified constant identities and types. *)
Theory concretizePtrBufferCopyFamilyAudit
Ancestors
  concretizePtrBufferCopyFamilyCandidate
  concretizePtrStorageReadProducer concretizePtrBufferCopyContent
  concretizePtrOpaqueRetpc ptrDiscipline memLocDefs list pointerConfinedDefs
  concretizePtrRequestHistory venomExecSemantics venomState venomInst words codegenRel
  concretizePtrWriteFootprint concretizePtrPrefixLedger concretizePtrBytes
  concretizePtrChronologicalHistory pred_set arithmetic
  concretizePtrWriteOwnership concretizePtrOwnershipErasure
  concretizePtrComparisonTransport concretizePtrPairedFields
  concretizePtrSourceOwnership concretizePtrValueTransport
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrDeletedGapHistory concretizePtrExecutedCoverage
  unitShapeDefs venomWf cfgWf o1PassContract
  concretizeStepStructure concretizeStepShape concretizePtrDeletedGaps
  concretizePtrOrdinaryNext concretizePtrTaggedSupport
  concretizePtrLedgerProbe concretizePtrReturnTransport
  concretizePtrOperationalOpcodes finite_map concretizePtrAllocationSize
  contextCodegenRel unitLabelMapIdentity opcodeClass venomExecProps memSafeRun
  concretizePtrActivationChronology concretizePtrPlacementBounds

val frozen_statement = ``
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst``;

val refuted_statement =
  #2 (strip_forall (dest_neg (concl ptr_buffer_copy_exact_frozen_obligation_false)));
val _ = if aconv frozen_statement refuted_statement then
  print "Frozen statement audit: identical kernel terms (constants and types)\n"
  else raise Fail "Frozen statement audit: mismatch";

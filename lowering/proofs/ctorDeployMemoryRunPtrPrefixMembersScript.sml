(* Paired execution of the remaining complex members; support excludes the processed prefix. *)
Theory ctorDeployMemoryRunPtrPrefixMembers
Ancestors
  valueEncodingDefs
  valueEncoding
  ctorDeployMemoryRunPtrPrefixMemberSetup ctorDeployMemoryRunPtrPrefixRecursiveSupport
  ctorAbiActualMemberRun ctorAbiActualMemberInputs ctorAbiActualMemberBoundary
  ctorAbiActualChildFrame ctorAbiActualMemory ctorAbiActualSites
  ctorAbiActualMembers ctorAbiActualEmpty
  abiDecoderMembers abiDecoderMemberInfos abiDecoderMemberCons abiDecoderMemberCode
  abiDecoderMemberSetup abiDecoderMemberBody abiDecoderDynamic abiDecoderOffset
  ctorAbiActualWorld instIdxIndep abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderEmpty abiDecoderEmptyMember
  abiDecoderCoherence abiDecoderContract abiDecoderTypedContract
  abiEncoderRegisteredEffect abiDecoderLoop fragExec compileEnv
  abiEncoder contractABI words list rich_list arithmetic
  allocaFrontierBound allocaBudgetProps abiDecoderReentryPointer
  ctorDeployMemoryRunPtrPrefixCanonical ptrDiscipline ptrSafeRun finite_map pred_set



(* Tail writes cannot change observations on a completed child support. *)
Theorem prefix_member_support_frame:
  abi_encoder_registered_effect (ctor_actual_sites fn child) [(c,k)] s t /\
  child SUBSET ids /\ ctor_actual_scratch fn ids D N t /\
  B SUBSET range_bytes [(p,n)] /\ D <= p /\ p+n <= D+N /\
  regions_disjoint (p,n) (c,k) ==>
  !a. a IN B ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  strip_tac >> rpt strip_tac >>
  `p <= a /\ a < p+n` by fs[SUBSET_DEF, range_bytes_def] >>
  irule ctor_actual_registered_window >>
  qexistsl_tac [`ctor_actual_sites fn child`, `[(c,k)]`] >>
  simp[venomMemDefsTheory.regions_disjoint_def] >>
  reverse conj_tac
  >- (gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  `D <= a /\ a+1 <= D+N` by decide_tac >>
  drule_all ctor_actual_sites_scratch_contained >>
  simp[venomMemDefsTheory.regions_disjoint_def]
QED

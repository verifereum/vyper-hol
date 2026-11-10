(* Resource-only normalization for the actual internal entry initializer. *)
Theory bodyIntCallResourceNormalize
Ancestors
  bodyIntCallActualJointInit bodyIntCallPackageRootResource
  bodyIntCallActualEntryFields intCallCallee compileEnv

Theorem internal_parameter_staged_containment:
  (!b z. staged b z <=> ?i po.
    i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc po z) /\
    b = w2n (EL (offset + i) (argv:bytes32 list))) ==>
  !i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b z. staged b z /\ b <= w2n (EL (offset + i) argv) /\
      w2n (EL (offset + i) argv) + sz <= b + z
Proof
  rpt strip_tac >> qexistsl [`w2n (EL (offset + i) argv)`, `sz`] >>
  simp[] >> qexistsl [`i`, `off`] >> simp[]
QED

Theorem internal_immutable_regions_stack_update:
  internal_immutable_regions ce (cx with stk updated_by f) vs lo =
  internal_immutable_regions ce cx vs lo
Proof
  simp[internal_immutable_regions_def]
QED

Theorem internal_entry_root_buffer_separation:
  compile_internal_function_entry ce params has_rb ctor ilen rt entry =
    ((ce2,rpc,imm),body_start) /\
  fp.jc_root_ce = (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
  fp.jc_rb = (if has_rb then SOME (bw,capacity) else NONE) /\
  (has_rb /\ ce.ce_is_ctor ==> !nm tv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,nm) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP (vs:evaluation_state).immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) nm = SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n bw) capacity) ==>
  !w cap. fp.jc_rb = SOME (w,cap) /\ fp.jc_root_ce.ce_is_ctor ==>
    !nm tv iv io.
    FLOOKUP fp.jc_root_ce.ce_module_vars (fp.jc_root_ce.ce_module,nm) =
      SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP (vs:evaluation_state).immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables fp.jc_root_ce.ce_module imms) nm =
      SOME (tv,iv) ==>
    regions_disjoint io (type_memory_size tv) (w2n w) cap
Proof
  strip_tac >> drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> rpt strip_tac >>
  Cases_on `has_rb` >> gvs[] >> metis_tac[]
QED

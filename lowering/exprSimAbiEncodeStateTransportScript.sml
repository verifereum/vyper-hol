Theory exprSimAbiEncodeStateTransport
Ancestors
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFramedSuffix
  exprSimAbiEncodeChargeTransfer localPtrsProps loweringSlice
  compileEnv exprLoweringProps venomState finite_map pred_set list arithmetic

Theorem abi_encode_caller_local_reads:
  local_ptrs_rel func cenv scopes initial /\
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  alloca_inv actual /\ site IN ids /\
  FLOOKUP actual.vs_allocas site = SOME(p,outsz) /\ 32+w <= outsz /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!name entry ptr sz inst.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) ==>
  !name b n. local_region cenv scopes initial name b n ==>
    mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory
Proof
  strip_tac >> rpt gen_tac >>
  simp_tac bool_ss [local_region_def] >> strip_tac >> gvs[] >>
  irule abi_encode_separated_interval_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  reverse conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >>
  irule abi_encode_local_ptr_separation >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexists `func` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!name entry ptr sz inst. _` drule_all >> simp[]
QED

Theorem abi_encode_caller_immutable_reads:
  immutable_alloca_sep func cenv cx vs initial /\
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  site IN ids /\ FLOOKUP actual.vs_allocas site = SOME(p,outsz) /\
  32+w <= outsz /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!i. i IN ids ==> ?inst. MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = i) ==>
  cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME(ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME(tv,v) ==>
    mem_bytes_at off (type_memory_size tv) actual.vs_memory =
    mem_bytes_at off (type_memory_size tv) initial.vs_memory
Proof
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule abi_encode_separated_interval_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >>
  irule abi_encode_immutable_region_separation >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

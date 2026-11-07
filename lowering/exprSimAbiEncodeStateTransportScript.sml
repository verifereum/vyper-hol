Theory exprSimAbiEncodeStateTransport
Ancestors
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFramedSuffix abiEncoderRegisteredEffect
  exprSimAbiEncodeChargeTransfer exprSimAbiEncodeExecFrame localPtrsProps loweringSlice
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

Theorem abi_encode_caller_locals:
  local_ptrs_rel func cenv scopes initial /\
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  alloca_inv actual /\ site IN ids /\
  FLOOKUP actual.vs_allocas site = SOME(p,outsz) /\ 32+w <= outsz /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  initial.vs_alloca_next <= actual.vs_alloca_next /\
  (!name entry ptr sz.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) ==>
    lookup_var ptr actual = lookup_var ptr initial) /\
  (!name entry ptr sz inst.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) ==>
  local_ptrs_rel func cenv scopes actual
Proof
  strip_tac >>
  `!name b n. local_region cenv scopes initial name b n ==>
    mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory` by
    (rpt gen_tac >> strip_tac >> drule_all abi_encode_caller_local_reads >> simp[]) >>
  irule local_ptrs_rel_mem_agree >> qexists `initial` >> simp[] >>
  metis_tac[]
QED

Theorem abi_encode_caller_immutables:
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs initial /\
  immutable_alloca_sep func cenv cx vs initial /\
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  abi_encode_exec_frame observer initial actual /\
  site IN ids /\ FLOOKUP actual.vs_allocas site = SOME(p,outsz) /\
  32+w <= outsz /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!i. i IN ids ==> ?inst. MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = i) ==>
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs actual
Proof
  strip_tac >> irule immutables_rel_mem_agree >> qexists `initial` >>
  `actual.vs_data_section = initial.vs_data_section /\
    LENGTH initial.vs_memory <= LENGTH actual.vs_memory` by
    gvs[abi_encode_exec_frame_def] >>
  simp[] >> rpt strip_tac >>
  drule_all abi_encode_caller_immutable_reads >> simp[]
QED

Theorem abi_encode_caller_world_fields:
  prepared.vs_accounts = initial.vs_accounts /\
  prepared.vs_transient = initial.vs_transient /\
  prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
  prepared.vs_pending_deletions = initial.vs_pending_deletions /\
  abi_encoder_registered_effect ids outs prepared actual ==>
  actual.vs_accounts = initial.vs_accounts /\
  actual.vs_transient = initial.vs_transient /\
  actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
  actual.vs_pending_deletions = initial.vs_pending_deletions
Proof
  simp[abi_encoder_registered_effect_def]
QED

Theorem abi_encode_caller_state_rel:
  state_rel func cenv cx vs initial /\
  abi_encode_exec_frame observer initial actual /\
  abi_encoder_registered_effect ids outs prepared actual /\
  prepared.vs_accounts = initial.vs_accounts /\
  prepared.vs_transient = initial.vs_transient /\
  prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
  prepared.vs_pending_deletions = initial.vs_pending_deletions /\
  (!name entry ptr sz.
    lookup_scopes name vs.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) ==>
    lookup_var ptr actual = lookup_var ptr initial) /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  initial.vs_alloca_next <= actual.vs_alloca_next /\
  (!name b n. local_region cenv vs.scopes initial name b n ==>
    mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME(ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME(tv,v) ==>
    mem_bytes_at off (type_memory_size tv) actual.vs_memory =
      mem_bytes_at off (type_memory_size tv) initial.vs_memory) ==>
  state_rel func cenv cx vs actual
Proof
  strip_tac >>
  `local_ptrs_rel func cenv vs.scopes initial /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs initial` by
    fs[state_rel_def] >>
  `local_ptrs_rel func cenv vs.scopes actual` by
    (irule local_ptrs_rel_mem_agree >> qexists `initial` >> simp[] >> metis_tac[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor vs actual` by
    (irule immutables_rel_mem_agree >> qexists `initial` >>
     fs[abi_encode_exec_frame_def] >> metis_tac[]) >>
  drule_all abi_encode_caller_world_fields >> strip_tac >>
  drule abi_encode_framed_semantic_fields >> strip_tac >>
  irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`vs`, `initial`] >>
  gvs[abi_encode_exec_frame_def]
QED

Theorem abi_encode_caller_resource_room:
  alloca_room ctx func initial /\ fmp_room ctx func initial /\
  abi_encode_exec_frame observer initial actual /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct observer /\
  (!i. MEM i (fn_insts observer) /\ i.inst_opcode = ALLOCA ==>
    MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    ~MEM i (fn_insts observer) ==>
    FLOOKUP actual.vs_allocas i.inst_id = FLOOKUP initial.vs_allocas i.inst_id) ==>
  alloca_room ctx func actual /\ fmp_room ctx func actual
Proof
  strip_tac >>
  `actual.vs_alloca_next + pending_alloca_size func actual <=
    initial.vs_alloca_next + pending_alloca_size func initial` by
    (irule abi_encode_charge_difference_lift >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `observer` >>
     fs[abi_encode_exec_frame_def]) >>
  fs[alloca_room_def, fmp_room_def, abi_encode_exec_frame_def] >>
  disch_tac >> qpat_x_assum `_ ==> _ /\ _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> decide_tac
QED

Theorem abi_encode_caller_immutable_separation:
  immutable_alloca_sep func cenv cx vs initial /\
  initial.vs_alloca_next <= actual.vs_alloca_next /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!name entry ptr sz.
    lookup_scopes name vs.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) ==>
    lookup_var ptr actual = lookup_var ptr initial) ==>
  immutable_alloca_sep func cenv cx vs actual
Proof
  strip_tac >>
  `!name b n. local_region cenv vs.scopes actual name b n ==>
    local_region cenv vs.scopes initial name b n` by
    (simp_tac bool_ss [local_region_def] >> rpt strip_tac >>
     qpat_x_assum `!name entry ptr sz. _` drule_all >>
     strip_tac >> qexistsl [`entry`, `p`, `w`] >> gvs[]) >>
  fs[immutable_alloca_sep_def] >> disch_tac >> fs[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name tv v off. _` drule_all >> strip_tac >>
  conj_tac >- decide_tac >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP initial.vs_allocas inst.inst_id`
  >- (qpat_x_assum `!i q k. _` drule_all >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  PairCases_on `x` >>
  `FLOOKUP actual.vs_allocas inst.inst_id = SOME(x0,x1)` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

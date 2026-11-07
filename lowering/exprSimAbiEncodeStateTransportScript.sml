Theory exprSimAbiEncodeStateTransport
Ancestors
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFramedSuffix abiEncoderRegisteredEffect
  exprSimAbiEncodeChargeTransfer exprSimAbiEncodeExecFrame localPtrsProps loweringSlice
  compileEnv exprLoweringProps venomState finite_map pred_set list arithmetic
  abiEncoderWindowContract abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderReentry

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

Theorem abi_encode_caller_phase_allocations:
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  window_strong_result ctx observer ready body_end len at av d prepared body_state /\
  actual.vs_allocas = body_state.vs_allocas /\
  actual.vs_alloca_next = body_state.vs_alloca_next ==>
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  window_alloca_growth initial actual /\
  (!i. i <> site /\ i NOTIN window_alloca_sites observer (frag_ids ready body_end) ==>
    FLOOKUP actual.vs_allocas i = FLOOKUP initial.vs_allocas i)
Proof
  strip_tac >>
  `(!i r. FLOOKUP prepared.vs_allocas i = SOME r ==>
      FLOOKUP actual.vs_allocas i = SOME r) /\
   (!i. i NOTIN window_alloca_sites observer (frag_ids ready body_end) ==>
      FLOOKUP actual.vs_allocas i = FLOOKUP prepared.vs_allocas i) /\
   window_alloca_growth prepared actual` by
    (drule window_strong_result_effect >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
     drule window_strong_result_growth >>
     simp[window_alloca_growth_def] >> strip_tac >> simp[]) >>
  qpat_x_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> strip_tac >>
  Cases_on `FLOOKUP initial.vs_allocas site = NONE`
  >- (gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE, window_alloca_growth_def] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_x_assum `!j r. _ = SOME r ==> _ = SOME r`
            (qspecl_then [`i`, `r`] mp_tac) >>
          Cases_on `site = i` >> gvs[]) >>
      rpt gen_tac >> strip_tac >> Cases_on `site = i`
      >- (`FLOOKUP body_state.vs_allocas i = SOME(initial.vs_alloca_next,outsz)` by
            (qpat_x_assum `!j r. _ = SOME r ==> _ = SOME r`
              (qspecl_then [`i`, `(initial.vs_alloca_next,outsz)`] mp_tac) >> simp[]) >>
          gvs[]) >>
      qpat_x_assum `!j b sz. _` (qspecl_then [`i`, `b`, `sz`] mp_tac) >>
      simp[] >> decide_tac) >>
  gvs[abi_builtin_allocate_state_def, window_alloca_growth_def] >>
  qpat_x_assum `!i b sz. _` ACCEPT_TAC
QED

Theorem abi_encode_caller_phase_registers:
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  window_strong_result ctx observer ready body_end len at av d prepared body_state /\
  (!op v. abi_decoder_operand_live body_end.cs_next_var op /\
    eval_operand op body_state = SOME v ==> eval_operand op actual = SOME v) /\
  next <= ready.cs_next_var /\ next <= body_end.cs_next_var ==>
  !x v. abi_decoder_operand_live next (Var x) /\ lookup_var x initial = SOME v ==>
    lookup_var x actual = SOME v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `eval_operand (Var x) prepared = SOME v` by
    (qpat_x_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> strip_tac >>
     qpat_x_assum `!op v. _` irule >> simp[eval_operand_def]) >>
  `not_fresh_at ready x` by
    (fs[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var x body_state = SOME v` by
    (drule window_strong_result_public >>
     simp_tac bool_ss [abi_encoder_window_result_def] >> strip_tac >>
     qpat_x_assum `!x v. _` irule >> gvs[eval_operand_def]) >>
  `abi_decoder_operand_live body_end.cs_next_var (Var x)` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!op v. _` (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def]
QED

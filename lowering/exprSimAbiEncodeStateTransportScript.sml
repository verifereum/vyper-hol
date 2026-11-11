Theory exprSimAbiEncodeStateTransport
Ancestors
  exprSimAbiEncodeCallerFrame exprSimAbiEncodeFramedSuffix abiEncoderRegisteredEffect
  exprSimAbiEncodeChargeTransfer exprSimAbiEncodeExecFrame localPtrsProps loweringSlice
  compileEnv exprLoweringProps venomState finite_map pred_set list arithmetic
  abiEncoderWindowContract abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderReentry
  exprSimAbiEncodeSiteRecovery exprSimAbiEncodeSiteEncoder abiEncoderProps words
  exprSimAbiEncodeSiteResources exprSimAbiEncodePrefixWindow
  exprSimAbiEncodeSuffixOwnership venomMemDefs venomInst abiBuiltinEncodeCorrect

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

Theorem abi_encode_caller_phase_old_rows:
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  window_strong_result ctx observer ready body_end len at av d prepared body_state /\
  abi_encoder_registered_effect {} [(p,32)] body_state actual /\
  actual.vs_allocas = body_state.vs_allocas /\
  actual.vs_alloca_next = body_state.vs_alloca_next /\
  ((FLOOKUP initial.vs_allocas site = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas site = SOME(p,outsz)) /\
  alloca_inv actual /\ site <= ready.cs_next_id /\
  32+w <= outsz /\ p <= d /\ d+LENGTH(enc at av) <= p+outsz ==>
  !aid b sz. FLOOKUP initial.vs_allocas aid = SOME(b,sz) /\ aid < site ==>
    mem_bytes_at b sz actual.vs_memory = mem_bytes_at b sz initial.vs_memory
Proof
  strip_tac >>
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  qabbrev_tac `B = window_alloca_sites observer (frag_ids ready body_end)` >>
  qabbrev_tac `sites = site INSERT B` >>
  `FLOOKUP prepared.vs_allocas site = SOME(p,outsz)` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `FLOOKUP actual.vs_allocas site = SOME(p,outsz)` by
    (drule window_strong_result_effect >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >> metis_tac[]) >>
  `abi_encoder_registered_effect sites [] prepared actual` by
    (drule abi_encode_body_finish_registered >>
     disch_then drule >>
     disch_then (qspecl_then [`site`, `outsz`, `sites`, `B`] mp_tac) >>
     simp[Abbr `sites`, Abbr `B`, SUBSET_DEF] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `aid NOTIN sites` by
    (simp[Abbr `sites`, Abbr `B`, window_alloca_sites_def, frag_ids_def] >>
     rpt strip_tac >> decide_tac) >>
  `FLOOKUP actual.vs_allocas aid = SOME(b,sz)` by
    (qpat_x_assum `!i r. FLOOKUP initial.vs_allocas i = SOME r ==> _` irule >> simp[]) >>
  drule abi_encode_owned_interval_frame >>
  disch_then drule >> disch_then drule >>
  disch_then irule >> simp[Abbr `sites`] >>
  qexistsl [`aid`, `b`, `sz`] >> gvs[]
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

Theorem abi_encode_caller_immutable_base:
  immutable_base_zero cenv initial /\ actual.vs_labels = initial.vs_labels /\
  (!x v. cenv.ce_imm_alloca = SOME (Var x) /\ lookup_var x initial = SOME v ==>
    lookup_var x actual = SOME v) ==>
  immutable_base_zero cenv actual
Proof
  strip_tac >> irule immutable_base_zero_frame >>
  qexists `initial` >> simp[] >> rpt strip_tac >>
  `lookup_var x initial = SOME 0w` by
    (fs[immutable_base_zero_alt, lookup_var_def] >>
     qpat_x_assum `!base. _` (qspec_then `Var x` mp_tac) >> simp[]) >>
  qpat_x_assum `!x v. _` drule_all >> simp[]
QED

Theorem abi_encode_caller_body_literal:
  compile_abi_encode_to_buf dst src ei ready = (len,body_end) /\
  (!j. MEM j (frag_code ready body_end) ==> MEM j (fn_insts func)) /\
  ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts func)) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id IN frag_ids ready body_end ==>
  inst.inst_operands = [Lit 32w]
Proof
  strip_tac >> drule abi_encode_body_site_step >> strip_tac >>
  fs[frag_ids_def] >> drule_all site_interval_alloca >> strip_tac >> simp[]
QED

Theorem abi_encode_caller_phase_row_sizes:
  (!inst n base sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ FLOOKUP initial.vs_allocas inst.inst_id = SOME(base,sz)
    ==> sz = w2n n) /\
  (!i. i <> site /\ i NOTIN window_alloca_sites func (frag_ids ready body_end) ==>
    FLOOKUP actual.vs_allocas i = FLOOKUP initial.vs_allocas i) /\
  FLOOKUP actual.vs_allocas site = SOME(p,outsz) /\
  (!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = site /\ inst.inst_operands = [Lit n] ==> outsz = w2n n) /\
  (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end ==> inst.inst_operands = [Lit 32w]) /\
  (!i b sz. i IN window_alloca_sites func (frag_ids ready body_end) /\
    FLOOKUP actual.vs_allocas i = SOME(b,sz) ==> sz = 32) ==>
  !inst n base sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ FLOOKUP actual.vs_allocas inst.inst_id = SOME(base,sz)
    ==> sz = w2n n
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `inst.inst_id = site`
  >- (gvs[] >> metis_tac[]) >>
  Cases_on `inst.inst_id IN window_alloca_sites func (frag_ids ready body_end)`
  >- (`inst.inst_id IN frag_ids ready body_end` by
        fs[window_alloca_sites_def] >>
      `inst.inst_operands = [Lit 32w]` by metis_tac[] >>
      `n = (32w:256 word)` by
        (qpat_x_assum `inst.inst_operands = [Lit n]` mp_tac >>
         qpat_x_assum `inst.inst_operands = [Lit 32w]` (fn th => rewrite_tac[th]) >>
         simp_tac (srw_ss()) []) >>
      `sz = 32` by
        (qpat_x_assum `!i b sz. i IN window_alloca_sites _ _ /\ _ ==> _`
          irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
      asm_rewrite_tac[] >> simp_tac (srw_ss()) [dimword_def]) >>
  `FLOOKUP actual.vs_allocas inst.inst_id = FLOOKUP initial.vs_allocas inst.inst_id`
    by metis_tac[] >> metis_tac[]
QED

Theorem abi_encode_caller_site_literal:
  fn_inst_ids_distinct func /\
  MEM allocation (fn_insts func) /\ allocation.inst_id = site /\
  allocation.inst_operands = [Lit (n2w outsz)] /\ outsz < dimword (:256) ==>
  !inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = site /\ inst.inst_operands = [Lit n] ==> outsz = w2n n
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `inst = allocation` by metis_tac[fn_inst_ids_distinct_inj] >>
  gvs[] >> simp[]
QED

Theorem abi_encode_phases_caller_state:
 stmt_state_rel ctx func ce cx vs initial /\
 local_ptrs_reserved ce st /\
 abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
 compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
 fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
 fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\
 (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
      j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
 st.cs_next_var <= ready.cs_next_var /\
 st.cs_next_var <= body_end.cs_next_var /\
 outsz = 32+32*word_size (maxlen+(case mid of NONE => 0 | SOME x => 4)) /\
 outsz < dimword (:256) /\ 32+w <= outsz /\
 p <= d /\ d+LENGTH (enc at av) <= p+outsz /\
 abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
 window_strong_result wc obs ready body_end len at av d prepared body_state /\
 abi_encoder_registered_effect {} [(p,32)] body_state actual /\
 actual.vs_allocas = body_state.vs_allocas /\
 actual.vs_alloca_next = body_state.vs_alloca_next /\
 (!op v. abi_decoder_operand_live body_end.cs_next_var op /\
      eval_operand op body_state = SOME v ==> eval_operand op actual = SOME v) /\
 abi_encode_exec_frame obs initial actual /\
 prepared.vs_accounts = initial.vs_accounts /\
 prepared.vs_transient = initial.vs_transient /\
 prepared.vs_logs = initial.vs_logs /\
 prepared.vs_requests = initial.vs_requests /\
 prepared.vs_pending_deletions = initial.vs_pending_deletions /\
 ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   FLOOKUP initial.vs_allocas st.cs_next_id = SOME(p,outsz)) /\
 actual.vs_labels = initial.vs_labels ==>
 stmt_state_rel ctx func ce cx vs actual /\
 (!name b n. local_region ce vs.scopes initial name b n ==>
   mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory) /\
 FLOOKUP actual.vs_allocas st.cs_next_id = SOME(p,outsz) /\
 p+outsz <= actual.vs_alloca_next /\ actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> (
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  `!x v. abi_decoder_operand_live st.cs_next_var (Var x) /\
    lookup_var x initial = SOME v ==> lookup_var x actual = SOME v` by
    (drule abi_encode_caller_phase_registers >>
     disch_then drule >> simp[]) >>
  `!x. not_fresh_at st x ==> abi_decoder_operand_live st.cs_next_var (Var x)` by
    simp[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  `immutable_base_zero ce actual` by
    (irule abi_encode_caller_immutable_base >> qexists `initial` >>
     simp[] >> conj_tac >- (fs[stmt_state_rel_def] >> rpt strip_tac >>
       qpat_x_assum `!x v. _` irule >> simp[] >> fs[local_ptrs_reserved_def]) >>
     fs[stmt_state_rel_def] >> rpt strip_tac >>
     qpat_x_assum `!x v. _` irule >> simp[] >>
     fs[local_ptrs_reserved_def]) >>
  `!name entry ptr sz.
    lookup_scopes name vs.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME(PtrVar (Var ptr) sz) ==>
    lookup_var ptr actual = lookup_var ptr initial` by
    (map_every qx_gen_tac [`name`, `entry`, `lp`, `sz`] >> strip_tac >>
     `?v. lookup_var lp initial = SOME v` by
       (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
     `not_fresh_at st lp` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `abi_decoder_operand_live st.cs_next_var (Var lp)` by metis_tac[] >>
     `lookup_var lp actual = SOME v` by
       (qpat_x_assum `!x v. _` irule >> simp[]) >> simp[]) >>
  qabbrev_tac `B = window_alloca_sites obs (frag_ids ready body_end)` >>
  qabbrev_tac `sites = st.cs_next_id INSERT B` >>
  `FLOOKUP prepared.vs_allocas st.cs_next_id = SOME(p,outsz)` by
    (irule abi_builtin_encode_setup_frame_row >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `FLOOKUP actual.vs_allocas st.cs_next_id = SOME(p,outsz)` by
    (drule window_strong_result_effect >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >> metis_tac[]) >>
  `abi_encoder_registered_effect sites [] prepared actual` by
    (irule abi_encode_body_finish_registered >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexists `B` >>
     simp[Abbr `sites`, Abbr `B`, SUBSET_DEF] >> decide_tac) >>
  `alloca_inv actual` by
    (drule window_strong_result_public >>
     simp_tac bool_ss [abi_encoder_window_result_def] >> strip_tac >>
     fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all abi_encode_setup_alloca_code >>
  qmatch_goalsub_abbrev_tac `MEM allocation (fn_insts obs)` >> strip_tac >>
  `allocation.inst_id = st.cs_next_id /\ allocation.inst_opcode = ALLOCA /\
   allocation.inst_operands = [Lit (n2w outsz)] /\
   allocation.inst_outputs = [STRING #"%" (toString st.cs_next_var)]` by
    simp[Abbr `allocation`, mk_inst_def] >>
  `MEM allocation (fn_insts func)` by
    (qpat_x_assum `!j. MEM j (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
  `!i. i IN sites ==> ?inst q. MEM inst (fn_insts func) /\
    inst.inst_id = i /\ inst.inst_outputs = [q] /\ not_local_ptr ce vs.scopes q` by
    (simp_tac bool_ss [Abbr `sites`, IN_INSERT] >> rpt gen_tac >> strip_tac
     >- (qexistsl [`allocation`, `STRING #"%" (toString st.cs_next_var)`] >>
         simp[] >> irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
     fs[Abbr `B`, window_alloca_sites_def] >>
     `inst.inst_id IN frag_ids ready body_end` by simp[] >>
     drule abi_encode_compiled_scratch_site >>
     disch_then drule >> simp[] >> strip_tac >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!name entry lp sz inst.
    lookup_scopes name vs.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME(PtrVar (Var lp) sz) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [lp] ==> inst.inst_id NOTIN sites` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_local_site_id_exclusion >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`ce`, `entry`, `name`, `vs.scopes`, `sz`] >> simp[]) >>
  `!i. i IN sites ==> ?inst. MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = i` by
    (simp_tac bool_ss [Abbr `sites`, IN_INSERT] >> rpt gen_tac >> strip_tac
     >- (qexists `allocation` >> simp[]) >>
     fs[Abbr `B`, window_alloca_sites_def] >> qexists `inst` >> simp[] >>
     qpat_x_assum `!j. MEM j (fn_insts obs) /\ _ ==> _` irule >> simp[]) >>
  `state_rel func ce cx vs initial /\ local_ptrs_rel func ce vs.scopes initial /\
   immutable_alloca_sep func ce cx vs initial` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `initial.vs_alloca_next <= actual.vs_alloca_next /\
   (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
     FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q)` by
    (fs[window_alloca_growth_def] >> rpt strip_tac >>
     qpat_x_assum `!i b sz. _` (qspecl_then [`i`, `q`, `k`] mp_tac) >> simp[]) >>
  `!name b n. local_region ce vs.scopes initial name b n ==>
    mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory` by
    (`st.cs_next_id IN sites` by simp[Abbr `sites`] >>
     rpt gen_tac >> strip_tac >>
     drule_all abi_encode_caller_local_reads >> simp[]) >>
  `(ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME(ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME(tv,v) ==>
    mem_bytes_at off (type_memory_size tv) actual.vs_memory =
      mem_bytes_at off (type_memory_size tv) initial.vs_memory)` by
    (`st.cs_next_id IN sites` by simp[Abbr `sites`] >>
     strip_tac >> rpt gen_tac >> strip_tac >>
     drule_all abi_encode_caller_immutable_reads >> simp[]) >>
  `state_rel func ce cx vs actual` by
    (drule_all abi_encode_caller_state_rel >> simp[]) >>
  `immutable_alloca_sep func ce cx vs actual` by
    (drule_all abi_encode_caller_immutable_separation >> simp[]) >>
  `!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
    MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    ~MEM i (fn_insts obs) ==>
    FLOOKUP actual.vs_allocas i.inst_id = FLOOKUP initial.vs_allocas i.inst_id` by
    (rpt strip_tac >>
     `i.inst_id <> st.cs_next_id` by
       (strip_tac >> `i = allocation` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
     `i.inst_id NOTIN B` by
       (simp[Abbr `B`, window_alloca_sites_def] >> disj2_tac >> rpt strip_tac >>
        `MEM inst (fn_insts func)` by
          (qpat_x_assum `!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==> _` irule >> simp[]) >>
        `i = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
     qpat_x_assum `!i. i <> _ /\ i NOTIN B ==> _` irule >> simp[]) >>
  `alloca_room ctx func initial /\ fmp_room ctx func initial` by
    fs[stmt_state_rel_def] >>
  `alloca_room ctx func actual /\ fmp_room ctx func actual` by
    (drule_all abi_encode_caller_resource_room >> simp[]) >>
  `!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = st.cs_next_id /\ inst.inst_operands = [Lit n] ==> outsz = w2n n` by
    (rpt gen_tac >> strip_tac >>
     `inst = allocation` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[] >> simp[]) >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `alloca_inv actual` mp_tac >>
          simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >>
          metis_tac[]) >>
      qpat_assum `alloca_room ctx func actual` mp_tac >>
      simp_tac bool_ss [alloca_room_def] >> strip_tac >> decide_tac) >>
  simp_tac bool_ss [stmt_state_rel_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id = st.cs_next_id`
  >- (qpat_x_assum `!inst n. MEM inst (fn_insts func) /\ _ ==> outsz = _` drule_all >>
      strip_tac >>
      `FLOOKUP body_state.vs_allocas st.cs_next_id = SOME(p,outsz)` by metis_tac[] >>
      gvs[]) >>
  Cases_on `inst.inst_id IN B`
  >- (`?j. MEM j (fn_insts obs) /\ j.inst_opcode = ALLOCA /\
        j.inst_id = inst.inst_id` by (fs[Abbr `B`, window_alloca_sites_def] >> metis_tac[]) >>
      `MEM j (fn_insts func)` by
        (qpat_x_assum `!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==> _` irule >> simp[]) >>
      `j = inst` by metis_tac[fn_inst_ids_distinct_inj] >> gvs[] >>
      `inst.inst_id IN frag_ids ready body_end` by fs[Abbr `B`, window_alloca_sites_def] >>
      `inst.inst_operands = [Lit 32w]` by
        (`cs_extends ready body_end` by (drule abiEncoderAppendTheory.cs_extends_abi_encode >> simp[]) >>
         `!j. MEM j (frag_code ready body_end) ==> MEM j (fn_insts obs)` by
           (rpt strip_tac >> irule abi_encode_frag_code_members >>
            goal_assum (drule_at Any) >> simp[]) >>
         `ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts obs))` by
           (irule ctorAbiActualArrayRunTheory.ctor_actual_function_ids >> simp[]) >>
         drule_all abi_encode_caller_body_literal >> simp[]) >>
      `sz = 32` by
        (`inst.inst_id IN window_alloca_sites obs (frag_ids ready body_end)` by
           fs[Abbr `B`] >>
         drule_all window_strong_result_sizes >> simp[]) >>
      gvs[] >> simp[dimword_def]) >>
  `FLOOKUP actual.vs_allocas inst.inst_id = FLOOKUP initial.vs_allocas inst.inst_id` by
    (qpat_x_assum `!i. i <> _ /\ i NOTIN B ==> _` irule >> simp[]) >>
  fs[stmt_state_rel_def] >> metis_tac[])
QED

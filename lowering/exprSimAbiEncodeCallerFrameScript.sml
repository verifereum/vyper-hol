Theory exprSimAbiEncodeCallerFrame
Ancestors
  loweringStateRelDefs
  compileEnv venomMemDefs venomState venomInst finite_map pred_set list arithmetic
  exprSimAbiEncodeSuffixOwnership exprSimAbiEncodeFrameTransfer abiDecodeStaticProps
  exprLoweringProps localPtrsProps exprSimAbiEncodeSiteResources
  abiEncoderWindowContract exprSimAbiEncodePrefixWindow

(* compileEnv's curried regions_disjoint is strong endpoint separation,
   unlike venomMemDefs' paired, zero-size-aware predicate. *)
Theorem abi_encode_initial_local_separation:
  !func ptr initial b n actual ids.
  local_backed func ptr initial b n /\
  b+n <= initial.vs_alloca_next /\ alloca_inv actual /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) ==>
  !i q k. i IN ids /\ FLOOKUP actual.vs_allocas i = SOME(q,k) ==>
    b+n <= q \/ q+k <= b
Proof
  rpt gen_tac >> simp_tac bool_ss [local_backed_def] >> strip_tac >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `alloca_inv actual` mp_tac >>
      simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
      strip_tac >> metis_tac[]) >>
  Cases_on `FLOOKUP initial.vs_allocas i`
  >- (qpat_x_assum `!i q k. _ /\ _ ==> _` drule_all >> decide_tac) >>
  PairCases_on `x` >>
  `FLOOKUP actual.vs_allocas i = SOME(x0,x1)` by metis_tac[] >>
  gvs[] >> qpat_x_assum `!aid b' sz'. _` drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, ADD_COMM]
QED

Theorem abi_encode_initial_region_separation:
  b+n <= initial.vs_alloca_next /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!i q k. i IN ids /\ FLOOKUP initial.vs_allocas i = SOME(q,k) ==>
    b+n <= q \/ q+k <= b) ==>
  !i q k. i IN ids /\ FLOOKUP actual.vs_allocas i = SOME(q,k) ==>
    b+n <= q \/ q+k <= b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP initial.vs_allocas i`
  >- (qpat_x_assum `!i q k. _ /\ _ ==> _` drule_all >> decide_tac) >>
  PairCases_on `x` >>
  `FLOOKUP actual.vs_allocas i = SOME(x0,x1)` by metis_tac[] >>
  gvs[] >> first_x_assum drule_all >> simp[ADD_COMM]
QED

Theorem abi_encode_separated_interval_frame:
  abi_builtin_encode_setup_frame next site outsz p w initial prepared /\
  abi_encoder_registered_effect ids [] prepared actual /\
  site IN ids /\ FLOOKUP actual.vs_allocas site = SOME(p,outsz) /\
  32+w <= outsz /\
  (!i q k. i IN ids /\ FLOOKUP actual.vs_allocas i = SOME(q,k) ==>
    b+n <= q \/ q+k <= b) ==>
  mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b n actual.vs_memory = mem_bytes_at b n prepared.vs_memory` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     irule abi_encode_registered_protected_byte >>
     qexistsl [`ids`, `b`, `n`, `[]`] >> simp[] >>
     rpt strip_tac >> first_x_assum drule_all >> decide_tac) >>
  `b+n <= p \/ p+outsz <= b` by metis_tac[] >>
  `mem_bytes_at b n prepared.vs_memory = mem_bytes_at b n initial.vs_memory` by
    (irule abi_encode_setup_memory_effect >> goal_assum (drule_at Any) >> decide_tac) >>
  simp[]
QED

Theorem abi_encode_initial_alloca_region_separation:
  b+n <= initial.vs_alloca_next /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!inst q k. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME(q,k) ==>
    loweringStateRelDefs$regions_disjoint b n q k) /\
  (!i. i IN ids ==> ?inst. MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = i) ==>
  !i q k. i IN ids /\ FLOOKUP actual.vs_allocas i = SOME(q,k) ==>
    b+n <= q \/ q+k <= b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP initial.vs_allocas i`
  >- (qpat_x_assum `!i q k. _ /\ _ ==> _` drule_all >> decide_tac) >>
  PairCases_on `x` >>
  `FLOOKUP actual.vs_allocas i = SOME(x0,x1)` by metis_tac[] >>
  gvs[] >>
  qpat_x_assum `!i. i IN ids ==> _` drule >> strip_tac >> gvs[] >>
  qpat_x_assum `!inst q k. _` drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, ADD_COMM]
QED

Theorem abi_encode_local_ptr_separation:
  !func cenv scopes initial actual ids name entry ptr sz w.
  local_ptrs_rel func cenv scopes initial /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) /\
  lookup_var ptr initial = SOME w /\ alloca_inv actual /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids) ==>
  !i q k. i IN ids /\ FLOOKUP actual.vs_allocas i = SOME(q,k) ==>
    w2n w+sz <= q \/ q+k <= w2n w
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp_tac bool_ss [local_ptrs_rel_def] >> strip_tac >>
  qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >> gvs[] >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] abi_encode_initial_local_separation) >>
  simp[ADD_COMM] >> disch_then drule >> simp[ADD_COMM] >>
  disch_then (qspec_then `ids` mp_tac) >>
  simp[GSYM AND_IMP_INTRO] >> metis_tac[]
QED

Theorem abi_encode_immutable_region_separation:
  immutable_alloca_sep func cenv cx vs initial /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME(ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP vs.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME(tv,v) /\
  (!i r. FLOOKUP initial.vs_allocas i = SOME r ==>
    FLOOKUP actual.vs_allocas i = SOME r) /\
  (!i q k. FLOOKUP actual.vs_allocas i = SOME(q,k) /\
    FLOOKUP initial.vs_allocas i = NONE ==> initial.vs_alloca_next <= q) /\
  (!i. i IN ids ==> ?inst. MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = i) ==>
  !i q k. i IN ids /\ FLOOKUP actual.vs_allocas i = SOME(q,k) ==>
    off+type_memory_size tv <= q \/ q+k <= off
Proof
  strip_tac >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] abi_encode_initial_alloca_region_separation) >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`ids`, `func`] mp_tac) >>
  fs[GSYM AND_IMP_INTRO] >> strip_tac >> rpt gen_tac >>
  ntac 2 disch_tac >> first_x_assum irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists `i` >> simp[]
QED

Theorem abi_encode_local_site_id_exclusion:
  !func cenv scopes name entry ptr sz ids.
  fn_inst_ids_distinct func /\ lookup_scopes name scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME(PtrVar (Var ptr) sz) /\
  (!i. i IN ids ==> ?inst q. MEM inst (fn_insts func) /\
    inst.inst_id = i /\ inst.inst_outputs = [q] /\ not_local_ptr cenv scopes q) ==>
  !inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN ids
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `!i. i IN ids ==> _` drule >> strip_tac >>
  `inst = inst'` by metis_tac[fn_inst_ids_distinct_inj] >>
  qpat_x_assum `inst = inst'` SUBST_ALL_TAC >>
  `q = ptr'` by metis_tac[listTheory.CONS_11] >>
  qpat_x_assum `not_local_ptr _ _ _` mp_tac >>
  simp_tac bool_ss [not_local_ptr_def] >> metis_tac[]
QED

Theorem abi_encode_scratch_local_id_exclusion:
  !dst src ei ready out body_end obs func ce earlier scopes name entry ptr sz.
  compile_abi_encode_to_buf dst src ei ready = (out,body_end) /\
  fn_has_code ready body_end obs /\ fn_inst_ids_distinct obs /\
  fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  local_ptrs_reserved ce earlier /\ earlier.cs_next_var <= ready.cs_next_var /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME(PtrVar (Var ptr) sz) ==>
  !inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==>
    inst.inst_id NOTIN window_alloca_sites obs (frag_ids ready body_end)
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i IN window_alloca_sites obs (frag_ids ready body_end) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = i /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q` by
    (simp[window_alloca_sites_def] >> rpt strip_tac >> gvs[] >>
     drule_all abi_encode_compiled_scratch_site >>
     disch_then (qspec_then `scopes` strip_assume_tac) >>
     qexistsl [`inst`, `q`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule abi_encode_local_site_id_exclusion >>
  metis_tac[]
QED

Theorem abi_encode_setup_local_id_exclusion:
  !mid maxlen st ops ready func ce earlier name scopes entry ptr sz.
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  fn_has_code st ready func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce earlier /\ earlier.cs_next_var <= st.cs_next_var /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME(PtrVar (Var ptr) sz) ==>
  !inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ptr] ==> inst.inst_id <> st.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_setup_alloca_code >> strip_tac >>
  `not_local_ptr ce scopes (STRING #"%" (toString st.cs_next_var))` by
    metis_tac[local_ptrs_reserved_fresh] >>
  `!i. i IN {st.cs_next_id} ==> ?inst q.
    MEM inst (fn_insts func) /\ inst.inst_id = i /\
    inst.inst_outputs = [q] /\ not_local_ptr ce scopes q` by
    (simp[] >> qexistsl
      [`mk_inst st.cs_next_id ALLOCA
        [Lit (n2w (32 + 32 * word_size
          (maxlen + (case mid of NONE => 0 | SOME _ => 4))))]
        [STRING #"%" (toString st.cs_next_var)]`,
       `STRING #"%" (toString st.cs_next_var)`] >>
     simp[mk_inst_def]) >>
  rpt gen_tac >> strip_tac >>
  `inst.inst_id NOTIN {st.cs_next_id}` suffices_by simp[] >>
  irule abi_encode_local_site_id_exclusion >> metis_tac[]
QED

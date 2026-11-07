Theory exprSimAbiEncodeCallerFrame
Ancestors
  compileEnv venomMemDefs venomState venomInst finite_map pred_set list arithmetic
  exprSimAbiEncodeSuffixOwnership exprSimAbiEncodeFrameTransfer abiDecodeStaticProps

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
  simp[compileEnvTheory.regions_disjoint_def, ADD_COMM]
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
    compileEnv$regions_disjoint b n q k) /\
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
  simp[compileEnvTheory.regions_disjoint_def, ADD_COMM]
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

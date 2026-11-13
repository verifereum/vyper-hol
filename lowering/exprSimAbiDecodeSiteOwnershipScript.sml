(* Caller-side ownership probes: the output allocation is not scratch. *)
Theory exprSimAbiDecodeSiteOwnership
Ancestors
  exprSimAbiDecodeScratchCover exprSimAbiDecodeSiteProvenance
  actualDecoderSites allocaSiteResource
  abiBuiltinAllocation venomMemDefs finite_map pred_set arithmetic

Theorem abi_decode_setup_output_registered:
  abi_builtin_allocation_frame next site outsz s t /\
  ((FLOOKUP s.vs_allocas site = NONE /\ d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas site = SOME (d,outsz)) ==>
  FLOOKUP t.vs_allocas site = SOME (d,outsz)
Proof
  rw[abi_builtin_allocation_frame_def, abi_builtin_allocate_state_def] >>
  gvs[FLOOKUP_UPDATE]
QED

(* Any scratch-site set excluding the output's ID has a stable permission
   disjoint from the entire output, on fresh allocation and on reuse alike. *)
Theorem abi_decode_registered_output_scratch:
  alloca_inv s /\ FLOOKUP s.vs_allocas output = SOME(d,n) /\
  output NOTIN sites ==>
  d+n <= s.vs_alloca_next /\
  abi_decode_scratch_cover sites
    ({a | s.vs_alloca_next <= a} UNION
     {a | ?id b sz. id IN sites /\
       FLOOKUP s.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}) s /\
  (!a. d <= a /\ a < d+n ==>
    a NOTIN ({a | s.vs_alloca_next <= a} UNION
     {a | ?id b sz. id IN sites /\
       FLOOKUP s.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}))
Proof
  strip_tac >>
  `d+n <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  conj_tac >- simp[] >> conj_tac
  >- (simp[abi_decode_scratch_cover_def, SUBSET_DEF] >> metis_tac[]) >>
  simp[] >> gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> spose_not_then strip_assume_tac >>
  `output <> id` by metis_tac[] >>
  drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_decode_output_slice_scratch:
  d+n <= s.vs_alloca_next /\ off+len <= n /\
  (!a. d <= a /\ a < d+n ==> a NOTIN scratch) ==>
  d+off+len <= s.vs_alloca_next /\
  (!a. d+off <= a /\ a < d+off+len ==> a NOTIN scratch)
Proof
  strip_tac >> conj_tac >- decide_tac >>
  gen_tac >> strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem abi_decode_output_registration_progress:
  abi_decode_alloc_progress sites s t /\
  FLOOKUP s.vs_allocas output = SOME(d,n) ==>
  FLOOKUP t.vs_allocas output = SOME(d,n)
Proof
  simp[abi_decode_alloc_progress_def]
QED

(* The DynArray slot ALLOCA preserves output registration and obtains
   disjointness from it even when the slot is reused below the frontier. *)
Theorem abi_decode_scratch_allocation_output:
  decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit w] /\ inst.inst_outputs = [v] /\
  FLOOKUP s.vs_allocas output = SOME(d,n) /\ inst.inst_id <> output ==>
  ?t b. exec_alloca inst s w = OK t /\ decode_site_resources ctx func t /\
    FLOOKUP t.vs_allocas output = SOME(d,n) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME(b,w2n w) /\
    d+n <= t.vs_alloca_next /\
    venomMemDefs$regions_disjoint (d,n) (b,w2n w)
Proof
  strip_tac >> drule_all decode_site_allocation >> strip_tac >>
  `FLOOKUP t.vs_allocas output = SOME(d,n)` by metis_tac[] >>
  `alloca_inv t` by fs[decode_site_resources_def] >>
  qexistsl [`t`, `b`] >> simp[] >> conj_tac
  >- metis_tac[alloca_site_registered_below] >>
  irule alloca_site_registered_disjoint >> metis_tac[]
QED

Theorem abi_decode_setup_alloca_inv:
  abi_builtin_allocation_frame next site outsz s t /\ alloca_inv s ==>
  alloca_inv t
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, alloca_inv_def,
      allocas_non_overlapping_def, alloca_next_valid_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `!aid base sz. FLOOKUP s.vs_allocas aid = SOME(base,sz) ==> _`
    (fn th => imp_res_tac th) >> fs[] >> metis_tac[]
QED

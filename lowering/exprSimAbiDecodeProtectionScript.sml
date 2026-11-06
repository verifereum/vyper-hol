Theory exprSimAbiDecodeProtection
Ancestors
  exprSimAbiDecodeEndpointFrame abiDecoderSiteEffect compileEnv
  finite_map pred_set

Theorem abi_decode_interval_row_separation:
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t /\
  q + n <= s.vs_alloca_next /\
  (!id b sz. first <= id /\ id < last /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    compileEnv$regions_disjoint b sz q n) /\
  first <= id /\ id < last /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
  compileEnv$regions_disjoint b sz q n
Proof
  simp_tac bool_ss [abi_decode_allocation_floor_def] >> strip_tac >>
  qpat_x_assum `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==> _`
    drule >> strip_tac
  >- metis_tac[] >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Definition abi_decode_write_set_def:
  abi_decode_write_set d outsz lo first last t =
    {a | d <= a /\ a < d + outsz} UNION {a | lo <= a} UNION
    {a | ?id b sz. first <= id /\ id < last /\
      FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz}
End

Theorem abi_decode_write_set_protects:
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t /\
  first <= outid /\ outid < last /\
  FLOOKUP t.vs_allocas outid = SOME (d,outsz) /\
  q + n <= s.vs_alloca_next /\
  (!id b sz. first <= id /\ id < last /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    compileEnv$regions_disjoint b sz q n) ==>
  decode_protects (abi_decode_write_set d outsz s.vs_alloca_next first last t) {(q,n)}
Proof
  strip_tac >>
  `compileEnv$regions_disjoint d outsz q n` by
    (irule abi_decode_interval_row_separation >> metis_tac[]) >>
  simp[decode_protects_def, abi_decode_write_set_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `compileEnv$regions_disjoint b sz q n` by
    (irule abi_decode_interval_row_separation >>
     qexistsl_tac [`first`, `id`, `last`, `s`, `t`] >>
     asm_rewrite_tac [] >> decide_tac) >>
  gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_decode_write_set_memory_frame:
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t /\
  first <= outid /\ outid < last /\
  FLOOKUP t.vs_allocas outid = SOME (d,outsz) /\
  q + n <= s.vs_alloca_next /\
  (!id b sz. first <= id /\ id < last /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    compileEnv$regions_disjoint b sz q n) /\
  decode_site_effect ctx func next
    (abi_decode_write_set d outsz s.vs_alloca_next first last t) s t ==>
  mem_bytes_at q n (t with <|vs_returndata := rd; vs_prev_bb := prev|>).vs_memory =
  mem_bytes_at q n s.vs_memory
Proof
  strip_tac >>
  `decode_protects (abi_decode_write_set d outsz s.vs_alloca_next first last t)
      {(q,n)}` by
    (irule abi_decode_write_set_protects >>
     asm_rewrite_tac [] >> qexists_tac `outid` >> asm_rewrite_tac []) >>
  simp[] >>
  drule decode_site_effect_protected >>
  disch_then (qspec_then `{(q,n)}` mp_tac) >>
  asm_rewrite_tac [] >> simp[]
QED

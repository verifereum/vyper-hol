Theory bodyPtrPrecompileBuiltinsPayloadFrames
Ancestors abiEncoderZeroFrame exprSimLiteralBuffer exprSimProps
          loweringPosts compileEnv loweringStateRelDefs exprLoweringProps valueEncoding venomState
          venomExecSemantics finite_map

Theorem scratch_exterior_region:
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 m' = mem_bytes_at i 1 m) /\
  (b+n <= a \/ a+sz <= b) ==>
  mem_bytes_at a sz m' = mem_bytes_at a sz m
Proof
  strip_tac >> irule abi_encoder_mem_bytes_singletons >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem scratch_store_state_frame:
  stmt_state_rel ctx fn cenv cx es s /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
    b+n <= a \/ a+sz <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    b+n <= off \/ off+type_memory_size tv <= b) ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  strip_tac >> irule literal_state_memory_frame >>
  qexists `s` >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule scratch_exterior_region >> metis_tac[]) >>
  conj_tac >- (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >> irule scratch_exterior_region >> metis_tac[]
QED

Theorem scratch_reset_allocations:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  first_x_assum
    (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next)`) >> simp[]
QED

Theorem scratch_store_wb_frame:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  sc.cs_next_var <= sa.cs_next_var /\
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
    b+n <= a \/ a+sz <= b) /\
  (!aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sc.cs_next_id ==>
    b+n <= a \/ a+sz <= b) ==>
  wb_frame cenv es es sc s t
Proof
  strip_tac >> drule scratch_reset_allocations >> strip_tac >>
  simp[wb_frame_def] >>
  conj_tac >-
    (rpt strip_tac >>
     `not_fresh_at sa x` by (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> irule scratch_exterior_region >> metis_tac[]) >>
  irule locals_kept_regions >> rpt strip_tac >>
  irule scratch_exterior_region >> metis_tac[]
QED

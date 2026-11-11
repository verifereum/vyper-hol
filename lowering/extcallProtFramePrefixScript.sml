(* Concrete write envelopes for protected request-prefix windows. *)
Theory extcallProtFramePrefix
Ancestors
  extcallProtFramePath abiEncoderWindowContract abiEncoderRegisteredEffect compileEnv
  finite_map pred_set list

Theorem extcall_protframe_growth_geometry:
  window_alloca_growth s t /\
  (!i r. FLOOKUP s.vs_allocas i = SOME r ==>
    FLOOKUP t.vs_allocas i = SOME r) /\
  pa + pk <= s.vs_alloca_next /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
    compileEnv$regions_disjoint pa pk b n) ==>
  pa + pk <= t.vs_alloca_next /\
  !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
    compileEnv$regions_disjoint pa pk b n
Proof
  strip_tac >> conj_tac
  >- metis_tac[window_alloca_growth_frontier] >>
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas i`
  >- (fs[window_alloca_growth_def] >>
      `s.vs_alloca_next <= b` by metis_tac[] >>
      simp[compileEnvTheory.regions_disjoint_def]) >>
  `FLOOKUP t.vs_allocas i = SOME x` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

Theorem extcall_protframe_registered_outputs:
  abi_encoder_registered_effect ids outs s t /\ window_alloca_growth s t /\
  (!d k. MEM (d,k) outs ==> ?i b n.
    FLOOKUP t.vs_allocas i = SOME (b,n) /\ b <= d /\ d+k <= b+n) /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      compileEnv$regions_disjoint pa pk b n) ==>
  !pa pk. prot pa pk ==>
    pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
      compileEnv$regions_disjoint pa pk b n
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==>
    FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `pa + pk <= t.vs_alloca_next /\
   !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
     compileEnv$regions_disjoint pa pk b n` by
    (irule extcall_protframe_growth_geometry >> qexists_tac `s` >>
     simp[] >> metis_tac[]) >>
  `mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk s.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`ids`, `outs`] >> rpt conj_tac
     >- (rpt strip_tac >>
         `compileEnv$regions_disjoint pa pk b sz` by metis_tac[] >>
         fs[compileEnvTheory.regions_disjoint_def,
            venomMemDefsTheory.regions_disjoint_def])
     >- (rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
         rename1 `MEM output outs` >> PairCases_on `output` >>
         qpat_x_assum `!d k. MEM (d,k) outs ==> _` drule >> strip_tac >>
         `compileEnv$regions_disjoint pa pk b n` by metis_tac[] >>
         fs[compileEnvTheory.regions_disjoint_def,
            venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

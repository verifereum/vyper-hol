(* Byte envelopes are applied before the joint unwrap forgets its writes. *)
Theory extcallProtFrameKwargUnwrap
Ancestors
  extcallProtFramePrefix extcallProtFramePath exprExtRequestJointUnwrap
  compileEnv finite_map

Theorem extcall_protframe_allocated_write_path:
  gas_marked_path memory ctx func s marks (OK t) /\
  FLOOKUP s.vs_allocas owner = SOME (baddr,capacity) /\
  baddr <= dst /\ dst + nbytes <= baddr + capacity /\
  (!pa pk. compileEnv$regions_disjoint dst nbytes pa pk ==>
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk s.vs_memory) /\
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
  strip_tac >> drule gas_marked_path_window_alloca_growth >> strip_tac >>
  drule gas_marked_path_allocas_preserved >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  `pa + pk <= t.vs_alloca_next /\
   !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
     compileEnv$regions_disjoint pa pk b n` by
    (irule extcall_protframe_growth_geometry >> qexists_tac `s` >>
     simp[] >> metis_tac[]) >>
  `compileEnv$regions_disjoint pa pk baddr capacity` by metis_tac[] >>
  `compileEnv$regions_disjoint dst nbytes pa pk` by
    (fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk s.vs_memory` by
    (qpat_x_assum `!pa pk. compileEnv$regions_disjoint dst nbytes pa pk ==> _`
       irule >> simp[]) >>
  metis_tac[]
QED

Theorem extcall_protframe_readonly_path:
  gas_marked_path memory ctx func s marks (OK t) /\
  t.vs_memory = s.vs_memory /\
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
  strip_tac >> drule gas_marked_path_window_alloca_growth >> strip_tac >>
  drule gas_marked_path_allocas_preserved >> strip_tac >>
  rpt gen_tac >> disch_tac >> simp[] >>
  `pa + pk <= t.vs_alloca_next /\
   !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
     compileEnv$regions_disjoint pa pk b n` by
    (irule extcall_protframe_growth_geometry >> qexists_tac `s` >>
     simp[] >> metis_tac[]) >> metis_tac[]
QED

(* Arbitrary protected windows across allocated decoder writes. *)
Theory extcallProtFrameDecode
Ancestors
  abiValidAllocatedContract abiMalformedSiteFrame abiMalformedRecursiveInterface
  extcallProtFramePath abiEncoderWindowContract compileEnv venomMemDefs
  venomState finite_map pred_set arithmetic

Theorem abi_valid_allocated_frame_protected:
  abi_valid_allocated_frame sites d n s t /\
  q + k <= s.vs_alloca_next /\
  compileEnv$regions_disjoint q k d n /\
  (!aid b sz. aid IN sites /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    compileEnv$regions_disjoint q k b sz) ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  strip_tac >> irule abi_valid_allocated_frame_slice >>
  goal_assum (drule_at Any) >> rpt gen_tac >> strip_tac >> conj_tac
  >- (fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  simp[abi_malformed_site_range_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `aid IN sites` >> simp[] >>
  qpat_x_assum `!aid b sz. _` drule_all >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_valid_allocated_frame_path_protected:
  gas_marked_path memory ctx func s gas (OK u) /\
  u.vs_memory = s.vs_memory /\
  q + k <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    compileEnv$regions_disjoint q k b sz) /\
  abi_malformed_destination host ce scopes dstid d n u /\
  abi_valid_allocated_frame sites d n u t ==>
  mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory
Proof
  strip_tac >>
  `window_alloca_growth s u` by
    metis_tac[gas_marked_path_window_alloca_growth] >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==>
    FLOOKUP u.vs_allocas i = SOME r` by
    metis_tac[gas_marked_path_allocas_preserved] >>
  `!i b sz. FLOOKUP u.vs_allocas i = SOME (b,sz) ==>
    compileEnv$regions_disjoint q k b sz` by
    (rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas i`
     >- (fs[window_alloca_growth_def] >>
         `s.vs_alloca_next <= b` by metis_tac[] >>
         simp[compileEnvTheory.regions_disjoint_def]) >>
     rename1 `SOME entry` >>
     `FLOOKUP u.vs_allocas i = SOME entry` by metis_tac[] >>
     gvs[] >> metis_tac[]) >>
  `compileEnv$regions_disjoint q k d n` by
    (fs[abi_malformed_destination_def] >>
     qpat_x_assum `!i b sz. FLOOKUP u.vs_allocas i = _ ==> _` drule >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at q k t.vs_memory = mem_bytes_at q k u.vs_memory` by
    metis_tac[window_alloca_growth_frontier, abi_valid_allocated_frame_protected] >>
  simp[]
QED

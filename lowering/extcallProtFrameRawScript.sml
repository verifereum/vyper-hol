(* Protection is attached while raw vv posts and normal paths coexist. *)
Theory extcallProtFrameRaw
Ancestors
  extcallProtFramePath loweringPosts supportedExprTraverse compileEnv
  abiEncoderWindowContract finite_map pred_set

Theorem pure_vv_window_growth_protected:
  vv_post ctx func cenv cx e es sa sb s ee v vv t /\
  window_alloca_growth s t /\
  (!i r. FLOOKUP s.vs_allocas i = SOME r ==>
         FLOOKUP t.vs_allocas i = SOME r) /\
  (!e es sa sb s ee v vv t.
    vv_post ctx func cenv cx e es sa sb s ee v vv t /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sa.cs_next_id <= inst.inst_id /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint off len b sz) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)) /\
  (!pa pk. prot pa pk ==> ~expr_has_effect e) /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !pid pb pz. FLOOKUP s.vs_allocas pid = SOME (pb,pz) ==>
      compileEnv$regions_disjoint pa pk pb pz) ==>
  !pa pk. prot pa pk ==>
    pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
    !pid pb pz. FLOOKUP t.vs_allocas pid = SOME (pb,pz) ==>
      compileEnv$regions_disjoint pa pk pb pz
Proof
  strip_tac >> qx_gen_tac `pa` >> qx_gen_tac `pk` >> disch_tac >>
  `pa + pk <= s.vs_alloca_next` by metis_tac[] >>
  `!pid pb pz. FLOOKUP t.vs_allocas pid = SOME (pb,pz) ==>
     compileEnv$regions_disjoint pa pk pb pz` by
    (rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas pid`
     >- (fs[window_alloca_growth_def] >>
         `s.vs_alloca_next <= pb` by metis_tac[] >>
         simp[compileEnvTheory.regions_disjoint_def]) >>
     `FLOOKUP t.vs_allocas pid = SOME x` by metis_tac[] >>
     gvs[] >> metis_tac[]) >>
  `~expr_has_effect e` by metis_tac[] >>
  qpat_x_assum `!e es sa sb s ee v vv t. _` drule >>
  simp[] >> strip_tac >>
  `mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk s.vs_memory` by
    (first_x_assum irule >> metis_tac[]) >>
  metis_tac[window_alloca_growth_frontier]
QED

Theorem pure_vv_marked_path_protected:
  vv_post ctx func cenv cx e es sa sb s ee v vv t /\
  gas_marked_path memory ctx func s n (OK t) /\
  (!e es sa sb s ee v vv t.
    vv_post ctx func cenv cx e es sa sb s ee v vv t /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sa.cs_next_id <= inst.inst_id /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint off len b sz) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory)) /\
  (!pa pk. prot pa pk ==> ~expr_has_effect e) /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !pid pb pz. FLOOKUP s.vs_allocas pid = SOME (pb,pz) ==>
      compileEnv$regions_disjoint pa pk pb pz) ==>
  !pa pk. prot pa pk ==>
    pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
    !pid pb pz. FLOOKUP t.vs_allocas pid = SOME (pb,pz) ==>
      compileEnv$regions_disjoint pa pk pb pz
Proof
  strip_tac >>
  drule gas_marked_path_window_alloca_growth >> strip_tac >>
  drule gas_marked_path_allocas_preserved >> strip_tac >>
  qx_gen_tac `pa` >> qx_gen_tac `pk` >> disch_tac >>
  drule pure_vv_window_growth_protected >>
  disch_then (qspecl_then [`prot`, `original`, `pa`, `pk`] mp_tac) >>
  simp[] >> disch_then irule >>
  rpt conj_tac >> gvs[] >> rpt strip_tac >> metis_tac[]
QED

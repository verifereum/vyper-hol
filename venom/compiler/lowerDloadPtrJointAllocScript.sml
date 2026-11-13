Theory lowerDloadPtrJointAlloc
Ancestors
  lowerDloadPtrJointNext lowerDloadPtrAllocTransport lowerDloadPtrAlloc
  lowerDloadPtrRel lowerDloadPtrAggregate lowerDloadPtrCall lowerDloadPtrBlockEntry ptrDiscipline
  o1PassContract lowerDloadDefs venomExecSemantics venomState venomInst
  contextCodegenRel finite_map list pred_set words

Theorem dload_alloca_step_shape[local]:
  i.inst_opcode = ALLOCA /\ step_inst fuel C i t = OK t1 ==>
  ?amount out. i.inst_operands = [Lit amount] /\ i.inst_outputs = [out] /\
    exec_alloca i t amount = OK t1
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dload_alloca_step_fields[local]:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit amount] /\
  i.inst_outputs = [out] ==>
  ?s1. step_inst fuel C i s = OK s1 /\ exec_alloca i s amount = OK s1 /\
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id` >>
  simp[exec_alloca_def, update_var_def] >>
  rename1 `FLOOKUP s.vs_allocas i.inst_id = SOME site` >>
  PairCases_on `site` >> simp[exec_alloca_def, update_var_def]
QED

Theorem dload_actual_alloca_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = ALLOCA /\ step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
  dload_table_stack (r::rs) (s::ss) (t::ts) /\ dload_frame_sites r /\
  dload_live_layout lo s.vs_alloca_next t.vs_alloca_next (r::rs) /\
  dload_memory_match lo (r::rs) tn un s t /\
  r.dr_scratch = FDOM t.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  SUM (MAP (\r. CARD r.dr_scratch) (r::rs)) <= ctx_dload_count C ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_table_stack (r1::rs) (s1::ss) (t1::ts) /\ dload_frame_sites r1 /\
    r1.dr_scratch = r.dr_scratch /\
    r1.dr_scratch = FDOM t1.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
    dload_memory_match lo (r1::rs)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 /\
    t1.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `MEM i (fn_insts f) /\ active_inst f i s` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `i.inst_id NOTIN r.dr_scratch` by (simp[] >> metis_tac[]) >>
  drule_all dload_alloca_step_shape >> strip_tac >>
  `?s1. step_inst fuel C i s = OK s1 /\ exec_alloca i s amount = OK s1 /\
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx` by
    (irule dload_alloca_step_fields >> simp[]) >>
  `t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    t1.vs_inst_idx = t.vs_inst_idx` by
    (gvs[exec_alloca_def, update_var_def, AllCaseEqs()]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all dload_singleton_reachable_next_fields >> strip_tac >>
  `active_inst f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  drule_all dload_alloca_successor_headroom >> strip_tac >>
  `r.dr_source = s.vs_allocas /\ r.dr_target = t.vs_allocas` by
    fs[dload_table_stack_cons] >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id`
  >- ( `FLOOKUP t.vs_allocas i.inst_id = NONE` by
         (fs[dload_frame_sites_def, FLOOKUP_DEF] >> ASM_SET_TAC[]) >>
       qexistsl [`s1`,`r with <|dr_source := r.dr_source |+
         (i.inst_id,(s.vs_alloca_next,w2n amount));
         dr_target := r.dr_target |+ (i.inst_id,(t.vs_alloca_next,w2n amount))|>`,
         `i'`,`emitted'`] >> simp[] >>
       conj_tac
       >- (drule_all (SRULE [] (Q.INST [`j` |-> `i`] dload_table_original_fresh)) >> simp[]) >>
       conj_tac
       >- (drule_all dload_frame_original_insert >> simp[]) >>
       conj_tac
       >- (`t1.vs_allocas = t.vs_allocas |+
              (i.inst_id,(t.vs_alloca_next,w2n amount))` by
             (gvs[exec_alloca_def, update_var_def]) >>
           simp[EXTENSION] >> metis_tac[]) >>
       conj_tac
       >- (drule_all dload_alloca_fresh_memory >> simp[]) >>
       drule_all dload_alloca_fresh_post_bound >> simp[]) >>
  PairCases_on `x` >>
  `?c. FLOOKUP t.vs_allocas i.inst_id = SOME (c,x1)` by
    (fs[dload_frame_sites_def] >> metis_tac[]) >>
  qexistsl [`s1`,`r`,`i'`,`emitted'`] >> simp[] >>
  conj_tac
  >- (drule_all (Q.INST [`j` |-> `i`] dload_table_original_repeated) >> simp[]) >>
  conj_tac
  >- (gvs[exec_alloca_def, update_var_def]) >>
  conj_tac
  >- (drule_all dload_alloca_repeated_memory >> simp[]) >>
  gvs[exec_alloca_def, update_var_def, dload_live_layout_def]
QED

(* Premise-origin ledger for this allocation checkpoint:
   - Control supplies source instruction membership and active_inst.  Target
     success supplies the literal operand and singleton output (no source
     success or paired lookup hypothesis is used).
   - The carried table stack identifies runtime tables.  Frame-site coupling
     and the exact scratch-domain identity synchronize fresh/repeated sites;
     membership excludes the original instruction ID from scratch.
   - The fields closure reconstructs source successor reachability before
     dload_alloca_successor_headroom is applied.  Fresh target headroom uses
     that source successor and the aggregate scratch budget; repeated target
     headroom follows from the carried predecessor layout.
   - Table coupling, frame sites, layout, memory matching and scratch-domain
     identity are predecessor invariants, not consequences of source safety.
     The cross-frame live-index/identity producer for the aggregate scratch
     budget remains open.  This theorem does not establish full boundary_core,
     saved layouts, allocation provenance/variable matching or stack closure.
   - Memory matching is returned at the unindexed execution states s1/t1;
     source reachability/control use their actual next instruction indices. *)

Theorem dload_actual_alloca_boundary_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  i.inst_opcode = ALLOCA /\ step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  SUM (MAP (\r. CARD r.dr_scratch) (r::rs)) <= ctx_dload_count C ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    r1.dr_scratch = r.dr_scratch /\
    r1.dr_scratch = FDOM t1.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)} /\
    t1.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  drule dload_boundary_tables >> strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_memory >> strip_tac >>
  `dload_frame_sites r` by fs[dload_live_layout_def] >>
  drule_all dload_actual_alloca_next >> strip_tac >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `i.inst_id NOTIN r.dr_scratch` by (simp[] >> metis_tac[]) >>
  drule_all dload_alloca_step_shape >> strip_tac >>
  `exec_alloca i s amount = OK s1` by
    (qpat_x_assum `step_inst fuel C i s = OK s1` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  `exec_alloca i t amount = OK t1` by
    (qpat_x_assum `step_inst fuel C' i t = OK t1` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  drule_all dload_boundary_core_alloca >>
  disch_then (qx_choose_then `r2` strip_assume_tac) >>
  `r2.dr_scratch = r.dr_scratch` by
    (qpat_x_assum `r2 = _` SUBST1_TAC >>
     Cases_on `FLOOKUP s.vs_allocas i.inst_id = NONE` >> simp[]) >>
  qexistsl [`s1`,`r2`,`i'`,`emitted'`] >> simp[] >>
  conj_tac
  >- (irule dload_boundary_core_index_update >> metis_tac[]) >>
  metis_tac[]
QED

(* Full-boundary successor ledger:
   dload_actual_alloca_boundary_next consumes the same source reachability,
   actual control, target success/activity and source-safety/budget origins as
   dload_actual_alloca_next.  The stronger predecessor boundary supplies the
   table, layout and memory projections previously passed separately.  Original
   instruction membership derives scratch exclusion; no extra exclusion premise
   is exposed.  Paired successful exec_alloca follows from the actual steps and
   the literal/output shape.  The generic core theorem selects its own concrete
   fresh-insert/repeated frame, whose scratch field is unchanged; it is never
   identified with the independent table/memory witness of the earlier theorem.
   The existing index boundary transports this core to the actual successors.
   Saved suffix metadata is preserved inside core.  Additional saved-layout,
   variable-definedness, support and live-index/scratch-budget certificates for
   the full induction remain separate obligations, not source-safety facts. *)

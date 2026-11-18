(* Match the actual successful external effect at a bounded LowerDload fetch. *)
Theory gasFocusLowerDloadExternalSingletonEffect
Ancestors
  gasFocusLowerDloadCutGuards o1SafeUpto gasCount
  lowerDloadSafetyDelegate lowerDloadSafetyCreate lowerDloadOracleCallAssembly
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyAllocBounds
  lowerDloadSafetyKernel lowerDloadDefs lowerDloadFrontier
  lowerDloadSafetyAssemblyPremises lowerDloadPtrRawReachable
  ptrDiscipline o1PassContract codegenRel contextCodegenRel ctxLookupAgree
  lowerDloadSafetyUpdates
  venomExecSemantics venomInst venomWf finite_map list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_external_singleton_effect:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ step_inst fuel C' inst t = OK u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  ?ss H'. step_inst 0 C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem
      ss.vs_memory u.vs_memory /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `ld_global lo A (f::fs)` by fs[] >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs u` by fs[Abbr `q`, gas_cut_def] >>
  `gas_cut n vs t` by metis_tac[ld_step_ok_cut_back] >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ lo <= vs.vs_alloca_next /\
   mem_inv dload_headroom_ok C vs` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> RETURNDATACOPY /\
   inst.inst_opcode <> REVERT` by fs[MEM] >>
  `~in_revert_forward fn s` by
    (`ALL_DISTINCT (fn_labels fn)` by simp[fn_labels_def] >>
     drule_all active_inst_block_lookup >> strip_tac >>
     gvs[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
     metis_tac[]) >>
  suspend "point"
QED

Resume ld_focus_external_singleton_effect[point]:
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule ld_raw_reachable_frontier >> strip_tac >>
  drule raw_reachable_initial_fmp >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `dload_headroom_ok C fn inst s` by metis_tac[ld_sync_source_mem_inv] >>
  `lo <= dyn_floor C vs /\ t.vs_alloca_next <= dyn_floor C vs /\
   t.vs_alloca_next < dimword(:256)` by
    (simp[dyn_floor_def] >> IF_CASES_TAC >>
     gvs[dload_headroom_ok_def, ctx_has_dalloca_def] >> decide_tac) >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!a u v sz. FLOOKUP A a = SOME (u,v,sz) ==> lo <= u /\ lo <= v` by
    metis_tac[ld_alloc_bounds] >>
  `!a k u v z b c sz. FLOOKUP A a = SOME (u,v,z) /\
    FLOOKUP A k = SOME (b,c,sz) /\ a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)` by
    metis_tac[ld_alloc_separate] >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  `!a u v sz. FLOOKUP A a = SOME (u,v,sz) ==>
    u+sz <= dyn_floor C vs /\ v+sz <= dyn_floor C vs /\ v+sz < dimword(:256)` by
    (rpt strip_tac >> drule_all ld_alloc_frontiers >> simp[] >> decide_tac) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by metis_tac[ld_global_selected, MEM] >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  suspend "effect"
QED

Resume ld_focus_external_singleton_effect[effect]:
  `tn.t_var = f.lf_tv` by simp[] >>
  `step_inst_base inst t = OK u` by fs[step_inst_non_invoke] >>
  qpat_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  `?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss u /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss u /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst f.lf_src ss tn).t_mem ss.vs_memory u.vs_memory /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ u.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ u.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ u.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ u.vs_prev_bb = f.lf_tgt.vs_prev_bb` by
    (Cases_on `MEM inst.inst_opcode [CALL;STATICCALL]`
     >- (`inst_wf inst` by
           (fs[fn_inst_wf_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
            metis_tac[]) >>
         (Q.SUBGOAL_THEN
           `?g a v ao az ro rz st.
             (inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
               st = f.lf_tgt.vs_call_ctx.cc_static) \/
             (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;a;ao;az;ro;rz] /\ st = T)`
           (REPEAT_TCL CHOOSE_THEN assume_tac)
          >- (qpat_x_assum `inst_wf inst` mp_tac >>
              qpat_assum `MEM inst.inst_opcode [CALL;STATICCALL]` mp_tac >>
              pure_rewrite_tac[MEM] >> strip_tac >>
              qpat_assum `inst.inst_opcode = _` (fn th =>
                simp[NoAsms, th, inst_wf_def, LENGTH_EQ_NUM_compute]) >>
              disch_tac >> metis_tac[])) >>
         drule_all ld_oracle_call_step >> strip_tac >>
         qexists_tac `ss` >> simp[ld_oracle_call_provenance]) >>
     Cases_on `inst.inst_opcode = DELEGATECALL`
     >- (drule_all ld_delegate_step >> strip_tac >>
         qexists_tac `ss` >> simp[step_prov_def, out_prov_def, ld_erase_set_prov]) >>
     `MEM inst.inst_opcode [CREATE;CREATE2]` by fs[MEM] >>
     drule_all ld_create_step >>
     disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
     qexists_tac `ss` >> simp[]) >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[step_inst_non_invoke] >>
  (conj_tac >- (irule ld_sync_ghost_step >> metis_tac[])) >>
  qpat_assum `FDOM A = _` (once_rewrite_tac o single o GSYM) >>
  rpt strip_tac >>
  metis_tac[ld_set_prov_selected, optionTheory.NOT_NONE_SOME]
QED

Finalise ld_focus_external_singleton_effect

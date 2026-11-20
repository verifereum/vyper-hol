(* Resume a successful LowerDload body after a fresh original ALLOCA. *)
Theory gasFocusLowerDloadFreshAllocaNext
Ancestors
  o1SafeUpto lowerDloadSafetyAllocation lowerDloadSafetyUpdates
  lowerDloadReturnStable lowerDloadReturnAlignment lowerDloadFrontier
  lowerDloadSafetyAdvance lowerDloadSafetyAmbient lowerDloadSafetyLocations
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadOracleCallAssembly
  o1LowerDloadClosure pointerConfinedDefs ptrDiscipline o1PassContract
  codegenRel contextCodegenRel venomWf venomExecSemantics venomInst venomState
  words finite_map pred_set list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_fresh_alloca_body_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  inst.inst_opcode = ALLOCA /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  ir_supply_covers_fn f.lf_supply fn /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ step_inst fuel C' inst t = OK u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  ?sz Ar ss g i Y.
    inst.inst_operands = [Lit sz] /\
    Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
    (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) /\
    step_inst 0 C inst s = OK ss /\ g.lf_fn = fn /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx) /\ ld_image g = ld_image f /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (u with vs_inst_idx := SUC t.vs_inst_idx) Ar (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 Ar (g::fs) /\
    ld_envelope g.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx) /\
    ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0
      (u with vs_inst_idx := SUC t.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb /\
    0 < LENGTH Y /\ get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y) /\
    ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    ss.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `lo <= vs.vs_alloca_next` by fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
  `lo <= s.vs_alloca_next` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_frame_raw_reachable >>
     disch_then (assume_tac o MATCH_MP ld_raw_reachable_frontier) >> decide_tac) >>
  `lo <= t.vs_alloca_next` by (drule ld_sync_frontier >> decide_tac) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
  `?out. inst.inst_outputs = [out]` by
    ((qpat_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> (gvs[inst_wf_def, LENGTH_EQ_NUM_compute]))) >>
  `MEM out (fn_ir_vars fn)` by
    (irule ld_inst_output_ir >> qexists_tac `inst` >> simp[]) >>
  `out IN fn_pv P fn` by
    (mp_tac ptr_roots_subset_fn_pv >>
     simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def] >>
     disch_then irule >> disj1_tac >> disj1_tac >> qexists_tac `inst` >> simp[inst_output_def]) >>
  drule_all ld_sync_original_site_fresh >> strip_tac >>
  mp_tac (ld_fresh_alloca_dispatch |> Q.INST
    [`s` |-> `s`, `t` |-> `t`, `inst` |-> `inst`, `out` |-> `out`,
     `fuel` |-> `fuel`, `C'` |-> `C'`, `ts` |-> `u`]) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sz` (qx_choose_then `ss` strip_assume_tac)) >>
  `step_inst 0 C inst s = OK ss` by simp[ld_alloca_step] >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[SUBSET_DEF] >> rpt strip_tac >> irule ld_global_selected >>
     qexistsl_tac [`f`,`f::fs`,`lo`] >> simp[]) >>
  suspend "successor"
QED

Resume ld_focus_fresh_alloca_body_next[successor]:
  qabbrev_tac `sn = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
   ss.vs_memory = s.vs_memory /\ u.vs_memory = t.vs_memory /\
   ss.vs_gas_readings = s.vs_gas_readings /\ u.vs_gas_readings = t.vs_gas_readings` by
    simp[update_var_def] >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `q.vs_current_bb = t.vs_current_bb /\ q.vs_inst_idx = SUC p` by simp[Abbr `q`] >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists_tac `bb` >> fs[get_instruction_def] >>
     metis_tac[simplifyCfgDefsTheory.lookup_block_member_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i sn /\ ld_envelope f.lf_supply fn sn (SUC s.vs_inst_idx) Y (SUC p) /\
         0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >> simp[ADD1, Abbr `sn`]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i sn` by
    (simp[Abbr `sn`] >> irule frame_reachable_next >>
     goal_assum (drule_at Any) >> simp[is_terminator_def] >>
     conj_tac >- (qexists_tac `0` >> fs[]) >> gvs[]) >>
  `ld_return_cont C fn cs sn` by
    (`~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
     drule_all ld_return_cont_next >> simp[Abbr `sn`]) >>
  suspend "allocation"
QED

Resume ld_focus_fresh_alloca_body_next[allocation]:
  qabbrev_tac `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz))` >>
  qabbrev_tac `H' = f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
  qabbrev_tac `tn' = step_taint inst s ss tn` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` >>
  `step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase Ar o_f H' /\
   ld_vars P Ar (f with <|lf_src := ss; lf_tgt := u; lf_H := H'; lf_tv := tn'.t_var|>) /\
   ld_memory lo Ar tn' ss u /\ ld_nonghost tn' ss u /\ FRANGE H' SUBSET FDOM Ar` by
    (`Ar = A |+ ((f.lf_serial,inst.inst_id),
                  (s.vs_alloca_next,t.vs_alloca_next,w2n sz))` by simp[Abbr `Ar`] >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
     drule_all ld_fresh_alloca_effect >>
     disch_then (qspecl_then [`0`,`PG`,`C'`,`C`] strip_assume_tac) >>
     qpat_x_assum `ss = _` kall_tac >> qpat_x_assum `u = _` kall_tac >>
     gvs[Abbr `H'`, Abbr `tn'`]) >>
  `ld_vars P Ar g` by
    (qpat_assum `ld_vars P Ar _` mp_tac >>
     simp[NoAsms, Abbr `g`, Abbr `sn`, Abbr `q`, ld_vars_def]) >>
  `ld_memory lo Ar tn' sn q /\ ld_nonghost tn' sn q` by
    (gvs[Abbr `sn`, Abbr `q`, ld_memory_def, ld_nonghost_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ld_ghost_ok (dyn_floor C vs) Ar H' (step_prov PG G inst ss)` by
    (`~MEM inst.inst_opcode [PARAM; ADD; SUB; ASSIGN]` by simp[] >>
     drule_then irule ld_ghost_ok_step_fixed >> metis_tac[]) >>
  `ld_dyn_agree (dyn_floor C vs) tn'.t_mem sn.vs_memory q.vs_memory` by
    (simp[NoAsms, Abbr `sn`, Abbr `q`, Abbr `tn'`] >>
     irule ld_dyn_agree_unwritten >> drule ld_sync_dyn_agree >> strip_tac >>
     simp[source_memory_write_ranges_def] >> qexists_tac `t` >> simp[]) >>
  `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
   sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\ q = u with vs_inst_idx := SUC p /\
   g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` by
    simp[Abbr `Ar`, Abbr `sn`, Abbr `q`, Abbr `g`] >>
  `ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y q.vs_inst_idx` by
    (simp[Abbr `sn`] >> metis_tac[Abbr `sn`]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst ss) tn' fn i sn` by simp[Abbr `tn'`] >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' fn i sn q Ar (g::fs) N /\
   ld_global lo Ar (g::fs)` by
    (drule_all (SRULE [PULL_EXISTS] ld_sync_fresh_alloca_update) >>
     qpat_assum `g = _` SUBST1_TAC >>
     qpat_assum `sn = _` SUBST1_TAC >> qpat_assum `q = _` SUBST1_TAC >>
     qpat_assum `Ar = _` SUBST1_TAC >> disch_then ACCEPT_TAC) >>
  suspend "frame"
QED

Resume ld_focus_fresh_alloca_body_next[frame]:
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by
    (rpt strip_tac >> `a <> (f.lf_serial,inst.inst_id)` by metis_tac[] >>
     simp[Abbr `Ar`, FLOOKUP_UPDATE]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\ g.lf_fn = f.lf_fn /\
   g.lf_Q = f.lf_Q /\ g.lf_src = sn /\ g.lf_tgt = q` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms]) >>
  `ld_image g = ld_image f` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms, ld_image_def]) >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 Ar (g::fs)` by
    (qpat_assum `fs0 = fs` SUBST_ALL_TAC >> BETA_TAC >>
     irule (BETA_RULE ld_stable_head_extend) >>
     goal_assum (drule_at (Pat `ld_global lo Ar (g::fs)`)) >>
     qexistsl_tac [`A`,`f`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!h. MEM h fs ==> _ /\ _` drule >> simp[]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by
    (qpat_assum `ld_nonghost tn' ss u`
       (strip_assume_tac o REWRITE_RULE [ld_nonghost_def]) >>
     first_assum ACCEPT_TAC) >>
  `sn.vs_gas_readings = ss.vs_gas_readings /\ q.vs_gas_readings = u.vs_gas_readings /\
   q = u with vs_inst_idx := SUC t.vs_inst_idx /\ tn' = step_taint inst s ss tn` by
    simp[NoAsms, Abbr `sn`, Abbr `q`, Abbr `tn'`] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (qpat_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     PURE_REWRITE_TAC [EVERY_DEF] >> BETA_TAC >>
     map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`g.lf_src = sn`, `g.lf_tgt = q`, `sn.vs_gas_readings = ss.vs_gas_readings`,
        `q.vs_gas_readings = u.vs_gas_readings`] >>
     qpat_assum `ss.vs_gas_readings = u.vs_gas_readings` (SUBST1_TAC o SYM) >>
     qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` SUBST1_TAC >>
     simp[NoAsms]) >>
  qexistsl_tac [`sz`,`ss`,`g`,`i`,`Y`] >>
  map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
    [`tn' = _`, `q = u with vs_inst_idx := SUC p`, `sn = _`, `Ar = _`] >>
  qpat_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 Ar (g::fs)`
    (strip_assume_tac o SRULE [] o BETA_RULE) >>
  qpat_assum `EVERY (\a. _ /\ LENGTH ss.vs_gas_readings <= _) (g::fs)`
    (strip_assume_tac o SRULE []) >>
  `get_instruction bb (SUC p) = SOME (HD Y) /\ active_inst (ld_image g) (HD Y) q /\
   lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb` by
    metis_tac[CONJUNCT1 EL] >>
  `ld_envelope g.lf_supply fn sn (SUC s.vs_inst_idx) Y (SUC p)` by
    (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `g.lf_fn = fn` by metis_tac[] >>
  simp[NoAsms, ld_prefix_zero] >> rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE [])
QED

Finalise ld_focus_fresh_alloca_body_next

(* Concrete return-package preservation for nonallocating ordinary steps. *)
Theory lowerDloadReturnOrdinary
Ancestors
  lowerDloadReturnAlignment lowerDloadOrdinaryEndpoint list venomWf venomInst passSharedDefs o1PassContract venomExecSemantics
  arithmetic contextCodegenRel venomExecProofs lowerDloadSafetyLocations
Libs
  lowerDloadReturnPackageLib

Theorem ld_stable_head_replace:
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  ld_global lo A (g::fs) ==>
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)
Proof
  simp[] >> strip_tac >> gvs[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `!j k. _` (qspecl_then [`j`,`k`] mp_tac) >>
  Cases_on `j` >> Cases_on `k` >> gvs[]
QED

val _ = if null (hyp ld_stable_head_replace) then ()
        else raise Fail "stable head replacement has hypotheses";

(* Singleton witnesses are explicit: ordinary generated scratch instructions
   are not mistaken for source instruction boundaries. *)
Theorem ld_return_point_ordinary_next:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A (f::fs) /\
  fn' = ld_image f /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  ^ld_probe_guard C' k bb t /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DLOAD /\
  inst.inst_opcode <> DLOADBYTES /\ step_inst fuel C' inst t = OK u /\
  ^ld_probe_guard C' j bb (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^ld_probe_point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names bb
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  qabbrev_tac `Guard0 = ^ld_probe_guard C' k bb t` >>
  qabbrev_tac `Guard1 = ^ld_probe_guard C' j bb
    (u with vs_inst_idx := SUC t.vs_inst_idx)` >>
  strip_tac >> qmatch_goalsub_abbrev_tac `Goal` >> fs[] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `active_inst fn inst s /\ t.vs_current_bb = s.vs_current_bb` by
    metis_tac[ld_sync_source, ld_sync_control] >>
  `ir_supply_covers_fn f.lf_supply fn` by
    (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_sync_supply_covered >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY inst_wf (fn_insts fn)` by
    (drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >>
     simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_def,
          MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[fn_insts_blocks_MEM]) >>
  `lower_dload_function_supply f.lf_supply fn =
    (fn', SND (lower_dload_function_supply f.lf_supply fn))` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `~in_revert_forward fn s` by
    (irule (Q.INST [`h` |-> `0`, `X` |-> `[inst]`] ld_guarded_source_non_revert) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
     j IN P f.lf_fn.fn_name) (f::fs)` by simp[] >>
  drule_all ld_ordinary_endpoint >> strip_tac >>
  `^ld_probe_stable lo P Sigma names fs f0 A0 A (g::fs)` by
    (irule ld_stable_head_replace >> conj_tac >- simp[] >>
     qexists_tac `f` >> simp[] >> metis_tac[]) >>
  `ld_return_cont C fn cs g.lf_src` by
    (fs[] >> irule ld_return_cont_next >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb` by
    (drule_all ld_sync_ordinary_effect >> strip_tac >>
     gvs[step_inst_non_invoke]) >>
  `?ti. get_instruction bb (SUC t.vs_inst_idx) = SOME ti` by
    (mp_tac (Q.INST [`C` |-> `C'`, `k` |-> `j`,
         `t` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`]
       ld_successful_body_fetch) >> fs[ADD1] >> metis_tac[]) >>
  `?next Y. active_inst fn next (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
     ld_envelope f.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
       (SUC s.vs_inst_idx) Y (p+1)` by
    (irule (SRULE [] (Q.INST [`X` |-> `[inst]`,
       `q` |-> `u with vs_inst_idx := SUC t.vs_inst_idx`]
       ld_envelope_successor_location)) >>
     goal_assum (drule_at Any) >> simp[] >> fs[ADD1] >> metis_tac[pairTheory.FST]) >>
  `active_inst fn next g.lf_src` by fs[] >>
  `ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
     (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt A (g::fs) N` by
    metis_tac[] >>
  `active_inst fn' ti g.lf_tgt` by
    (simp[active_inst_def] >> qexists_tac `bb` >> fs[get_instruction_def, ADD1] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `0 < LENGTH Y /\ ti = EL 0 Y` by
    (irule ld_envelope_active_head >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `g.lf_tgt` >> fs[ADD1] >> metis_tac[pairTheory.FST]) >>
  simp[Abbr `Goal`] >>
  qexistsl_tac [`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,
    `next`,`g.lf_src`,`g.lf_tgt`,`A`,`g::fs`,`N`,`Y`,`p+1`,`0`] >>
  simp[lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
  fs[ADD1] >> metis_tac[ld_image_def]
QED

val _ = if null (hyp ld_return_point_ordinary_next) then ()
        else raise Fail "ordinary return point has hypotheses";

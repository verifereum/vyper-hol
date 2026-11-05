(* Actual fresh/cached private allocation ownership. *)
Theory lowerDloadScratchOwnership
Ancestors
  lowerDloadAllocationOrigins lowerDloadSafetyRelation lowerDloadScratchIdentity
  venomExecSemantics venomState finite_map words list pred_set

Theorem ld_scratch_alloca_ownership:
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ALL_DISTINCT (fn_ir_inst_ids f.lf_fn) /\ ld_private f d ai /\
  (!j. j < LENGTH (f::fs) ==>
    (EL j (f::fs)).lf_tgt.vs_alloca_next =
    (EL j (f::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (f::fs))) /\
  ld_global lo A (f::fs) /\ ld_maps A f /\
  ld_intervals lo f.lf_tgt /\ lo <= f.lf_src.vs_alloca_next /\
  lo <= f.lf_tgt.vs_alloca_next /\
  FLOOKUP f.lf_src.vs_allocas ai = NONE /\
  inst.inst_id = ai /\ inst.inst_outputs = [a] /\
  exec_alloca inst f.lf_tgt (32w:bytes32) = OK u /\
  g = f with <|lf_tgt := u; lf_E := d INSERT f.lf_E|> ==>
  (ld_global lo A (g::fs) /\
  ld_slots A (g::fs) = ld_slots A (f::fs) /\
  ld_intervals lo u /\
  (?c. FLOOKUP u.vs_allocas ai = SOME (c,32) /\ lo <= c /\
    c+32 <= u.vs_alloca_next /\ FLOOKUP u.vs_vars a = SOME (n2w c)) /\
  u.vs_alloca_next = f.lf_tgt.vs_alloca_next +
    (if FLOOKUP f.lf_tgt.vs_allocas ai = NONE then 32 else 0)) /\
  ld_maps A g /\
  ld_charge (g::fs) = ld_charge (f::fs) + (if d IN f.lf_E then 0 else 1) /\
  u.vs_alloca_next = f.lf_tgt.vs_alloca_next + 32 * (if d IN f.lf_E then 0 else 1) /\
  (!j. j < LENGTH (g::fs) ==>
    (EL j (g::fs)).lf_tgt.vs_alloca_next =
    (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs)))
Proof
  strip_tac >> conj_asm1_tac >- (

  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `ld_intervals lo u` by
    (irule (INST_TYPE [alpha |-> ``:256``] ld_intervals_exec_alloca) >>
    qexistsl_tac [`inst`, `f.lf_tgt`, `32w:bytes32`] >> simp[]) >>
  `ld_slots A (g::fs) = ld_slots A (f::fs)` by
    (irule ld_slots_head_cong >> simp[]) >>
  Cases_on `FLOOKUP f.lf_tgt.vs_allocas ai`
  >- (gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      conj_tac >- (irule ld_global_insert_private >>
        qexistsl_tac [`inst.inst_id`, `f`, `32`] >> simp[]) >>
      simp[FLOOKUP_UPDATE]) >>
  PairCases_on `x` >>
  `x1 = 32` by (drule_all ld_maps_target >> simp[]) >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  conj_tac >- (irule ld_global_head_cong >> qexists_tac `f` >> simp[]) >>
  simp[FLOOKUP_UPDATE] >>
  gvs[ld_intervals_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `ld_maps A g` by
    (gvs[] >> irule ld_maps_scratch >> simp[] >>
     qexists_tac `inst` >> simp[] >>
     metis_tac[ld_private_functional]) >>
  `ld_charge (g::fs) = ld_charge (f::fs) + (if d IN f.lf_E then 0 else 1)` by
    (qpat_assum `ld_maps A f` (mp_then Any mp_tac ld_charge_scratch) >>
     disch_then (qspecl_then [`u`,`fs`,`d`] mp_tac) >> simp[]) >>
  `u.vs_alloca_next = f.lf_tgt.vs_alloca_next + 32 * (if d IN f.lf_E then 0 else 1)` by
    (drule_all ld_private_cache >> strip_tac >>
     Cases_on `d IN f.lf_E` >> gvs[]) >>
  qpat_assum `ld_maps A f` (mp_then Any mp_tac ld_frontiers_scratch) >>
  disch_then (qspecl_then [`u`,`fs`,`d`] mp_tac) >>
  simp[]
QED

val _ = if null (hyp ld_scratch_alloca_ownership) then () else
  raise Fail "scratch ownership theorem has hypotheses";

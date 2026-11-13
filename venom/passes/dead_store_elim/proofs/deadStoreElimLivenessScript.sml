Theory deadStoreElimLiveness
Ancestors
  deadStoreElimDefs cfgDefs venomInst venomWf list rich_list
  relation venomExecProofs analysisSimProofsBase basePtrDefs memLocDefs
  venomExecSemantics venomEffects cfgAnalysisProps cfgHelpers

(* No read of an outstanding store footprint from this program point until
   a complete overwrite. Reads at the current index precede its clobber. *)
Definition dse_suffix_dead_def:
  dse_suffix_dead cfg aliases bp loc space fn bb idx <=>
    (!j. idx <= j /\ j < LENGTH bb.bb_instructions /\
         (!k. idx <= k /\ k < j ==>
              ~dse_inst_clobbers bp space loc (EL k bb.bb_instructions)) ==>
         ~dse_inst_reads_alias aliases bp space loc
            (EL j bb.bb_instructions)) /\
    ((!k. idx <= k /\ k < LENGTH bb.bb_instructions ==>
          ~dse_inst_clobbers bp space loc (EL k bb.bb_instructions)) ==>
     !succ target. MEM succ (cfg_succs_of cfg bb.bb_label) /\
       RTC (\a b. MEM b (cfg_succs_of cfg a) /\
            block_no_full_clobber bp space loc fn a) succ target ==>
       ~block_has_unclobbered_read aliases bp space loc fn target)
End

Theorem dse_suffix_dead_after_store:
  dse_suffix_dead cfg aliases bp loc space fn bb (SUC idx) <=>
  ~dse_mem_def_live cfg aliases bp loc space fn bb idx
Proof
  `!j. SUC idx <= j <=> idx < j` by decide_tac >>
  simp[dse_suffix_dead_def, dse_mem_def_live_def,
       arithmeticTheory.GREATER_DEF] >>
  metis_tac[]
QED

Theorem dse_suffix_dead_no_read:
  dse_suffix_dead cfg aliases bp loc space fn bb idx /\
  idx < LENGTH bb.bb_instructions ==>
  ~dse_inst_reads_alias aliases bp space loc (EL idx bb.bb_instructions)
Proof
  simp[dse_suffix_dead_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `idx` mp_tac) >> simp[]
QED

Theorem dse_suffix_dead_step:
  dse_suffix_dead cfg aliases bp loc space fn bb idx /\
  ~dse_inst_clobbers bp space loc (EL idx bb.bb_instructions) ==>
  dse_suffix_dead cfg aliases bp loc space fn bb (SUC idx)
Proof
  rewrite_tac[dse_suffix_dead_def] >> strip_tac >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!j. _ ==> ~dse_inst_reads_alias _ _ _ _ _`
        (qspec_then `j` mp_tac) >>
      impl_tac >- (simp[] >> rpt strip_tac >>
        Cases_on `k = idx` >> gvs[]) >> simp[]) >>
  strip_tac >>
  `!k. idx <= k /\ k < LENGTH bb.bb_instructions ==>
       ~dse_inst_clobbers bp space loc (EL k bb.bb_instructions)` by
    (rpt strip_tac >> Cases_on `k = idx` >> gvs[]) >>
  qpat_x_assum `(_ ==> !succ target. _)` mp_tac >> simp[]
QED

Definition dse_label_dead_def:
  dse_label_dead cfg aliases bp loc space fn lbl <=>
    !target. RTC (\a b. MEM b (cfg_succs_of cfg a) /\
                  block_no_full_clobber bp space loc fn a) lbl target ==>
      ~block_has_unclobbered_read aliases bp space loc fn target
End

Theorem block_no_full_clobber_from_instructions:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY (\inst. ~dse_inst_clobbers bp space loc inst) bb.bb_instructions ==>
  block_no_full_clobber bp space loc fn bb.bb_label
Proof
  rpt strip_tac >> simp[block_no_full_clobber_def] >> rpt strip_tac >>
  `bb' = bb` by (irule same_label_same_block >> metis_tac[]) >> gvs[]
QED

Theorem dse_label_dead_step:
  dse_label_dead cfg aliases bp loc space fn lbl /\
  MEM succ (cfg_succs_of cfg lbl) /\
  block_no_full_clobber bp space loc fn lbl ==>
  dse_label_dead cfg aliases bp loc space fn succ
Proof
  simp[dse_label_dead_def] >> rpt strip_tac >>
  `RTC (\a b. MEM b (cfg_succs_of cfg a) /\
       block_no_full_clobber bp space loc fn a) lbl target` by
    (irule (cj 2 RTC_RULES) >> qexists_tac `succ` >> simp[]) >>
  metis_tac[]
QED

Theorem dse_label_dead_suffix:
  dse_label_dead cfg aliases bp loc space fn bb.bb_label /\
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  dse_suffix_dead cfg aliases bp loc space fn bb 0
Proof
  rpt strip_tac >> rewrite_tac[dse_suffix_dead_def] >> conj_tac
  >- (gen_tac >> strip_tac >> strip_tac >>
      `block_has_unclobbered_read aliases bp space loc fn bb.bb_label` by
        (simp[block_has_unclobbered_read_def] >>
         qexistsl_tac [`bb`, `j`] >> simp[]) >>
      fs[dse_label_dead_def] >> metis_tac[RTC_REFL]) >>
  strip_tac >>
  `block_no_full_clobber bp space loc fn bb.bb_label` by
    (irule block_no_full_clobber_from_instructions >>
     simp[EVERY_EL]) >>
  rpt gen_tac >> strip_tac >>
  drule_all dse_label_dead_step >>
  simp[dse_label_dead_def] >> metis_tac[]
QED

Theorem dse_suffix_dead_successor:
  dse_suffix_dead cfg aliases bp loc space fn bb idx /\
  LENGTH bb.bb_instructions <= idx /\
  MEM succ (cfg_succs_of cfg bb.bb_label) ==>
  dse_label_dead cfg aliases bp loc space fn succ
Proof
  simp[dse_suffix_dead_def, dse_label_dead_def] >>
  rpt strip_tac >>
  qpat_x_assum `(_ ==> !succ target. _)` mp_tac >>
  simp[] >> metis_tac[]
QED

Theorem dse_suffix_dead_advance:
  !count idx.
    dse_suffix_dead cfg aliases bp loc space fn bb idx /\
    (!k. idx <= k /\ k < idx + count ==>
         ~dse_inst_clobbers bp space loc (EL k bb.bb_instructions)) ==>
    dse_suffix_dead cfg aliases bp loc space fn bb (idx + count)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
  irule dse_suffix_dead_step >> conj_tac
  >- (qpat_x_assum `!k. _ ==> ~dse_inst_clobbers _ _ _ _` irule >>
      decide_tac) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem dse_phi_no_clobber:
  inst.inst_opcode = PHI /\ loc.ml_size <> SOME 0 ==>
  ~dse_inst_clobbers bp space loc inst
Proof
  strip_tac >> Cases_on `space` >>
  simp[dse_inst_clobbers_def, bp_get_write_location_def,
       is_raw_fmp_opcode_def, write_effects_def, empty_effects_def,
       ml_is_fixed_def, completely_contains_def, ml_empty_def] >>
  Cases_on `loc.ml_offset` >> Cases_on `loc.ml_size` >> gvs[]
QED

Theorem dse_suffix_dead_phi_prefix:
  dse_suffix_dead cfg aliases bp loc space fn bb 0 /\
  loc.ml_size <> SOME 0 ==>
  dse_suffix_dead cfg aliases bp loc space fn bb
    (phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >>
  qspec_then `bb.bb_instructions` assume_tac phi_prefix_all_phi >>
  qspec_then `phi_prefix_length bb.bb_instructions` mp_tac
    dse_suffix_dead_advance >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_then irule >>
  gen_tac >> strip_tac >> irule dse_phi_no_clobber >> simp[] >>
  fs[EVERY_EL] >>
  first_x_assum (qspec_then `k` mp_tac) >>
  simp[EL_TAKE, LENGTH_TAKE, phi_prefix_length_le]
QED

Theorem dse_exec_block_successor:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  s.vs_inst_idx <= LENGTH bb.bb_instructions /\
  exec_block fuel ctx bb s = OK s1 ==>
  MEM s1.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)
Proof
  rpt strip_tac >>
  drule_all wf_function_bb_well_formed >>
  simp[bb_well_formed_def] >> strip_tac >>
  `cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb` by
    (rewrite_tac[cfg_analyze_succs] >>
     irule cfg_succs_of_build_succs >>
     fs[wf_function_def, fn_labels_def]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
    (rpt strip_tac >>
     `i < LENGTH bb.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
     decide_tac) >>
  drule_all exec_block_current_bb_in_succs >> simp[]
QED

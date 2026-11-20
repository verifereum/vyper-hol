Theory asmRelocDataEnv
Ancestors fnPlanPlaceRevertPostamble asmDataEnv asmSymOwnStep asmSymBridge
  asmWf asmSymSem symbolResolve codegenEncodingWf finite_map list pred_set

Theorem lo_reloc_data_env:
  asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst q = FILTER is_data_inst p ==>
  (!l. MEM (AsmDataHeader l) p ==> l IN FDOM (asm_data_env q code)) /\
  asm_data_env_lo_ok (lo_reloc p q) p (asm_data_env q code) code
Proof
  strip_tac >>
  `!l. MEM (AsmDataHeader l) p ==> MEM (AsmDataHeader l) q` by
    (rpt strip_tac >>
     `MEM (AsmDataHeader l) (FILTER is_data_inst p)` by
       simp[MEM_FILTER, is_data_inst_def] >>
     metis_tac[MEM_FILTER]) >>
  conj_tac >- metis_tac[asm_data_env_header_fdom] >>
  `asm_data_env_lo_ok (SND (compute_label_offsets q)) q
       (asm_data_env q code) code` by
    simp[asm_data_env_lo_ok_canonical, asm_data_env_ok_asm_data_env] >>
  fs[asm_data_env_lo_ok_def] >> rpt strip_tac >>
  `~MEM (AsmLabel l) p` by metis_tac[asm_static_wf_def] >>
  simp[lo_reloc_def, FLOOKUP_FUNION, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

(* The binding domain records declarations, not their current byte offsets. *)
Theorem compute_label_offsets_domain:
  !p. FDOM (SND (compute_label_offsets p)) =
      {l | MEM (AsmLabel l) p \/ MEM (AsmDataHeader l) p}
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- simp[compute_label_offsets_def, EXTENSION] >>
  gen_tac >> disch_tac >> qx_gen_tac `a` >> Cases_on `a` >>
  simp[compute_label_offsets_snoc, MEM_SNOC, EXTENSION] >> metis_tac[]
QED

Theorem lo_reloc_domain_contains:
  FILTER is_data_inst q = FILTER is_data_inst p ==>
  FDOM (SND (compute_label_offsets p)) SUBSET FDOM (lo_reloc p q)
Proof
  strip_tac >>
  `!l. MEM (AsmDataHeader l) q <=> MEM (AsmDataHeader l) p` by
    (gen_tac >>
     `MEM (AsmDataHeader l) (FILTER is_data_inst q) <=>
      MEM (AsmDataHeader l) (FILTER is_data_inst p)` by simp[] >>
     fs[MEM_FILTER, is_data_inst_def]) >>
  simp[lo_reloc_def, FDOM_DRESTRICT, compute_label_offsets_domain, SUBSET_DEF] >>
  gen_tac >> Cases_on `MEM (AsmLabel x) p` >> simp[]
QED

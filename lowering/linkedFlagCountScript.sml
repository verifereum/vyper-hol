(* Checked flag counts for the compiler's qualified flag keys. *)
Theory linkedFlagCount
Ancestors
  linkedNsidProps abiDecoderCallerFlags vyperTypeConstantFold
  vyperTypeContractStaticMaps vyperTypeContract compileUnit vyperContext
  vyperAST finite_map alist list pair

Triviality flag_info_src_count:
  !tops src fmid fnm key n.
    (!name members. MEM (FlagDecl name members) tops /\
      nsid_to_string (src,name) = key ==> LENGTH members = n) ==>
    SND (build_flag_info_src src tops fmid fnm) key =
      if (?name members. MEM (FlagDecl name members) tops /\
            nsid_to_string (src,name) = key) then n else fnm key
Proof
  Induct >- simp[build_flag_info_src_def] >>
  gen_tac >> Cases_on `h` >> simp[build_flag_info_src_def] >>
  rpt gen_tac >> strip_tac
  >~ [`build_flag_member_id_one _ _`]
  >- (qmatch_goalsub_abbrev_tac
        `build_flag_info_src src tops next_id next_count` >>
      qpat_assum `!src fmid fnm key n. _`
        (qspecl_then [`src`,`next_id`,`next_count`,`key`,`n`] mp_tac) >>
      impl_tac >-
        (rpt strip_tac >> first_x_assum irule >>
         qexists_tac `name` >> simp[]) >>
      disch_then SUBST1_TAC >>
      simp[Abbr `next_count`, LEFT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS] >>
      Cases_on `nsid_to_string (src,s) = key` >> simp[]
      >- (`LENGTH l = n` by
            (first_x_assum irule >> qexists_tac `s` >> simp[]) >>
          simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Triviality flag_info_mods_count:
  !mods fmid fnm key n.
    (!src tops name members. MEM (src,tops) mods /\
      MEM (FlagDecl name members) tops /\
      nsid_to_string (src,name) = key ==> LENGTH members = n) ==>
    SND (build_flag_info_mods mods fmid fnm) key =
      if (?src tops name members. MEM (src,tops) mods /\
            MEM (FlagDecl name members) tops /\
            nsid_to_string (src,name) = key) then n else fnm key
Proof
  Induct >> simp[build_flag_info_mods_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `info = build_flag_info_src h0 h1 fmid fnm` >>
  PairCases_on `info` >>
  `SND (build_flag_info_src h0 h1 fmid fnm) key =
    if (?name members. MEM (FlagDecl name members) h1 /\
          nsid_to_string (h0,name) = key) then n else fnm key` by
    (irule flag_info_src_count >> metis_tac[MEM]) >>
  simp[build_flag_info_mods_def, GSYM markerTheory.Abbrev_def] >>
  qpat_assum `!fmid fnm key n. _`
    (qspecl_then [`info0`,`info1`,`key`,`n`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_assum `!src ts name members. _`
        (qspecl_then [`src`,`tops`,`name`,`members`] mp_tac) >>
      simp[]) >>
  disch_then SUBST1_TAC >>
  `info1 key = if (?name members. MEM (FlagDecl name members) h1 /\
          nsid_to_string (h0,name) = key) then n else fnm key` by
    (Cases_on `build_flag_info_src h0 h1 fmid fnm` >>
     fs[markerTheory.Abbrev_def]) >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS] >>
  Cases_on `?name members. MEM (FlagDecl name members) h1 /\
      nsid_to_string (h0,name) = key` >> simp[]
QED

Theorem linked_flag_member_count:
  contract_namespaces_ok dep mods /\
  FLOOKUP (type_env_all_modules mods) nsid = SOME (FlagArgs n) ==>
  SND (build_flag_info_mods mods (K (K 0)) (K 0)) (nsid_to_string nsid) = n
Proof
  strip_tac >>
  `contract_namespaces_ok F mods` by
    (Cases_on `dep` >> fs[contract_namespaces_ok_deploy_implies_runtime]) >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  `!src tops name members. MEM (src,tops) mods /\
      MEM (FlagDecl name members) tops ==> ~MEM #"." name` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `contract_namespaces_ok F mods`
       (strip_assume_tac o REWRITE_RULE [contract_namespaces_ok_def]) >>
     qpat_x_assum `EVERY (\(s,ts). EVERY _ ts) mods` mp_tac >>
     simp[Once EVERY_MEM] >>
     disch_then (qspec_then `(src,tops)` mp_tac) >> simp[] >>
     simp[Once EVERY_MEM] >>
     disch_then (qspec_then `FlagDecl name members` mp_tac) >> simp[]) >>
  PairCases_on `nsid` >>
  `?ts members. ALOOKUP mods nsid0 = SOME ts /\
      MEM (FlagDecl nsid1 members) ts /\ LENGTH members = n` by
    (Cases_on `ALOOKUP mods nsid0` >> fs[FLOOKUP_type_env_all_modules] >>
     drule type_env_flag_declaration >> metis_tac[]) >>
  `MEM (nsid0,ts) mods` by (drule_then ACCEPT_TAC ALOOKUP_MEM) >>
  `!s ts' name members'. MEM (s,ts') mods /\
      MEM (FlagDecl name members') ts' /\
      nsid_to_string (s,name) = nsid_to_string (nsid0,nsid1) ==>
      LENGTH members' = n` by
    (rpt strip_tac >>
     `(s,name) = (nsid0,nsid1)` by
       (irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
     `ALOOKUP mods s = SOME ts'` by
       (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
     drule_all flag_decl_type_env_all_modules >> fs[]) >>
  drule flag_info_mods_count >>
  disch_then (qspecl_then [`K (K 0)`,`K 0`] SUBST1_TAC) >>
  simp[] >> metis_tac[]
QED

Theory lowerDloadNormalLive
Ancestors
  lowerDloadNormalData lowerDloadOwnership lowerDloadLifetime
  lowerDloadRelocation pred_set finite_map

Theorem ld_normal_data_live_restrict:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  survivors SUBSET live /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN survivors) ==>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk survivors keys d A suspended gstk f
Proof
  strip_tac >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
     owner IN survivors` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[ld_live_def,ld_selected_def] >> metis_tac[]) >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E survivors a b)
     tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t)` by
    (irule ld_byte_rel_restrict >>
     drule ld_normal_data_memory >> disch_then (irule_at Any) >>
     fs[ld_site_bytes_def,SUBSET_DEF] >> metis_tac[]) >>
  gvs[ld_normal_data_def,SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_normal_data_serial_delete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s ==>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk (live DELETE (0,k)) keys d A suspended gstk f
Proof
  strip_tac >> irule ld_normal_data_live_restrict >>
  reverse conj_tac >- (qexists_tac `live` >> simp[]) >>
  rpt strip_tac >>
  drule_all ld_annotated_serial >> simp[] >> strip_tac >>
  `owner <> (0,k)` by (strip_tac >> gvs[]) >>
  simp[] >> drule ld_normal_data_geometry >> strip_tac >>
  metis_tac[]
QED

Theorem ld_normal_data_serial_support:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_live astk L AP AG (owner,(bs,sz)) ==>
  owner IN live DELETE (0,k)
Proof
  strip_tac >> drule_all ld_normal_data_serial_delete >>
  disch_then (mp_then Any strip_assume_tac ld_normal_data_geometry) >>
  metis_tac[]
QED

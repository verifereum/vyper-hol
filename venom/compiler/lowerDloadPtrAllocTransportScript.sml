Theory lowerDloadPtrAllocTransport
Ancestors
  lowerDloadPtrAlloc lowerDloadPtrCall lowerDloadPtrTaint lowerDloadPtrAggregate
  lowerDloadPtrRel finite_map list pred_set words

Theorem dload_live_site_original_insert:
  FLOOKUP f.dr_source id = NONE /\ FLOOKUP f.dr_target id = NONE /\
  dload_live_site (f::fs) owner q x y m ==>
  dload_live_site
    ((f with <|dr_source := f.dr_source |+ (id,(b,n));
               dr_target := f.dr_target |+ (id,(c,n))|>)::fs) owner q x y m
Proof
  Cases_on `owner` >> simp[dload_live_site_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem dload_pointer_word_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_pointer_word fs p q x y ==>
  dload_pointer_word gs p q x y
Proof
  PairCases_on `p` >> PairCases_on `q` >>
  simp[dload_pointer_word_def] >> metis_tac[]
QED

Theorem dload_value_word_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_value_word fs mask p q x y ==>
  dload_value_word gs mask p q x y
Proof
  Cases_on `p` >> Cases_on `q` >>
  simp[dload_value_word_def] >> metis_tac[dload_pointer_word_sites_mono]
QED

Theorem dload_vars_match_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_vars_match fs V G H tn un s t ==>
  dload_vars_match gs V G H tn un s t
Proof
  simp[dload_vars_match_def] >> rpt strip_tac >>
  metis_tac[dload_value_word_sites_mono]
QED

Theorem dload_param_values_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_param_values fs PG PH xs ys ==>
  dload_param_values gs PG PH xs ys
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN, EL_GENLIST] >>
  rpt strip_tac >> gvs[] >> metis_tac[dload_value_word_sites_mono]
QED

Theorem dload_saved_metadata_head_replace:
  (!k. k < LENGTH cs ==>
    dload_saved_metadata (DROP (SUC k) (f::fs)) (EL k Ws) (EL k cs) (EL k ds)) <=>
  (!k. k < LENGTH cs ==>
    dload_saved_metadata (DROP (SUC k) (g::fs)) (EL k Ws) (EL k cs) (EL k ds))
Proof
  simp[]
QED

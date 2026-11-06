(* Frame one immutable binding, rather than the whole immutable store. *)
Theory whitelistForIterImmFrame
Ancestors
  vyperBareGlobalName vyperPlaceFrames vyperState vyperTypeSystem
  vyperTypeInvariants vyperInterpreter vyperAST list finite_map alist

Theorem lookup_immutable_set_other:
  (src',name') <> (src,name) /\
  set_immutable cx src' name' tv v es = (r,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[lookup_immutable_def] >>
  Cases_on `src' = src` >>
  gvs[set_source_immutables_def, get_source_immutables_def, FLOOKUP_UPDATE,
      ALOOKUP_ADELKEY]
QED

Theorem lookup_immutable_write_other:
  write_place cx p v es = (r,es') /\
  (!src' name' path. p = ImmutablePlace src' name' path ==>
                      (src',name') <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p`
  >- (strip_tac >> drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (strip_tac >> drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  rename1 `write_place cx (ImmutablePlace other_src other_name path)` >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables other_src imms) other_name` >>
  simp[return_def, raise_def] >>
  rename1 `FLOOKUP _ _ = SOME tva` >>
  Cases_on `assign_subscripts (FST tva) (SND tva) path (Replace v)` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> irule lookup_immutable_set_other >>
  goal_assum (drule_at Any) >> simp[]
QED

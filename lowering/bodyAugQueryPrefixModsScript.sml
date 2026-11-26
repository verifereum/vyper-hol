(* The successful AugAssign queries leave the source state at the RHS entry. *)
Theory bodyAugQueryPrefixMods
Ancestors
  gasOutcomeFullMods gasExemptCertMods gasStorage vyperState vyperInterpreter
  exprSimMemorySource exprSimIfExpWidenedAdapter

Theorem augassign_read_type_prefix_mods:
  read_place cx p st = (INL cur,st) /\
  place_type_value cx p st = (INL ptv,st) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (k cur ptv) (st,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (read_place cx p) (\v. bind (place_type_value cx p) (k v)))
    (st,s,G,tn) Q R
Proof
  strip_tac >>
  `read_result cx (PlaceR p) st = (INL cur,st)` by simp[read_result_def] >>
  `!gs. read_place cx p (st with gas_obs := gs) =
        (INL cur,st with gas_obs := gs)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[read_result_def]) >>
  drule_then assume_tac exprSimIfExpWidenedAdapterTheory.place_type_value_gas_obs >>
  `!gs. bind (read_place cx p) (\v. bind (place_type_value cx p) (k v))
          (st with gas_obs := gs) = k cur ptv (st with gas_obs := gs)` by
    simp[bind_def] >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` mp_tac >>
  rw[gas_outcome_full_mods_def, gas_bad_storage_at_def] >>
  qexists_tac `marks`
  >- (disj1_tac >> simp[] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac
  >- (irule gas_exempt_cert_mods_source_cong >>
      qexists_tac `ignore_bind (k cur ptv) (return ())` >>
      simp[ignore_bind_def, bind_def]) >>
  qexists_tac `H` >> simp[]
QED

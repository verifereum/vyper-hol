Theory linkedDefaultOutcomeSource
Ancestors
  gasOutcomeFullMods gasStorage gasExemptCertMods fragGasOriginPtr vyperState pair sum

Theorem gas_outcome_full_source_map_mods:
  (!es. source' es = (f (FST (source es)), SND (source es))) /\
  (!ex. f (INR ex) = INR ex) /\ (!v. ISL (f (INL v))) /\
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source'
    (es, s, G, tn)
    (\H raw ee G tn t. ?res. raw = f res /\ Q H res ee G tn t)
    (\H raw ee gt r. ?res. raw = f res /\ R H res ee gt r)
Proof
  strip_tac >>
  `ignore_bind source' (return ()) = ignore_bind source (return ())` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `source x` >> rename1 `source x = (res0, st1)` >>
     Cases_on `res0` >> simp[] >>
     rename1 `f (INL v)` >>
     `ISL (f (INL v))` by simp[] >> Cases_on `f (INL v)` >> fs[]) >>
  `!x. SND (source' x) = SND (source x)` by simp[] >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  asm_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`f res`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
      rpt strip_tac >> res_tac >> simp[] >> metis_tac[])
  >> disj2_tac >> disj2_tac >> metis_tac[]
QED

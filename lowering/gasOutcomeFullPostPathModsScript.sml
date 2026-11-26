(* Refine a normal post using the path of the same counted outcome. *)
Theory gasOutcomeFullPostPathMods
Ancestors gasOutcomeFullMods fragGasOriginPtr fragExec

Theorem gas_outcome_full_mods_post_path:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!marks H res ee G' tn' t.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK t,G',tn') /\ Q H res ee G' tn' t ==>
    Q' H res ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qhdtm_x_assum `gas_outcome_full_mods`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

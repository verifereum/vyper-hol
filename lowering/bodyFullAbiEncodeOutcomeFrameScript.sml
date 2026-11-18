(* Preserve the labels of the very same physical outcome witness. *)
Theory bodyFullAbiEncodeOutcomeFrame
Ancestors
  gasOutcomeFull fragGasPathFrameMem fragGasOriginPtr fragGasOrigin
  fragGasMode

Theorem abi_encode_outcome_labels:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\
                         t.vs_labels = s.vs_labels) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      rpt conj_tac >- fs[] >- fs[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> simp[] >>
          metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                    gas_marked_path_exec, gas_path_code_labels]) >>
      disj2_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

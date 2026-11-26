Theory bodyShaUniformRunMods
Ancestors
  fragGasSeqPtr ptrSafeRun vyperStorageFootprint

(* The machine result and pointer endpoint do not depend on the horizon. *)
Theorem sha_uniform_run_mods:
  valid_horizon cx st0 H0 obs /\
  (!H. valid_horizon cx st0 H obs ==>
       ?r g t. run_inst_seq code s = r /\
               inst_seq_ptr (DF H) lo ctx fn PG G tn code s g t /\
               P H r g t) ==>
  ?r g t. run_inst_seq code s = r /\
          !H. valid_horizon cx st0 H obs ==>
              inst_seq_ptr (DF H) lo ctx fn PG G tn code s g t /\
              P H r g t
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choose_then `r` (qx_choose_then `g`
    (qx_choose_then `t` strip_assume_tac))) >>
  qexistsl_tac [`r`, `g`, `t`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choose_then `r'` (qx_choose_then `g'`
    (qx_choose_then `t'` strip_assume_tac))) >>
  `g' = g /\ t' = t` by
    (irule inst_seq_ptr_ghost_unique >>
     qpat_assum `inst_seq_ptr (DF H) _ _ _ _ _ _ _ _ g' t'` (irule_at Any) >>
     qpat_assum `inst_seq_ptr (DF H0) _ _ _ _ _ _ _ _ g t` (irule_at Any)) >>
  gvs[]
QED

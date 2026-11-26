(* Transport a successful local MemoryPlace write through the linked gas outcome.
   The caller supplies the actual scope update and its normal installation post;
   this leaf only lifts that endpoint over all gas-observation tails. *)
Theory bodyAssignLocalWriteInstallOutcomeMods
Ancestors
  gasOutcomeFullMods gasOutcomeFullPostMods gasOutcomeFullBindMods
  bodyFullPostsMods bodyFullShared vyperStorageTrace vyperState
  fragGasOriginPtr fragExec loweringPosts venomState

Theorem assign_local_write_install_outcome_mods:
  ~z.vs_halted /\
  (!tail. write_place cx (MemoryPlace id path)
      (v) (ee with gas_obs := tail) =
      (INL (),ff with gas_obs := tail)) /\
  ff.storage_trace = ee.storage_trace /\ ff.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ff.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
       (z,Gz,tz) [] (OK t,Gf,tf) /\
     N H (INL ()) (ff with gas_obs := []) Gf tf t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v)
    (ee,z,Gz,tz) N X
Proof
  strip_tac >> irule gas_outcome_full_mods_pure >> conj_tac
  >- (qexistsl [`Gf`,`ff`,`INL ()`,`t`,`tf`] >> conj_tac
      >- (qpat_assum `!tail. write_place _ _ _ _ = _` ACCEPT_TAC)
      >- (rpt gen_tac >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> _`
            (drule_then strip_assume_tac) >>
          simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC))
  >- (qpat_assum `~z.vs_halted` ACCEPT_TAC)
QED

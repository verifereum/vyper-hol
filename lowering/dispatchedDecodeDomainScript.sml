Theory dispatchedDecodeDomain
Ancestors vyperValue vyperMisc list rich_list

Definition cd_cast_domain_def:
  cd_cast_domain (BaseTV (BytesT (Fixed n))) = (n <= 32) /\
  cd_cast_domain (ArrayTV t bd) = cd_cast_domain t /\
  cd_cast_domain (TupleTV ts) = EVERY cd_cast_domain ts /\
  cd_cast_domain (StructTV fs) = EVERY (cd_cast_domain o SND) fs /\
  cd_cast_domain _ = T
Termination
  WF_REL_TAC `measure type_value_size` >> rw[] >>
  gvs[type_value_size_def]
End

Theorem evaluate_type_cd_cast_domain_mutual[local]:
  (!tenv ty tv. evaluate_type tenv ty = SOME tv ==> cd_cast_domain tv) /\
  (!tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs /\
    EVERY cd_cast_domain acc ==> EVERY cd_cast_domain tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), cd_cast_domain_def] >>
  `LENGTH args = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF]) >>
  gvs[combinTheory.o_DEF, every_zip_snd]
QED

Theorem evaluate_type_cd_cast_domain:
  evaluate_type tenv ty = SOME tv ==> cd_cast_domain tv
Proof
  metis_tac[evaluate_type_cd_cast_domain_mutual]
QED

Theorem evaluate_types_cd_cast_domain:
  OPT_MMAP (evaluate_type tenv) tys = SOME tvs ==>
  EVERY cd_cast_domain tvs
Proof
  strip_tac >>
  `evaluate_types tenv tys [] = SOME tvs` by
    simp[evaluate_types_OPT_MMAP] >>
  metis_tac[evaluate_type_cd_cast_domain_mutual, EVERY_DEF]
QED

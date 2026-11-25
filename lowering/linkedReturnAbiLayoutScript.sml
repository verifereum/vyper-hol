Theory linkedReturnAbiLayout
Ancestors
  exprLowering compileEnv finite_map list pair

Theorem type_to_abi_enc_info_struct_fields:
  !(sf:(string, (string # type # num) list) fmap) frame ty.
    frame.ce_struct_fields = ce.ce_struct_fields ==>
    type_to_abi_enc_info sf frame ty = type_to_abi_enc_info sf ce ty
Proof
  ho_match_mp_tac type_to_abi_enc_info_ind >> rpt strip_tac >>
  `type_memory_bytes frame = type_memory_bytes ce` by
    (irule type_memory_bytes_frame >> first_assum ACCEPT_TAC) >>
  once_rewrite_tac[type_to_abi_enc_info_def] >> gs[Cong MAP_CONG] >>
  rw[] >~ [`GENLIST`]
  >- (Cases_on `n` >> gs[] >> first_x_assum (qspec_then `0` mp_tac) >> gs[]) >>
  CASE_TAC >> gs[] >> irule MAP_CONG >> simp[FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

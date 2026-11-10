Theory abiDecodePtrRejectSource
Ancestors
  abiValidMembers supportedTypes vyperABI contractABI vyperABIValid
  list rich_list arithmetic

Theorem abi_decode_first_conversion_failure:
  !tys raw hds.
    abi_to_vyper_list env tys
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw hds) = NONE ==>
    ?pre ty post pvs.
      tys = pre ++ ty::post /\
      abi_to_vyper_list env pre
        (abi_decode_members (MAP (vyper_to_abi_type env) pre) raw hds) = SOME pvs /\
      abi_to_vyper env ty
        (dec (vyper_to_abi_type env ty)
          (abi_decode_member_bytes (vyper_to_abi_type env ty) raw
            (DROP (SUM (MAP abi_member_head_size
              (MAP (vyper_to_abi_type env) pre))) hds))) = NONE
Proof
  Induct >- simp[abi_decode_members_def] >>
  qx_gen_tac `ty` >> rpt gen_tac >>
  simp_tac bool_ss [MAP, abi_decode_members_def, Once abi_to_vyper_def] >>
  Cases_on `abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty)
      (abi_decode_member_bytes (vyper_to_abi_type env ty) raw hds))`
  >- (strip_tac >> qexistsl_tac [`[]`, `ty`, `tys`, `[]`] >>
      simp[abi_decode_members_def]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  gvs[AllCaseEqs(), Excl "dec_def"] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ty::pre`, `ty'`, `post`, `x::pvs`] >>
  asm_simp_tac bool_ss [MAP, SUM, APPEND, abi_decode_members_def,
    Once abi_to_vyper_def, DROP_DROP_T, ADD_COMM] >>
  full_simp_tac bool_ss [DROP_DROP_T, ADD_COMM] >>
  simp_tac (srw_ss()) []
QED

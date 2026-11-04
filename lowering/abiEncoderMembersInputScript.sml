(* Peel complete member inputs into the current source slot and remaining tuple. *)
Theory abiEncoderMembersInput
Ancestors
  abiEncoderInput abiEncoderBufferFrame abiDecodeRanges valueEncoding contractABI list rich_list
  arithmetic

Theorem abi_encoder_complex_input_span:
  abi_encoder_input (AbiComplex infos) at av sb capacity mem ==>
  abi_encoder_input (AbiComplex infos) at av sb (abi_encoder_member_span infos) mem
Proof
  simp_tac bool_ss [abi_encoder_complex_input_iff] >> rpt strip_tac >>
  qexistsl_tac [`ats`, `avs`] >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_tuple_input_types:
  abi_encoder_tuple_type at tys /\ has_type at (ListV avs) /\ LENGTH tys = LENGTH avs ==>
  has_types tys avs /\ has_type (Tuple tys) (ListV avs) /\
  enc at (ListV avs) = enc (Tuple tys) (ListV avs)
Proof
  rw[abi_encoder_tuple_type_def] >> gvs[Once has_type_def] >>
  drule have_type_replicate >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once enc_def, LET_THM]
QED

Theorem abi_encoder_complex_input_tuple:
  abi_encoder_input (AbiComplex infos) at (ListV avs) sb capacity mem /\
  abi_encoder_tuple_type at tys ==>
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
    sb (abi_encoder_member_span infos) mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  `layout = tys` by
    (irule abi_encoder_tuple_type_unique >> qexists_tac `at` >> asm_simp_tac bool_ss []) >>
  gvs[] >> drule_all abi_encoder_tuple_input_types >> strip_tac >>
  irule abiEncoderInputTheory.complex >> simp[abi_encoder_tuple_type_def, has_type_def]
QED

Theorem abi_encoder_members_input_cons:
  abi_encoder_input (AbiComplex ((ei,abi_sz,mem_sz,dyn)::infos))
    (Tuple (ty::tys)) (ListV (av::avs)) sb capacity mem ==>
  has_type ty av /\ abi_sz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_input ei ty av sb mem_sz mem /\
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
    (sb+mem_sz) (abi_encoder_member_span infos) mem /\
  mem_sz+abi_encoder_member_span infos <= capacity
Proof
  strip_tac >> qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  gvs[abi_encoder_tuple_type_def, Once has_type_def] >>
  qpat_assum `!i ei abi_sz mem_sz dyn. _`
    (qspecl_then [`0`, `ei`, `abi_sz`, `mem_sz`, `dyn`]
      (mp_tac o SIMP_RULE (srw_ss()) [abi_encoder_member_span_def])) >>
  strip_tac >> asm_simp_tac bool_ss [] >>
  `mem_sz+abi_encoder_member_span infos <= capacity` by
    fs[abi_encoder_member_span_def] >> asm_simp_tac bool_ss [] >>
  `LENGTH avs < dimword (:256)` by decide_tac >>
  irule abiEncoderInputTheory.complex >> simp[abi_encoder_tuple_type_def, has_type_def] >>
  asm_simp_tac (srw_ss()) [] >>
  MAP_EVERY qx_gen_tac [`j`, `child`, `child_asz`, `child_msz`, `child_dyn`] >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _`
    (qspecl_then [`SUC j`, `child`, `child_asz`, `child_msz`, `child_dyn`] mp_tac) >>
  asm_simp_tac (srw_ss()) [TAKE, abi_encoder_member_span_def, AC ADD_COMM ADD_ASSOC]
QED

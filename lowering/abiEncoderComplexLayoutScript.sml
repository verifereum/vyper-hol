(* Complex descriptor heads and dynamic flags agree with semantic tuple layout. *)
Theory abiEncoderComplexLayout
Ancestors
  abiEncoderMembersInput abiEncoderInput abiDecodeRanges valueEncoding contractABI list
  rich_list arithmetic

Theorem abi_encoder_members_metadata:
  LENGTH (infos:(abi_enc_info # num # num # bool) list) = LENGTH tys /\
  (!i ei asz msz dyn. i < LENGTH infos /\ EL i infos = (ei,asz,msz,dyn) ==>
    asz = abi_member_head_size (EL i tys) /\ dyn = is_dynamic (EL i tys)) ==>
  MAP (\(_,asz,_,_). asz) infos = MAP abi_member_head_size tys /\
  MAP (\(_,_,_,dyn). dyn) infos = MAP is_dynamic tys
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> conj_tac >>
  irule LIST_EQ >> asm_simp_tac (srw_ss()) [EL_MAP] >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `EL i infos` >> rename1 `EL i infos = (child,rest)` >> PairCases_on `rest` >>
  qpat_x_assum `!i ei asz msz dyn. _`
    (qspecl_then [`i`, `child`, `rest0`, `rest1`, `rest2`] mp_tac) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_any_dynamic:
  !tys. EXISTS is_dynamic tys = any_dynamic tys
Proof
  Induct >> simp[is_dynamic_def]
QED

Theorem abi_encoder_complex_input_metadata:
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb capacity mem ==>
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths tys 0 /\
  (EXISTS (\(_,_,_,dyn). dyn) infos <=> any_dynamic tys) /\ has_types tys avs
Proof
  strip_tac >> qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  gvs[abi_encoder_tuple_type_def, Once has_type_def] >>
  rename1 `has_types tys avs` >>
  mp_tac (Q.INST [`tys` |-> `tys:abi_type list`] abi_encoder_members_metadata) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >>
  qpat_assum `MAP (\(_,_,_,dyn). dyn) infos = _`
    (assume_tac o SIMP_RULE (srw_ss()) [EXISTS_MAP, ETA_AX] o AP_TERM ``EXISTS I:bool list -> bool``) >>
  asm_simp_tac (srw_ss()) [head_lengths_acc, ADD_CLAUSES, GSYM abi_encoder_any_dynamic] >>
  qpat_x_assum `EXISTS _ infos = _` mp_tac >> simp[EXISTS_MEM]
QED

Theorem abi_encoder_static_tuple_tails:
  !tys avs. ~any_dynamic tys ==> SUM (MAP2 abi_member_tail_size tys avs) = 0
Proof
  Induct >> Cases_on `avs` >> simp[is_dynamic_def, abi_member_tail_size_def]
QED

Theorem abi_encoder_complex_static_length:
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb capacity mem /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  LENGTH (enc (Tuple tys) (ListV avs)) = SUM (MAP (\(_,asz,_,_). asz) infos)
Proof
  strip_tac >> drule abi_encoder_complex_input_metadata >> strip_tac >>
  `~any_dynamic tys` by
    (qpat_assum `EXISTS _ infos = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  drule abi_encoder_static_tuple_tails >> disch_then (qspec_then `avs` assume_tac) >>
  asm_simp_tac bool_ss [canonical_tuple_length, head_lengths_acc, ADD_CLAUSES]
QED

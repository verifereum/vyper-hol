Theory entryConversionPositive
Ancestors
  vyperABI vyperABIRoundtrip entryEncodingPositive valueEncodingProofs
  list rich_list arithmetic

(* List alignment is already exported by vyper_to_abi_list_EL. *)
Theorem same_conversion_length:
  !vs avs. vyper_to_abi_same env ty vs = SOME avs ==>
    LENGTH avs = LENGTH vs
Proof
  Induct >> simp[Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem sparse_conversion_length:
  !n avs. vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
    LENGTH avs = n
Proof
  Induct >> simp[Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem list_conversion_encoding_positive:
  !ts vs avs. LIST_REL P ts vs /\
    vyper_to_abi_list env ts vs = SOME avs /\
    (!ty v av. P ty v /\ vyper_to_abi env ty v = SOME av ==>
       0 < LENGTH (enc (vyper_to_abi_type env ty) av)) ==>
    EVERY (\p. 0 < LENGTH (enc (FST p) (SND p)))
      (ZIP (vyper_to_abi_types env ts,avs))
Proof
  Induct >> Cases_on `vs` >> simp[Once vyper_to_abi_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), Excl "enc_def"] >>
  conj_tac >- metis_tac[] >> first_x_assum irule >> metis_tac[]
QED

Theorem same_conversion_encoding_positive:
  !vs avs. EVERY P vs /\ vyper_to_abi_same env ty vs = SOME avs /\
    (!v av. P v /\ vyper_to_abi env ty v = SOME av ==>
       0 < LENGTH (enc aty av)) ==>
    EVERY (\av. 0 < LENGTH (enc aty av)) avs
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), Excl "enc_def"] >>
  conj_tac >- metis_tac[] >> first_x_assum irule >> metis_tac[]
QED

Theorem sparse_conversion_encoding_positive:
  !n avs. vyper_to_abi_sparse env ty tv n sparse = SOME avs /\
    0 < LENGTH (enc aty (default_to_abi tv)) /\
    (!k v av. k < n /\ ALOOKUP sparse k = SOME v /\
       vyper_to_abi env ty v = SOME av ==>
       0 < LENGTH (enc aty av)) ==>
    EVERY (\av. 0 < LENGTH (enc aty av)) avs
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), Excl "enc_def"] >>
  `!k. k < n ==> k < SUC n` by decide_tac >>
  `n < SUC n` by decide_tac >>
  metis_tac[]
QED

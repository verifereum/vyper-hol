Theory entryAbiSparseTyping
Ancestors
  entryConversionPositive vyperABI vyperTypeABI contractABI list rich_list

(* sparse_conversion_length already exports the required count boundary. *)
Theorem sparse_conversion_abi_typed:
  !n avs.
    has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
    (!i v av. i < n /\ ALOOKUP sparse i = SOME v /\
      vyper_to_abi env ty v = SOME av ==>
      has_type (vyper_to_abi_type env ty) av) /\
    vyper_to_abi_sparse env ty tv n sparse = SOME avs ==>
    EVERY (has_type (vyper_to_abi_type env ty)) avs
Proof
  Induct >> simp[Once vyper_to_abi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  `!k. k < n ==> k < SUC n` by decide_tac >>
  `n < SUC n` by decide_tac >>
  metis_tac[]
QED

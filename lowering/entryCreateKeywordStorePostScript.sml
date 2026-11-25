(* Interface for composing a scoped default-expression exit with its store. *)
Theory entryCreateKeywordStorePost
Ancestors
  groupedKeywordOmitted

Theorem grouped_keyword_store_normal_callback:
  ^(concl grouped_keyword_store_normal_witness)
Proof
  ACCEPT_TAC grouped_keyword_store_normal_witness
QED

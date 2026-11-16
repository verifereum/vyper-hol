(* Add the state-independent empty protected-output containment to the
   original guarded entry.  Reuse its actual proposition, not a copy of the
   implementation-level quotation hierarchy. *)
Theory bodyFullAbiDecodeCallerEntryContained
Ancestors
  bodyFullAbiDecodeCallerEntry

val (entry_vars, entry_body) = strip_forall (concl abi_decode_caller_guarded_entry);
val (entry_pre, entry_post) = dest_imp entry_body;

Theorem abi_decode_caller_guarded_entry_contained:
  ^entry_pre ==>
  ^entry_post /\
  EVERY (\(a,bytes). d <= a /\ a + LENGTH bytes <= d + outsz)
    ([] : (num # word8 list) list)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> conj_tac
  >- (irule abi_decode_caller_guarded_entry >>
      ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl_tac [`G`, `data`, `data_var`, `tn`] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[listTheory.EVERY_DEF]
QED

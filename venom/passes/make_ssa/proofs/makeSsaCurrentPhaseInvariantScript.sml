(* Definition-interface audit.  These are obstructions to a naive initial
   construction, not counterexamples to either frozen contract. *)
Theory makeSsaCurrentPhaseInvariant
Ancestors makeSsaCurrentNameStoreReplay makeSsaCurrentDynamicStores
  makeSsaCurrentTokens list

(* The compiler's full static history contains nondefault tokens even before
   the first runtime write.  The existing replay initial token store gives
   these NONE, while the concrete-name store has an initial atom at each name.
   Thus a phase invariant equating ALL history tokens with name origins cannot
   be initialized using the existing replay's three initial stores. *)
Theorem current_phase_initial_history_obstruction:
  current_history_valid V H /\ MEM t (MAP FST H) /\
  current_token_name H t = SOME x ==>
  current_token_initial t <> current_origin_initial x
Proof
  strip_tac >>
  `!v. t <> CurrentDefault v` by metis_tac[current_history_token_nondefault] >>
  Cases_on `t` >> gvs[current_token_initial_def, current_origin_initial_def]
QED


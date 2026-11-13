(* Relational finite iteration, independent of decoder resource invariants. *)
Theory entryDecoderRelationIteration
Ancestors
  entryDecoderStateFrame allocaHistory calldataSafeIteration relation arithmetic

Theorem entry_relation_finite_iteration:
  !n j I R s.
    reflexive R /\ transitive R /\ j <= n /\ I j s /\
    (!k u. k < n /\ I k u ==> ?v. I (SUC k) v /\ R u v) ==>
    ?t. I n t /\ R s t
Proof
  Induct >- (simp[reflexive_def] >> metis_tac[]) >>
  map_every qx_gen_tac [`j`, `Inv`, `R`, `s`] >> strip_tac >>
  Cases_on `j = SUC n` >- (gvs[reflexive_def] >> metis_tac[]) >>
  `j <= n` by decide_tac >>
  `n < SUC n /\ (!k. k < n ==> k < SUC n)` by decide_tac >>
  `?u. Inv n u /\ R s u` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `?v. Inv (SUC n) v /\ R u v` by metis_tac[] >>
  qexists_tac `v` >> gvs[transitive_def] >> metis_tac[]
QED

Theorem entry_observation_history_reflexive:
  reflexive (\s t. entry_decoder_obs s t /\
    (alloca_history fn s ==> alloca_history fn t))
Proof
  simp[reflexive_def]
QED

Theorem entry_observation_history_transitive:
  transitive (\s t. entry_decoder_obs s t /\
    (alloca_history fn s ==> alloca_history fn t))
Proof
  simp[transitive_def] >> metis_tac[entry_decoder_obs_trans]
QED

Theorem entry_safe_pull_frame_iteration:
  let Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s);
      Pull = \s t. ((!fuel. mem_safe_run fuel ctx fn t) ==>
        !fuel. mem_safe_run fuel ctx fn s);
      Frame = \s t. entry_decoder_obs s t /\
        (alloca_history fn s ==> alloca_history fn t)
  in
  j <= n /\ Inv j s /\
  (!k u. k < n /\ Inv k u ==>
    ?v. Inv (SUC k) v /\ Safe u v /\ Pull u v /\ Frame u v) ==>
  ?t. Inv n t /\ Safe s t /\ Pull s t /\ Frame s t
Proof
  qmatch_goalsub_abbrev_tac `LET _ Safe` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Pull` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ Frame` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >> strip_tac >>
  `reflexive (\s t. Safe s t /\ Pull s t /\ Frame s t)` by
    (simp[reflexive_def, Abbr `Safe`, Abbr `Pull`, Abbr `Frame`] >> metis_tac[]) >>
  `transitive (\s t. Safe s t /\ Pull s t /\ Frame s t)` by
    (simp_tac bool_ss [transitive_def, Abbr `Safe`, Abbr `Pull`, Abbr `Frame`] >>
     metis_tac[calldata_safe_transfer_trans, entry_decoder_obs_trans]) >>
  irule (BETA_RULE (Q.INST [`R` |-> `\s t. Safe s t /\ Pull s t /\ Frame s t`]
    (SPEC_ALL entry_relation_finite_iteration))) >>
  simp[] >> qexists_tac `j` >> simp[]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry relation iteration inherited admission"
    end) [entry_relation_finite_iteration, entry_observation_history_reflexive,
          entry_observation_history_transitive, entry_safe_pull_frame_iteration];

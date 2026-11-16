(* Closed-world sequence composition, conditional on the Step 4 producer. *)
Theory e2eCompose
Ancestors
  e2eTransactionWorld e2eOutcomesDefs e2eDefs e2eLifecycle

(* ML abbreviation only: the exact Step 4 proposition, folded through
   transaction_result. Final acceptance must discharge this hypothesis. *)
val step4_producer_tm =
  ``!policy tops runtime_bc am tx ret es H.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es ==>
    ?r es'. run_call es = SOME (r, es') /\
      transaction_result tops ret am tx es r es'``;

Theorem call_staging_environment[local]:
  vyper_call_staging policy tops runtime_bc am tx ret es ==>
  supported_program tops /\ call_state_rel tops runtime_bc am tx es /\
  balance_bounded (2 ** 256 - 1) es
Proof
  simp_tac bool_ss [vyper_call_staging_def] >> strip_tac >>
  qpat_x_assum `call_state_rel _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [call_state_rel_def] >> strip_tac >> simp[]
QED

Theorem closed_world_transaction_correct_assuming_producer:
  ^step4_producer_tm /\
  call_ready tops runtime_bc am tx.target /\
  vyper_call_staging policy tops runtime_bc am tx ret es /\
  s1_request_prefix tops /\
  vyper_closed_world policy tops runtime_bc am tx H es /\
  call_tx_well_typed tx /\ runtime_bc <> [] /\
  LENGTH es.contexts = 1 /\ run_call es = SOME (r, es') /\
  ~MEM tx.target es'.rollback.toDelete ==>
  call_ready tops runtime_bc (transaction_world am r es') tx.target /\
  transaction_result tops ret am tx es r es'
Proof
  strip_tac >> conj_tac
  >- (`supported_program tops /\
       call_state_rel tops runtime_bc am tx es /\
       balance_bounded (2 ** 256 - 1) es` by
        metis_tac[call_staging_environment] >>
      metis_tac[call_preserves_transaction_world]) >>
  qpat_x_assum `!policy tops runtime_bc am tx ret es H. _`
    (qspecl_then [`policy`, `tops`, `runtime_bc`, `am`, `tx`, `ret`, `es`, `H`]
      mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
QED

Theorem transaction_sequence_correct_assuming_producer:
  ^step4_producer_tm /\
  LENGTH worlds = SUC (LENGTH calls) /\
  call_ready tops runtime_bc (HD worlds) a /\
  s1_request_prefix tops /\ runtime_bc <> [] /\
  (!i tx ret H es r es'.
    i < LENGTH calls /\ EL i calls = (tx, ret, H, es, r, es') /\
    call_ready tops runtime_bc (EL i worlds) a ==>
    tx.target = a /\ call_tx_well_typed tx /\
    vyper_call_staging policy tops runtime_bc (EL i worlds) tx ret es /\
    vyper_closed_world policy tops runtime_bc (EL i worlds) tx H es /\
    LENGTH es.contexts = 1 /\ run_call es = SOME (r, es') /\
    ~MEM a es'.rollback.toDelete /\
    EL (SUC i) worlds = transaction_world (EL i worlds) r es') ==>
  EVERY (\am. call_ready tops runtime_bc am a) worlds /\
  (!i tx ret H es r es'.
    i < LENGTH calls /\ EL i calls = (tx, ret, H, es, r, es') ==>
    transaction_result tops ret (EL i worlds) tx es r es')
Proof
  strip_tac >>
  `EVERY (\am. call_ready tops runtime_bc am a) worlds` by
    (irule (INST_TYPE
       [alpha |-> ``:type``,
        beta |-> ``:(bool # bytes32 # type_value) list # num list``]
       transaction_sequence_call_ready) >> simp[] >>
     qexists `calls` >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `tx.target = a /\ call_tx_well_typed tx /\
      vyper_call_staging policy tops runtime_bc (EL i worlds) tx ret es /\
      vyper_closed_world policy tops runtime_bc (EL i worlds) tx H es /\
      LENGTH es.contexts = 1 /\ run_call es = SOME (r, es') /\
      ~MEM a es'.rollback.toDelete /\
      EL (SUC i) worlds = transaction_world (EL i worlds) r es'` by
        metis_tac[] >>
     drule_all call_staging_environment >> strip_tac >> gvs[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `i < LENGTH worlds` by decide_tac >>
  `call_ready tops runtime_bc (EL i worlds) a` by
    fs[listTheory.EVERY_EL] >>
  `tx.target = a /\ call_tx_well_typed tx /\
   vyper_call_staging policy tops runtime_bc (EL i worlds) tx ret es /\
   vyper_closed_world policy tops runtime_bc (EL i worlds) tx H es /\
   LENGTH es.contexts = 1 /\ run_call es = SOME (r, es') /\
   ~MEM a es'.rollback.toDelete /\
   EL (SUC i) worlds = transaction_world (EL i worlds) r es'` by
     metis_tac[] >>
  mp_tac (Q.INST [`am` |-> `EL i worlds`]
    closed_world_transaction_correct_assuming_producer) >>
  impl_tac >- metis_tac[] >> simp[]
QED

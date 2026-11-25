(* The same four typed words determine the source value and the bytes of
   the computed precompile request, independently of the call oracle. *)
Theory bodyECRecoverPayloadMods
Ancestors
  exprSimPrecompiles venomCallOracleDefs extCallOracle
  venomState valueEncodingDefs list

Theorem ecrecover_payload_mods:
  well_typed_builtin_app ann ECRecover (MAP expr_type args) /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) args vals /\
  LIST_REL (\x ev. eval_operand x sarg =
    SOME (typed_val_to_w256
      (THE (evaluate_type (get_tenv cx) (expr_type (FST ev)))) (SND ev)))
    [h;v;r;sig] (ZIP (args,vals)) /\
  eval_operand h sarg = SOME wh /\ eval_operand v sarg = SOME wv /\
  eval_operand r sarg = SOME wr /\ eval_operand sig sarg = SOME ws ==>
  let a = vfmExecution$ecrecover wh (w2n wv) (w2n wr) (w2n ws);
      payload = word_to_bytes wh T ++ word_to_bytes wv T ++
                word_to_bytes wr T ++ word_to_bytes ws T
  in
    (builtin_result cx acc ann ECRecover (MAP expr_type args) vals =
       INL (AddressV (case a of NONE => 0w | SOME x => x)) /\
     precompile_input ECRecover vals = payload) /\
    (!sbuf wi. mem_bytes_at (w2n wi) 128 sbuf.vs_memory = payload ==>
       let rq = venom_call_request sbuf 1w 0w wi 128w T in
       rq.cr_data = payload /\ computed_precompile rq /\
       precompile_result rq.cr_target rq.cr_data =
         SOME (SOME (case a of NONE => []
                            | SOME x => PAD_LEFT 0w 32 (word_to_bytes x T))))
Proof
  strip_tac >> simp[] >>
  conj_tac
  >- (drule_all ecrecover_typed_result >>
      disch_then (qspec_then `acc` strip_assume_tac) >> gvs[LIST_REL_THM, ZIP]) >>
  rpt gen_tac >> strip_tac >>
  drule ecrecover_request_result >>
  simp[computed_precompile_def, venom_call_request_def,
       read_memory_def, GSYM mem_bytes_at_def, wordsTheory.dimword_def]
QED

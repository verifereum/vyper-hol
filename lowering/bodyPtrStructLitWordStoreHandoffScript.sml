(* Destination framing across a word-load unwrap. This is conditional on
   coverage BEFORE unwrap; it does not derive the first field's layout bound. *)
Theory bodyPtrStructLitWordStoreHandoff
Ancestors emitHelperProps compileEnv loweringStateRelDefs freshWrites decoderGhostFramePtr ghostPcTransportPtr
  bodyPtrStructLitFieldStore bodyPtrDefs venomInst venomState finite_map

Theorem emitted_destination_word_load_frame:
  emit_op opc ops sc = (Var dst,sm) /\ ~not_fresh_at sm out /\
  ptr_covers G tn dst s N ==>
  ptr_covers
    (step_prov PG G (mk_inst id loadop [src] [out]) (update_var out w s))
    (step_taint (mk_inst id loadop [src] [out]) s (update_var out w s) tn)
    dst (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) N
Proof
  strip_tac >>
  `not_fresh_at sm dst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]) >>
  `dst <> out` by metis_tac[] >>
  simp[] >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Histories used for protection retain the context's actual readonly analysis.
   The earlier origin predicates remain unchanged. *)
Theory readonlyInvokeCopyFwdAnalyzedOrigins
Ancestors
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHeterogeneousMapOrigins
  readonlyInvokeCopyFwdAlignedOrigins readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryStackAlignment readonlyInvokeCopyFwdReadonlyContract
  readonlyMemoryArgsDefs venomExecSemantics venomState finite_map list pred_set

Definition ricf_analyzed_ledger_def:
  ricf_analyzed_ledger vs C stk PG G tn fn s a U B ledger <=>
    EVERY (\entry. ?ctxP logP.
      ctxP.icf_rma = readonly_mem_analyze C /\
      ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B entry) ledger
End

Definition ricf_analyzed_map_origins_def:
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites <=>
    !key tr. FLOOKUP sites key = SOME tr ==> ?ctxP logP.
      ctxP.icf_rma = readonly_mem_analyze C /\
      ricf_aligned_translation_origin vs C ctxP logP
        stk PG G tn fn inst s U B key tr
End

Definition ricf_analyzed_saved_map_origins_def:
  ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps <=>
    !j key tr. j < LENGTH stk /\ FLOOKUP (EL j maps) key = SOME tr ==>
      ?ctxP logP p pre anchor tail atn.
        ctxP.icf_rma = readonly_mem_analyze C /\ SUC j <= LENGTH pre /\
        ricf_aligned_origin_at vs C ctxP logP stk PG G tn fn inst s U B
          key tr p pre anchor tail atn
End

Definition ricf_analyzed_origins_def:
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B ledger sites maps <=>
    ricf_analyzed_ledger vs C stk PG G tn fn s a U B ledger /\
    ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
    ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps
End

Theorem ricf_analyzed_origins_empty[simp]:
  ricf_analyzed_origins vs C [] PG G tn fn inst s a U B [] FEMPTY []
Proof
  simp[ricf_analyzed_origins_def, ricf_analyzed_ledger_def,
    ricf_analyzed_map_origins_def, ricf_analyzed_saved_map_origins_def]
QED

Theorem ricf_analyzed_map_origins_update:
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  ctxP.icf_rma = readonly_mem_analyze C /\
  ricf_aligned_translation_origin vs C ctxP logP stk PG G tn fn inst s U B key tr ==>
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B (sites |+ (key,tr))
Proof
  simp[ricf_analyzed_map_origins_def, FLOOKUP_UPDATE] >> strip_tac >>
  qx_gen_tac `lookup_key` >> qx_gen_tac `lookup_tr` >>
  Cases_on `lookup_key = key` >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem ricf_analyzed_map_origins_next:
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_analyzed_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B sites
Proof
  rw[ricf_analyzed_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
  qexistsl_tac [`p`,`pre`,`anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_next >> metis_tac[]
QED

Theorem ricf_analyzed_saved_map_origins_next:
  ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_analyzed_saved_map_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    U B maps
Proof
  rw[ricf_analyzed_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_next >> metis_tac[]
QED

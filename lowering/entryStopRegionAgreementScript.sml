(* Regional syntactic agreement across suffix-retaining STOP insertion. *)
Theory entryStopRegionAgreement
Ancestors
  entryStopStepTransport entryStopObserverConstruction abiEncoderObserver
  venomExecSemantics venomExecProps venomInst list rich_list arithmetic

Theorem entry_stop_region_code_agrees:
  lookup_block lbl fn.fn_blocks = SOME original /\
  phi_prefix_length original.bb_instructions <= k /\
  k <= LENGTH original.bb_instructions /\
  (!idx. (lbl,idx) IN R ==> idx <= k) ==>
  region_code_agrees (entry_stop_function lbl k iid fn) fn (lbl,k) R
Proof
  strip_tac >> rewrite_tac[region_code_agrees_def] >> conj_tac
  >- (rpt gen_tac >>
      simp[entry_stop_function_def, entry_stop_lookup_block] >>
      Cases_on `lookup_block lbl' fn.fn_blocks` >> simp[] >>
      strip_tac >> Cases_on `lbl' = lbl`
      >- (gvs[] >>
          `original.bb_label = lbl` by metis_tac[lookup_block_label] >>
          `idx < k` by (first_x_assum drule >> simp[]) >>
          gvs[entry_stop_block_before_cut]) >>
      `x.bb_label = lbl'` by metis_tac[lookup_block_label] >> gvs[]) >>
  rpt gen_tac >>
  simp[entry_stop_function_def, entry_stop_lookup_block] >>
  Cases_on `lookup_block lbl' fn.fn_blocks` >> simp[] >>
  strip_tac >> Cases_on `lbl' = lbl`
  >- (gvs[] >>
      `original.bb_label = lbl` by metis_tac[lookup_block_label] >>
      drule_all entry_stop_phi_prefix >>
      disch_then (qspec_then `iid` strip_assume_tac) >>
      gvs[entry_stop_block_def]) >>
  `x.bb_label = lbl'` by metis_tac[lookup_block_label] >> gvs[]
QED

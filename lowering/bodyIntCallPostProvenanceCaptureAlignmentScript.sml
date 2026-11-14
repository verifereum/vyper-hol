(* Capture agreement depends on module lookups, not list representation. *)
Theory bodyIntCallPostProvenanceCaptureAlignment
Ancestors
  bodyIntCallPostProvenanceCallbacks bodySim vyperSubscriptOverlap
  vyperInterpreter exprLowering

Theorem effect_free_expr_accesses:
  ~expr_has_effect e ==> expr_accesses mods e = accesses_expr e
Proof
  strip_tac >> drule effect_free_int_calls >>
  simp[expr_accesses_def, reached_functions_def]
QED

Theorem nonconstant_reads_lookup_cong:
  !accs mods mods'. (!src. ALOOKUP mods src = ALOOKUP mods' src) ==>
    nonconstant_reads mods accs = nonconstant_reads mods' accs
Proof
  Induct_on `accs` >- simp[nonconstant_reads_def] >>
  rpt gen_tac >> strip_tac >>
  `nonconstant_reads mods accs = nonconstant_reads mods' accs` by metis_tac[] >>
  Cases_on `h` >>
  simp[nonconstant_reads_def] >>
  rename1 `ReadAcc v` >> Cases_on `v` >>
  simp[nonconstant_reads_def] >>
  Cases_on `p` >> simp[nonconstant_reads_def]
QED

Theorem effect_free_subscript_overlap_lookup_cong:
  (!src. ALOOKUP mods src = ALOOKUP mods' src) /\
  ~expr_has_effect obj /\ ~expr_has_effect idx ==>
  (subscript_overlap mods obj idx <=> subscript_overlap mods' obj idx)
Proof
  strip_tac >> simp[subscript_overlap_def, effect_free_expr_accesses] >>
  metis_tac[nonconstant_reads_lookup_cong]
QED

Theorem body_inv_copies_subscript_base_source:
  body_inv tops ctx ce cx /\ ~expr_has_effect obj /\ ~expr_has_effect idx ==>
  (copies_subscript_base ce obj idx <=> subscript_reads_base cx obj idx)
Proof
  strip_tac >> drule body_inv_modules_aligned >> strip_tac >>
  simp[copies_subscript_base_def, subscript_reads_base_def] >>
  irule effect_free_subscript_overlap_lookup_cong >> simp[] >>
  gen_tac >> simp[vyperContextTheory.get_module_code_def] >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  gvs[vyperContextTheory.get_module_code_def]
QED

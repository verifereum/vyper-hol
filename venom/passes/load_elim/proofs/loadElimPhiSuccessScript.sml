Theory loadElimPhiSuccess
Ancestors
  loadElimPhiCapture loadElimDefs venomExecSemantics venomState list

(* All reads use the incoming snapshot, including when prefix outputs collide. *)
Theorem le_eval_phis_prefix_success:
  !pre s rest u.
    EVERY (\inst. inst.inst_opcode = PHI /\
      ?out w. eval_one_phi s inst = SOME (out,w)) pre /\
    eval_phis s rest = OK u ==>
    ?t. eval_phis s (pre ++ rest) = OK t
Proof
  Induct_on `pre` >- simp[] >>
  rpt gen_tac >> strip_tac >> fs[EVERY_DEF] >>
  first_x_assum drule >> strip_tac >>
  simp[eval_phis_def, exec_result_case_eq]
QED

Theorem le_phis_for_block_success:
  eval_phis s rest = OK u /\ s.vs_prev_bb = SOME pred /\
  (!pa. MEM pa actions /\ pa.pa_join_lbl = lbl ==>
    ?pairs v w. pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
      ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs /\
      lookup_var v s = SOME w) ==>
  ?t. eval_phis s (phis_for_block actions lbl ++ rest) = OK t
Proof
  strip_tac >> irule le_eval_phis_prefix_success >>
  conj_tac >- metis_tac[] >>
  simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexistsl [`pa.pa_phi_out`, `w`] >>
  irule le_generated_phi_eval >> simp[] >>
  metis_tac[]
QED

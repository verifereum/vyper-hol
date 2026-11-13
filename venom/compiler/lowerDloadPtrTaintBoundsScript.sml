Theory lowerDloadPtrTaintBounds
Ancestors ptrDiscipline venomState list pred_set finite_map arithmetic

Theorem dload_op_taint_bound:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {k | k < 32}) ==>
  op_taint tn op SUBSET {k | k < 32}
Proof
  Cases_on `op` >> simp[op_taint_def] >>
  strip_tac >> Cases_on `FLOOKUP tn.t_var s` >> simp[] >> metis_tac[]
QED

Theorem dload_set_var_taint_bound:
  (!v m. FLOOKUP tv v = SOME m ==> m SUBSET {k | k < 32}) /\
  M SUBSET {k | k < 32} ==>
  !v m. FLOOKUP (set_var_taint tv outs M) v = SOME m ==> m SUBSET {k | k < 32}
Proof
  strip_tac >> Cases_on `outs`
  >- (simp[set_var_taint_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `t` >> simp[set_var_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem dload_out_taint_bound:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {k | k < 32}) ==>
  out_taint tn i s SUBSET {k | k < 32}
Proof
  strip_tac >>
  `!op. op_taint tn op SUBSET {k | k < 32}` by
    (gen_tac >> irule dload_op_taint_bound >> metis_tac[]) >>
  Cases_on `i.inst_operands` >> simp[out_taint_def] >>
  Cases_on `t` >> simp[out_taint_def]
  >- (Cases_on `eval_operand h s` >> simp[] >>
      rpt IF_CASES_TAC >> simp[mem_word_taint_def, key_taint_def, SUBSET_DEF] >>
      qpat_x_assum `!op. _` (qspec_then `h` mp_tac) >> simp[SUBSET_DEF]) >>
  Cases_on `t'` >> simp[out_taint_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  rpt IF_CASES_TAC >> simp[shift_taint_def, SUBSET_DEF] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem dload_phi_taint_bound:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {k | k < 32}) ==>
  phi_taint prev tn i SUBSET {k | k < 32}
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_taint_def] >>
  Cases_on `resolve_phi x i.inst_operands` >> simp[] >>
  irule dload_op_taint_bound >> metis_tac[]
QED

Theorem dload_phis_taint_bound:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {k | k < 32}) ==>
  !v m. FLOOKUP (phis_taint prev tn is) v = SOME m ==> m SUBSET {k | k < 32}
Proof
  strip_tac >> Induct_on `is` >> simp[phis_taint_def]
  >- metis_tac[] >>
  gen_tac >> IF_CASES_TAC >> simp[]
  >- metis_tac[] >>
  match_mp_tac dload_set_var_taint_bound >> conj_tac >- metis_tac[] >>
  irule dload_phi_taint_bound >> metis_tac[]
QED

Theorem dload_entry_taint_bound:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {k | k < 32}) ==>
  !v m. FLOOKUP (entry_taint_vars f s tn).t_var v = SOME m ==> m SUBSET {k | k < 32}
Proof
  strip_tac >> simp[entry_taint_vars_def] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >> simp[]
  >- metis_tac[] >>
  match_mp_tac dload_phis_taint_bound >> metis_tac[]
QED

Theorem dload_reachable_taint_bounds:
  !vs C cs PG G tn f i s.
  frame_reachable vs C cs PG G tn f i s ==>
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {k | k < 32}) /\
  (!cf. MEM cf cs ==> !v m. FLOOKUP cf.cf_tvar v = SOME m ==> m SUBSET {k | k < 32})
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- simp[entry_taint_def]
  >- (simp[step_taint_def] >> conj_tac
      >- (match_mp_tac dload_set_var_taint_bound >> conj_tac
          >- metis_tac[] >> irule dload_out_taint_bound >> metis_tac[]) >>
      metis_tac[])
  >- (conj_tac >- (match_mp_tac dload_entry_taint_bound >> metis_tac[]) >> metis_tac[])
  >- (simp[] >> gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  simp[FLOOKUP_DRESTRICT] >> metis_tac[MEM]
QED

Theorem dload_reachable_op_taint_bound:
  frame_reachable vs C cs PG G tn f i s ==>
  op_taint tn op SUBSET {k | k < 32}
Proof
  strip_tac >> irule dload_op_taint_bound >>
  drule dload_reachable_taint_bounds >> metis_tac[]
QED

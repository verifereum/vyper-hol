(* Width of current and saved variable byte masks. *)
Theory lowerDloadSafetyTaintWidth
Ancestors ptrDiscipline finite_map pred_set list arithmetic

Theorem ld_op_taint_width:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {j | j < 32}) ==>
  op_taint tn op SUBSET {j | j < 32}
Proof
  strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
  Cases_on `FLOOKUP tn.t_var s` >> gvs[] >> metis_tac[]
QED

Theorem ld_set_var_taint_width:
  (!v m. FLOOKUP tv v = SOME m ==> m SUBSET {j | j < 32}) /\
  mask SUBSET {j | j < 32} ==>
  !v m. FLOOKUP (set_var_taint tv outs mask) v = SOME m ==>
    m SUBSET {j | j < 32}
Proof
  strip_tac >> Cases_on `outs`
  >- (simp[set_var_taint_def, DRESTRICT_UNIV] >> metis_tac[]) >>
  Cases_on `t` >> simp[set_var_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_out_taint_width:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {j | j < 32}) ==>
  out_taint tn inst s SUBSET {j | j < 32}
Proof
  strip_tac >>
  `!op. op_taint tn op SUBSET {j | j < 32}` by metis_tac[ld_op_taint_width] >>
  simp[out_taint_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[]
  >- (Cases_on `eval_operand h s` >> simp[] >>
      rpt IF_CASES_TAC >> simp[mem_word_taint_def, key_taint_def, SUBSET_DEF]) >>
  Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  rpt IF_CASES_TAC >> simp[shift_taint_def, SUBSET_DEF] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem ld_step_taint_width:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {j | j < 32}) ==>
  !v m. FLOOKUP (step_taint inst s s' tn).t_var v = SOME m ==>
    m SUBSET {j | j < 32}
Proof
  strip_tac >> simp[step_taint_def] >>
  metis_tac[ld_set_var_taint_width, ld_out_taint_width]
QED

Theorem ld_phis_taint_width:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {j | j < 32}) ==>
  !v m. FLOOKUP (phis_taint prev tn ins) v = SOME m ==>
    m SUBSET {j | j < 32}
Proof
  strip_tac >> Induct_on `ins`
  >- (simp[phis_taint_def] >> metis_tac[]) >>
  qx_gen_tac `h` >> simp[phis_taint_def] >> IF_CASES_TAC >> simp[]
  >- metis_tac[] >>
  `phi_taint prev tn h SUBSET {j | j < 32}` by
    (simp[phi_taint_def] >> Cases_on `prev` >> simp[] >>
     Cases_on `resolve_phi x h.inst_operands` >> simp[] >> metis_tac[ld_op_taint_width]) >>
  metis_tac[ld_set_var_taint_width]
QED

Theorem ld_entry_taint_width:
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {j | j < 32}) ==>
  !v m. FLOOKUP (entry_taint_vars fn s tn).t_var v = SOME m ==>
    m SUBSET {j | j < 32}
Proof
  strip_tac >> simp[entry_taint_vars_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  metis_tac[ld_phis_taint_width]
QED

Theorem ld_frame_reachable_taint_width:
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  (!v m. FLOOKUP tn.t_var v = SOME m ==> m SUBSET {j | j < 32}) /\
  (!f v m. MEM f stk /\ FLOOKUP f.cf_tvar v = SOME m ==>
    m SUBSET {j | j < 32})
Proof
  map_every qid_spec_tac [`s`,`inst`,`fn`,`tn`,`G`,`PG`,`stk`,`C`,`vs0`] >>
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- simp[entry_taint_def]
  >- (rpt strip_tac >> metis_tac[ld_step_taint_width])
  >- (rpt strip_tac >> metis_tac[ld_entry_taint_width])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >> gvs[FLOOKUP_DRESTRICT, AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_reachable_op_taint_width:
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  op_taint tn op SUBSET {j | j < 32}
Proof
  strip_tac >> irule ld_op_taint_width >>
  drule ld_frame_reachable_taint_width >> metis_tac[]
QED

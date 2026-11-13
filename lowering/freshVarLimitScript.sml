(* Any finite runtime variable map has a fresh compiler-variable cutoff. *)
Theory freshVarLimit
Ancestors compileEnv loweringStateRelDefs venomState finite_map pred_set ASCIInumbers list

Theorem log_finite_name_bound[local]:
  !names. FINITE names ==>
    ?bound:num. !n. bound <= n ==> STRING #"%" (toString n) NOTIN names
Proof
  ho_match_mp_tac FINITE_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `STRING #"%" (toString _) <> name` >>
  Cases_on `?k:num. name = STRING #"%" (toString k)`
  >- (pop_assum strip_assume_tac >> qexists_tac `MAX bound (SUC k)` >>
      simp[ASCIInumbersTheory.toString_11] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  qexists_tac `bound` >> rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem log_fresh_limit_exists:
  !s sb. ?limit_st. sb.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st s
Proof
  rpt gen_tac >> qspec_then `FDOM s.vs_vars` mp_tac log_finite_name_bound >>
  simp[] >> strip_tac >>
  qexists_tac `sb with cs_next_var := MAX sb.cs_next_var bound` >>
  simp[fresh_vars_wrt_def, arithmeticTheory.GREATER_EQ] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED


(* Membership: empty lists leave code alone; loops first emit JMP. *)
Theory membershipFirstEmission
Ancestors
  compilerFirstEmission entryConditionalFirstEmission contextFirstEmission
  exprLowering fragExec compileEnv emitHelper venomInst context

fun member_append_tac ths g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
       (ths @ [cs_appends_return, cs_appends_prims, cs_appends_emit_helpers, LET_THM])],
    ho_match_mp_tac cs_appends_bind >> conj_tac
      >- member_append_tac ths >> rpt gen_tac >> member_append_tac ths,
    ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >> member_append_tac ths,
    IF_CASES_TAC >> member_append_tac ths]) g;
fun member_tail_tac ths g =
  (rpt gen_tac >> strip_tac >>
   qmatch_asmsub_abbrev_tac `tail s = (y,c)` >>
   `cs_appends tail` by
     (simp_tac bool_ss [Abbr `tail`] >> member_append_tac ths) >>
   fs[cs_appends_def]) g;
fun member_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun member_strong_tac ths g =
  (FIRST [member_emit_tac,
    ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- member_strong_tac ths >> member_tail_tac ths,
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- member_strong_tac ths >> member_tail_tac ths]) g;

Theorem membership_list_in_appends[local]:
  !es. cs_appends (compile_list_membership_in v es)
Proof
  Induct >> simp_tac bool_ss [compile_list_membership_in_def]
  >- simp[cs_appends_return] >> gen_tac >>
  Cases_on `es` >> simp_tac (srw_ss()) [compile_list_membership_in_def] >>
  member_append_tac []
QED

Theorem membership_list_notin_appends[local]:
  !es. cs_appends (compile_list_membership_notin v es)
Proof
  Induct >> simp_tac bool_ss [compile_list_membership_notin_def]
  >- simp[cs_appends_return] >> gen_tac >>
  Cases_on `es` >> simp_tac (srw_ss()) [compile_list_membership_notin_def] >>
  member_append_tac []
QED

Theorem first_emission_list_membership_in:
  !a x b. compile_list_membership_in v es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `es` >- (rewrite_tac[compile_list_membership_in_def] >>
    metis_tac[first_emission_return]) >>
  rename1 `h::t` >> Cases_on `t` >>
  simp_tac (srw_ss()) [compile_list_membership_in_def] >>
  ho_match_mp_tac first_emission_strong >>
  member_strong_tac [membership_list_in_appends]
QED

Theorem first_emission_list_membership_notin:
  !a x b. compile_list_membership_notin v es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `es` >- (rewrite_tac[compile_list_membership_notin_def] >>
    metis_tac[first_emission_return]) >>
  rename1 `h::t` >> Cases_on `t` >>
  simp_tac (srw_ss()) [compile_list_membership_notin_def] >>
  ho_match_mp_tac first_emission_strong >>
  member_strong_tac [membership_list_notin_appends]
QED

Theorem first_emission_array_membership_loop:
  (!p. cs_appends (loader p)) ==>
  !a x b. compile_array_membership_loop v ar len sz off loader isin a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> simp_tac bool_ss [compile_array_membership_loop_def] >>
  ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >>
      rpt gen_tac >> MATCH_ACCEPT_TAC first_emission_fresh) >>
  gen_tac >> ntac 6 (
    ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
    >- (ho_match_mp_tac first_emission_no_code >>
        MATCH_ACCEPT_TAC (cj 1 first_emission_counters)) >> gen_tac) >>
  member_strong_tac []
QED

fun var_member_tac g =
  (ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
   >- (FIRST [metis_tac[first_emission_return],
       ho_match_mp_tac first_emission_strong >>
       MATCH_ACCEPT_TAC first_emission_ptr_load]) >>
   gen_tac >> rewrite_tac[comp_ignore_bind_def] >>
   ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
   >- (FIRST [metis_tac[first_emission_return],
       ho_match_mp_tac first_emission_strong >> member_strong_tac []]) >>
   gen_tac >> ho_match_mp_tac first_emission_array_membership_loop >>
   simp[cs_appends_def] >> metis_tac[first_emission_ptr_load]) g;

Theorem first_emission_var_array_membership:
  !a x b. compile_var_array_membership ce v ar ty isin a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  Cases_on `ty`
  >~ [`ArrayT et bound`] >- (Cases_on `bound` >>
      simp_tac (srw_ss()) [compile_var_array_membership_def, LET_THM] >>
      var_member_tac) >>
  simp_tac (srw_ss()) [compile_var_array_membership_def, LET_THM] >>
  var_member_tac
QED

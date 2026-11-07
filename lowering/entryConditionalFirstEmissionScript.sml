(* A condition may emit nothing; its following branch must emit. *)
Theory entryConditionalFirstEmission
Ancestors
  compilerFirstEmission fragExec compileEnv emitHelper venomInst

Theorem entry_first_emission_then_strong:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!x b y c. k x b = (y,c) ==>
    cs_extends b c /\
    (!fn. fn_has_code b c fn ==>
      ?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (b.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)) ==>
  !a y c. comp_bind m k a = (y,c) ==>
    cs_extends a c /\
    (!fn. fn_has_code a c fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> rpt gen_tac >> simp_tac bool_ss [comp_bind_def] >>
  Cases_on `m a` >> rename1 `m a = (x,b)` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  first_x_assum drule >> disch_then strip_assume_tac >>
  first_x_assum drule >> disch_then strip_assume_tac >>
  (conj_tac >- metis_tac[cs_extends_trans]) >>
  rpt strip_tac >> drule_all fn_has_code_split >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* Exactly the If prefix; the suffix can include arbitrary later PHIs. *)
Theorem entry_conditional_first_emission:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!op t e z. cs_appends (tail op t e z)) ==>
  !a y c.
    (do op <- m;
        t <- fresh_label "then";
        e <- fresh_label "else";
        z <- fresh_label "if_exit";
        emit_inst JNZ [op; Label t; Label e] [];
        tail op t e z od) a = (y,c) ==>
    cs_extends a c /\
    (!fn. fn_has_code a c fn ==>
      ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  strip_tac >> ho_match_mp_tac entry_first_emission_then_strong >>
  conj_tac >- (first_assum ACCEPT_TAC) >> gen_tac >>
  ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_counters]) >>
  gen_tac >> ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_counters]) >>
  gen_tac >> ho_match_mp_tac entry_first_emission_then_strong >> conj_tac
  >- (ho_match_mp_tac first_emission_no_code >> metis_tac[first_emission_counters]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (CONJUNCT1 first_emission_emit_helpers) >> simp[]) >>
  fs[cs_appends_def] >> metis_tac[]
QED

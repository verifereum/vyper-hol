(* Account accessors preserve the callback's weak first-emission boundary. *)
Theory accountFirstEmission
Ancestors
  exprValueFirstEmission compilerFirstEmission exprLowering
  fragExec compileEnv emitHelper venomInst context

Theorem first_emission_acc:
  (!a x b. cfn ce (BaseT AddressT) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !acc a x b. compile_acc cfn ce e acc a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> gen_tac >> Cases_on `acc`
  >~ [`compile_acc _ _ _ Address`] >- (
    rewrite_tac[compile_acc_def] >>
    match_mp_tac first_emission_lower_value >> first_assum ACCEPT_TAC)
  >~ [`compile_acc _ _ _ Code`] >- (
    simp_tac bool_ss [compile_acc_def, LET_THM] >>
    rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
    drule_at (Pos (el 2)) (cj 1 first_emission_emit_helpers) >> simp[]) >>
  simp_tac bool_ss [compile_acc_def, LET_THM] >>
  (ho_match_mp_tac first_emission_pair_let >> conj_tac
   >- (match_mp_tac first_emission_lower_value >> first_assum ACCEPT_TAC) >>
   gen_tac) >>
  rewrite_tac[state_pair_let_bind]
  >~ [`comp_bind _ _ _ = _`] >- (
    ho_match_mp_tac first_emission_bind >> conj_tac
    >- (ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
        drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
    gen_tac >> ho_match_mp_tac first_emission_strong >>
    rpt gen_tac >> strip_tac >>
    drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  ho_match_mp_tac first_emission_strong >> rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

(* Conditional closure at the optional-clamp conversion boundary. *)
Theory conditionalConversionFirstEmission
Ancestors
  compilerFirstEmission conversionFirstEmission exprLowering fragExec
  compileEnv emitHelper venomInst context

Theorem first_emission_cond:
  (!a x b. m a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!a x b. n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. (if p then m else n) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Cases_on `p` >> simp[]
QED

Theorem first_emission_int_to_bytesm:
  !a x b. compile_type_convert v (ConvIntToBytesM signed bits m) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_type_convert_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_cond >> conj_tac
      >- (ho_match_mp_tac first_emission_cond >> conj_tac
          >- suspend "signed_clamp"
          >> suspend "unsigned_clamp") >>
      metis_tac[first_emission_return]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

Resume first_emission_int_to_bytesm[signed_clamp]:
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail st0 = (y,c)` >>
  `cs_appends tail` by
    (simp_tac bool_ss [Abbr `tail`] >>
     ho_match_mp_tac cs_appends_bind >>
     simp[cs_appends_emit_helpers, cs_appends_ignore_bind, cs_appends_return]) >>
  fs[cs_appends_def]
QED

Resume first_emission_int_to_bytesm[unsigned_clamp]:
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `tail st0 = (y,c)` >>
  `cs_appends tail` by
    (simp_tac bool_ss [Abbr `tail`] >>
     ho_match_mp_tac cs_appends_bind >>
     simp[cs_appends_emit_helpers, cs_appends_ignore_bind, cs_appends_return]) >>
  fs[cs_appends_def]
QED

Finalise first_emission_int_to_bytesm

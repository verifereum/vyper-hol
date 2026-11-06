(* Place construction preserves the first non-PHI boundary. *)
Theory exprPlaceFirstEmission
Ancestors
  exprValueFirstEmission contextFirstEmission compilerFirstEmission
  entryConditionalFirstEmission exprLowering fragExec compileEnv emitHelper
  venomInst context

fun place_emit_tac g =
  (rpt gen_tac >> strip_tac >>
   FIRST (map (fn th => drule_at (Pos (el 2)) th >> simp[])
     [cj 1 first_emission_emit_helpers, cj 2 first_emission_emit_helpers,
      cj 3 first_emission_emit_helpers])) g;
fun place_weak_tac g =
  (FIRST [FIRST_PROVE [metis_tac[first_emission_return]],
    ho_match_mp_tac first_emission_strong >> place_emit_tac,
    ho_match_mp_tac first_emission_bind >> conj_tac
      >- place_weak_tac >> gen_tac >> place_weak_tac,
    ho_match_mp_tac first_emission_ignore_bind >> conj_tac >> place_weak_tac,
    IF_CASES_TAC >> place_weak_tac]) g;

Theorem first_emission_mapping_subscript:
  !a x b. compile_mapping_subscript baseop key a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_mapping_subscript_def, compile_alloc_buffer_def, LET_THM] >>
  place_weak_tac
QED

Theorem first_emission_keccak256_key:
  !a x b. compile_keccak256_key key bs32 a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_keccak256_key_def, compile_alloc_buffer_def, LET_THM] >>
  IF_CASES_TAC >> place_weak_tac
QED

Theorem first_emission_tuple_subscript:
  !a x b. compile_tuple_subscript baseop off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rewrite_tac[compile_tuple_subscript_def] >> place_weak_tac
QED

Theorem first_emission_array_subscript:
  (!a x b. loader baseop a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_array_subscript baseop idx dyn cnt ws sz signed loader a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac bool_ss [compile_array_subscript_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (Cases_on `dyn` >> simp_tac bool_ss []
      >- first_assum ACCEPT_TAC >> metis_tac[first_emission_return]) >>
  gen_tac >> place_weak_tac
QED

Theorem first_emission_attribute:
  (!a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_attribute cfn ce rty ty e fld a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac bool_ss [compile_attribute_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >> gen_tac >> place_weak_tac
QED

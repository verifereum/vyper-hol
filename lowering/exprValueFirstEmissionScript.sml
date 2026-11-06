(* Value wrappers preserve the same first-emission interface as callbacks. *)
Theory exprValueFirstEmission
Ancestors
  contextFirstEmission compilerFirstEmission exprLowering
  fragExec compileEnv emitHelper venomInst context

Theorem first_emission_unwrap_value:
  !vv a x b. unwrap_value ce vv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> Cases_on `vv` >> simp_tac (srw_ss()) [unwrap_value_def]
  >- metis_tac[first_emission_return] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_strong >> MATCH_ACCEPT_TAC first_emission_ptr_load) >>
  Cases_on `p.ptr_location` >> simp_tac (srw_ss()) [LET_THM]
  >- metis_tac[first_emission_return] >>
  MATCH_ACCEPT_TAC first_emission_ensure_in_memory
QED

Theorem first_emission_lower_value:
  (!a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. lower_value cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- first_assum ACCEPT_TAC >>
  MATCH_ACCEPT_TAC first_emission_unwrap_value
QED

Theorem first_emission_multi_vvs:
  (!e a x b. MEM e es /\ cfn ce (expr_type e) e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_multi_vvs cfn ce es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct_on `es`
  >- (simp_tac bool_ss [compile_multi_vvs_def] >> metis_tac[first_emission_return]) >>
  gen_tac >> strip_tac >> rewrite_tac[compile_multi_vvs_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[listTheory.MEM] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (first_x_assum match_mp_tac >> metis_tac[listTheory.MEM]) >>
  gen_tac >> metis_tac[first_emission_return]
QED

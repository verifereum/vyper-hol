(* Assignment-target construction and dynamic-array pop preserve first emission. *)
Theory targetPointerFirstEmission
Ancestors
  guardedCallbackFirstEmission exprPlaceFirstEmission exprValueFirstEmission
  contextFirstEmission compilerFirstEmission entryConditionalFirstEmission
  exprLowering fragExec compileEnv emitHelper venomInst context

Theorem first_emission_dynarray_pop:
  !a x b. compile_dynarray_pop baseop ws sz ctor imm loc a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp_tac bool_ss [compile_dynarray_pop_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      MATCH_ACCEPT_TAC first_emission_ptr_load) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 2 first_emission_emit_helpers) >> simp[]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      MATCH_ACCEPT_TAC first_emission_ptr_store) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_get_target_ptr:
  !cfn ce target.
  (!ce ty e a x b. cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_get_target_ptr cfn ce target a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_get_target_ptr_def]
  >- (Cases_on `FLOOKUP ce.ce_vars s` >> simp[comp_return_def, cs_extends_refl] >>
      rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
      simp[comp_return_def, cs_extends_refl])
  >- (simp_tac bool_ss [LET_THM] >>
      qmatch_goalsub_abbrev_tac `FLOOKUP ce.ce_module_vars nsid` >>
      Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[comp_return_def, cs_extends_refl] >>
      rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
      simp[comp_return_def, cs_extends_refl]) >>
  (ho_match_mp_tac first_emission_bind >> conj_tac
   >- (qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >> simp[] >>
       disch_then (qspec_then `ce` mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
   gen_tac >> qpat_x_assum `!y. base_assignment_target_size y < _ ==> _` kall_tac >>
   simp_tac bool_ss [LET_THM])
  >~ [`case SND (SND result) of _ => _`]
  >- suspend "subscript" >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos (el 2)) (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> simp[comp_return_def, cs_extends_refl]
QED

Resume first_emission_get_target_ptr[subscript]:
  Cases_on `SND (SND result)` >> simp_tac (srw_ss()) []
  >- suspend "array_none" >>
  rename1 `SND (SND result) = SOME pt` >> Cases_on `pt` >> simp_tac (srw_ss()) []
  >- suspend "mapping" >>
  suspend "array_val"
QED


Resume first_emission_get_target_ptr[array_none]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> rpt gen_tac >>
      first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_array_subscript >>
      ho_match_mp_tac first_emission_strong >>
      MATCH_ACCEPT_TAC first_emission_ptr_load) >>
  gen_tac >> simp[comp_return_def, cs_extends_refl]
QED

Resume first_emission_get_target_ptr[array_val]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> rpt gen_tac >>
      first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_array_subscript >>
      ho_match_mp_tac first_emission_strong >>
      MATCH_ACCEPT_TAC first_emission_ptr_load) >>
  gen_tac >> simp[comp_return_def, cs_extends_refl]
QED

Resume first_emission_get_target_ptr[mapping]:
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (match_mp_tac first_emission_lower_value >> rpt gen_tac >>
      first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >> asm_simp_tac bool_ss []
      >- MATCH_ACCEPT_TAC first_emission_keccak256_key >>
      simp[comp_return_def, cs_extends_refl]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_mapping_subscript >>
  gen_tac >> simp[comp_return_def, cs_extends_refl]
QED

Finalise first_emission_get_target_ptr

Theorem first_emission_guarded_pop:
  (!ce ty e a x b. expr_size e < expr_size (vyperAST$Pop ann target) /\
    cfn ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) ==>
  !a x b. compile_expr_body
    (expr_child_callback (expr_size (vyperAST$Pop ann target)) cfn)
    bdispatch tdispatch ce ty (vyperAST$Pop ann target) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==>
       ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
         isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  strip_tac >> simp_tac (srw_ss()) [compile_expr_body_def, LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- (match_mp_tac first_emission_get_target_ptr >>
      match_mp_tac first_emission_expr_child_callback >> fs[] >>
      first_assum ACCEPT_TAC) >>
  gen_tac >> PairCases_on `v` >> simp_tac (srw_ss()) [LET_THM] >>
  ho_match_mp_tac first_emission_pair_let >> conj_tac
  >- MATCH_ACCEPT_TAC first_emission_dynarray_pop >>
  rpt gen_tac >> strip_tac >> gvs[cs_extends_refl]
QED

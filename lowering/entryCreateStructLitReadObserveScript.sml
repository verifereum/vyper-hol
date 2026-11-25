(* Observe the actual unwrap path after the field's destination ADD. The
   static exit tests restrict only the observation, not the ordinary post. *)
Theory entryCreateStructLitReadObserve
Ancestors
  bodyFullStructLit bodyFullUnwrap entryStageUnwrapScoped entryCreateFocusSpec
  entryCreateCompletedCut abiEncoderProps venomExecSemantics

Theorem structlit_read_observed_scoped:
  structlit_read_observed
    (\cx st0 tv ee sb sc s z.
      ((!bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) /\
       (!bb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
               get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
               i.inst_id NOTIN frag_ids sb sc)) ==>
      create_operand_full_scope sb sc explicit ctx func s [] (OK z))
    ctx func explicit
Proof
  simp_tac bool_ss [structlit_read_observed_def] >> rpt gen_tac >>
  disch_then (strip_assume_tac o CONJUNCT1) >>
  Cases_on `(!bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
                 phi_prefix_length bb.bb_instructions = 0) /\
            (!bb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
                    get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
                    i.inst_id NOTIN frag_ids sb sc)`
  >- (pop_assum strip_assume_tac >>
      mp_tac stage_unwrap_origin_ptr_scoped >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`] strip_assume_tac) >>
      qexistsl_tac [`v`,`z`,`G'`,`tn'`] >>
      conj_tac >- asm_simp_tac bool_ss [create_operand_full_scope_def, exec_result_case_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac unwrap_value_origin_ptr >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl_tac [`v`,`z`,`G'`,`tn'`] >>
  conj_tac >- asm_simp_tac bool_ss [] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

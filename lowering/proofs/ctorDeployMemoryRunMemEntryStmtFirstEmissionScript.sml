Theory ctorDeployMemoryRunMemEntryStmtFirstEmission
Ancestors
  ctorDeployMemoryRunMemEntryFirstEmission stmtLoweringMono
  compilerFirstEmission stmtLowering compileEnv context exprLowering fragExec exprLoweringProps

Theorem ctor_compile_target_first_emission:
  !env target a x b. compile_get_target_ptr compile_expr env target a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_target_callback_first_emission >>
  disch_then irule >> metis_tac[ctor_compile_expr_first_emission]
QED

Theorem ctor_pass_stmt_first_emission:
  !ce lc ty a x b. compile_stmt ce lc ty Pass a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  simp[compile_stmt_def, comp_return_def, cs_extends_refl]
QED

Theorem ctor_expr_stmt_first_emission:
  !ce lc ty e a x b. compile_stmt ce lc ty (Expr e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >>
  ho_match_mp_tac first_emission_ignore_bind >>
  metis_tac[ctor_compile_expr_first_emission, first_emission_return]
QED

Theorem ctor_emit_local_alloca_first_emission:
  !ce id a x b. emit_local_alloca ce id a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> simp_tac bool_ss [emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[comp_return_def, cs_extends_refl] >>
  Cases_on `x` >> simp[comp_return_def, cs_extends_refl] >>
  BasicProvers.TOP_CASE_TAC >> simp[comp_return_def, cs_extends_refl] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `ALLOCA`) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem ctor_raise_bare_stmt_first_emission:
  !ce lc ty a x b. compile_stmt ce lc ty (Raise RaiseBare) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >>
  mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `REVERT`) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_raise_unreachable_stmt_first_emission:
  !ce lc ty a x b. compile_stmt ce lc ty (Raise RaiseUnreachable) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >>
  mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_unlock_first_emission:
  !nk ut view a x b. compile_nonreentrant_unlock nk ut view a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac bool_ss [compile_nonreentrant_unlock_def] >>
  Cases_on `view` >- metis_tac[first_emission_return] >>
  simp[] >> Cases_on `ut` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `TSTORE`) >>
  mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `SSTORE`) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_emit_inst_weak_first_emission[local]:
  !opc ops outs. opc <> PHI ==>
  !a x b. emit_inst opc ops outs a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  metis_tac[cj 1 first_emission_emit_helpers]
QED

Theorem ctor_external_void_return_first_emission[local]:
  !nr a x b.
    (let (enabled,nk,ut,view) = nr in
       do (if enabled then compile_nonreentrant_unlock nk ut view else return ());
          emit_inst STOP [] [] od) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> PairCases_on `nr` >> simp_tac (bool_ss ++ pairSimps.PAIR_ss) [LET_THM] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (Cases_on `nr0` >> simp[] >>
      metis_tac[ctor_unlock_first_emission, first_emission_return]) >>
  mp_tac (ctor_emit_inst_weak_first_emission |> Q.SPEC `STOP`) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_return_none_stmt_first_emission:
  !ce lc ty a x b. compile_stmt ce lc ty (Return NONE) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> simp_tac bool_ss [compile_stmt_def] >>
  Cases_on `ce.ce_return_pc` >> simp_tac std_ss []
  >- (Cases_on `ce.ce_ctor_exit_label` >> simp_tac std_ss []
      >- ACCEPT_TAC (Q.SPEC `ce.ce_nonreentrant` ctor_external_void_return_first_emission) >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  Cases_on `x` >> simp_tac (bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss) [var_location_case_def]
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >>
          simp[] >> metis_tac[]) >>
      mp_tac (ctor_emit_inst_weak_first_emission |> Q.SPEC `RET`) >>
      simp[] >> metis_tac[])
  >- (Cases_on `ce.ce_ctor_exit_label` >> simp_tac std_ss []
      >- ACCEPT_TAC (Q.SPEC `ce.ce_nonreentrant` ctor_external_void_return_first_emission) >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[])
  >- (Cases_on `ce.ce_ctor_exit_label` >> simp_tac std_ss []
      >- ACCEPT_TAC (Q.SPEC `ce.ce_nonreentrant` ctor_external_void_return_first_emission) >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[])
  >- (Cases_on `ce.ce_ctor_exit_label` >> simp_tac std_ss []
      >- ACCEPT_TAC (Q.SPEC `ce.ce_nonreentrant` ctor_external_void_return_first_emission) >>
      rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]
QED

Theorem ctor_reason_message_first_emission:
  !ce e a x b. compile_reason_message ce e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> Cases_on `e` >>
  simp[compile_reason_message_def] >>~-
    ([`compile_expr _ _ _ _ = _`], metis_tac[ctor_compile_expr_first_emission]) >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> Cases_on `lit` >>
  simp[compile_reason_message_def] >>~-
    ([`compile_expr _ _ _ _ = _`], metis_tac[ctor_compile_expr_first_emission]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_reason_message_def] >>~-
    ([`compile_expr _ _ _ _ = _`], metis_tac[ctor_compile_expr_first_emission]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_bytelike_literal_first_emission] >>
  metis_tac[first_emission_return]
QED

Theorem ctor_revert_reason_first_emission:
  !ce msg ty sz a x b. compile_revert_with_reason ce msg ty sz a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> rewrite_tac[compile_revert_with_reason_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- (simp[cs_appends_emit_helpers] >>
           simp[cs_appends_def] >>
           metis_tac[ctor_alloc_buffer_first_emission, ctor_unwrap_value_first_emission]) >>
       rpt gen_tac) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_raise_reason_stmt_first_emission:
  !ce lc ty e a x b. compile_stmt ce lc ty (Raise (RaiseReason e)) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_reason_message_first_emission] >>
  metis_tac[ctor_revert_reason_first_emission]
QED

Theorem ctor_bind_return_eq[local]:
  comp_bind (comp_return v) k = k v
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem ctor_augassign_stmt_first_emission:
  !ce lc ty target_ty bt bop e a x b.
    compile_stmt ce lc ty (AugAssign target_ty bt bop e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 7 gen_tac >> simp_tac bool_ss [compile_stmt_def, ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_compile_target_first_emission] >>
  gen_tac >> BasicProvers.TOP_CASE_TAC >> simp_tac std_ss []
  >- (mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >>
      simp[] >> metis_tac[]) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (Cases_on `x` >> simp_tac (srw_ss()) [] >>
      rpt gen_tac >> strip_tac >>
      irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[cj 2 ci_mono_compile_expr_sa]) >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[cj 3 ci_mono_compile_expr_sa]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_lower_expr_value_first_emission:
  !ce ty e a x b. lower_value compile_expr ce ty e a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> ho_match_mp_tac ctor_lower_value_first_emission >>
  metis_tac[ctor_compile_expr_first_emission]
QED

Theorem ctor_log_eval_first_emission:
  !ce es a x b. compile_log_eval_all ce es a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> Induct >> simp_tac bool_ss [compile_log_eval_all_def, LET_THM]
  >- metis_tac[first_emission_return] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_lower_expr_value_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >>
  metis_tac[first_emission_return]
QED

Theorem ctor_encode_log_topic_first_emission:
  !v bs a x b. compile_encode_log_topic v bs a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> Cases_on `bs` >> simp_tac bool_ss [compile_encode_log_topic_def]
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `ADD`) >> simp[] >> metis_tac[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  metis_tac[first_emission_return]
QED

Theorem ctor_log_topics_first_emission:
  !ops a x b. compile_log_topic_ops ops a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >> simp_tac bool_ss [compile_log_topic_ops_def]
  >- metis_tac[first_emission_return] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_encode_log_topic_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >>
  metis_tac[first_emission_return]
QED

Theorem ctor_log_stmt_first_emission:
  !ce lc ty id args a x b. compile_stmt ce lc ty (Log id args) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >> simp_tac std_ss []
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  PairCases_on `x` >> simp_tac (bool_ss ++ pairSimps.PAIR_ss) [pairTheory.pair_case_def, ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_log_eval_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_log_topics_first_emission] >>
  gen_tac >> IF_CASES_TAC
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  simp_tac bool_ss [LET_THM, ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_list_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (simp[cs_appends_def] >> metis_tac[ctor_alloc_buffer_first_emission]) >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_abi_encode]) >>
  simp[cs_appends_emit_helpers]
QED

Theorem ctor_dynarray_append_first_emission:
  !ce base v ws sz dt st cap prim loc sop a x b.
    compile_dynarray_append ce base v ws sz dt st cap prim (load_opc_for loc) sop a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 11 gen_tac >> simp_tac bool_ss [compile_dynarray_append_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (Cases_on `loc` >> simp_tac bool_ss [load_opc_for_def] >>
      rpt gen_tac >> strip_tac >> irule (cj 3 first_emission_emit_helpers) >>
      goal_assum $ drule_at Any >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- simp[cs_appends_emit_helpers] >> rpt gen_tac) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (Cases_on `prim` >> simp[cs_appends_emit_helpers] >>
      IF_CASES_TAC >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac >>
      simp[cs_appends_emit_helpers] >> irule ctor_ci_mono_appends >>
      simp[ci_mono_compile_store_memory, ci_mono_compile_word_copy_loop,
           comp_return_def, ci_mono_def, cs_extends_refl]) >>
  ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem ctor_append_stmt_first_emission:
  !ce lc ty target e a x b. compile_stmt ce lc ty (Append target e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM, ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_lower_expr_value_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >- metis_tac[first_emission_return] >>
      simp_tac bool_ss [LET_THM] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- metis_tac[ctor_alloc_buffer_first_emission] >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
      >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_store_memory]) >>
      simp[cs_appends_def, comp_return_def, cs_extends_refl]) >>
  metis_tac[ctor_dynarray_append_first_emission]
QED

Theorem ctor_imm_store_word_first_emission:
  !imm dst v a x b. compile_imm_store_word imm dst v a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> Cases_on `imm` >> simp_tac std_ss [compile_imm_store_word_def]
  >- (mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `ISTORE`) >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `ADD`) >> simp[] >> metis_tac[]) >>
  mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `ISTORE`) >> simp[] >> metis_tac[]
QED

Theorem ctor_store_at_loc_first_emission:
  !imm dst v loc a x b. compile_store_at_loc imm dst v loc a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> Cases_on `loc`
  >- (simp_tac bool_ss [compile_store_at_loc_def] >>
      mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MSTORE`) >> simp[] >> metis_tac[]) >>
  Cases_on `x` >> simp_tac bool_ss [compile_store_at_loc_def] >>
  rpt gen_tac >> strip_tac >>
  FIRST [drule ctor_imm_store_word_first_emission >> simp[],
         drule_at (Pos last) (cj 2 first_emission_emit_helpers) >> simp[]]
QED

Theorem ctor_copy_memory_first_emission:
  !dst src sz a x b. compile_copy_memory dst src sz a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> Cases_on `sz` >> simp_tac bool_ss [compile_copy_memory_def]
  >- metis_tac[first_emission_return] >>
  mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MCOPY`) >> simp[] >> metis_tac[]
QED

Theorem ctor_store_bytestring_first_emission:
  !src dst a x b. compile_store_bytestring src dst a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> simp_tac bool_ss [compile_store_bytestring_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (simp_tac bool_ss [compile_bytestring_copy_len_def, LET_THM] >>
      ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_bind >> conj_tac
      >- simp[cs_appends_emit_helpers] >>
      gen_tac >> ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MCOPY`) >> simp[] >> metis_tac[]
QED

Theorem ctor_tuple_load_all_first_emission:
  !ce src tys off a x b. compile_tuple_load_all ce src tys off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> Cases_on `tys` >> simp_tac bool_ss [compile_tuple_load_all_def, LET_THM]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `ADD`) >> simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_context_helpers]) >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_list_helpers]) >>
  simp[cs_appends_def, comp_return_def, cs_extends_refl]
QED

Theorem ctor_external_return_first_emission:
  !rv prim raw info sz nr nk ut view a x b.
    compile_external_return rv prim raw info sz nr nk ut view a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 9 gen_tac >> simp_tac bool_ss [compile_external_return_def, ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (Cases_on `nr` >> simp[] >> metis_tac[ctor_unlock_first_emission, first_emission_return]) >>
  Cases_on `rv` >> simp_tac std_ss []
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  Cases_on `raw` >> simp_tac bool_ss []
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_bind >> conj_tac
      >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
      gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
      ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  Cases_on `prim` >> simp_tac bool_ss [] >>
  (ho_match_mp_tac first_emission_strong >>
   ho_match_mp_tac first_emission_strong_bind >> conj_tac
   >- metis_tac[ctor_alloc_buffer_first_emission] >>
   gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
   FIRST [ho_match_mp_tac cs_appends_ignore_bind >> simp[cs_appends_emit_helpers],
          ho_match_mp_tac cs_appends_bind >> conj_tac
          >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_abi_encode]) >>
          simp[cs_appends_emit_helpers]])
QED

Theorem ctor_byte_offset_first_emission:
  !ptr off a x b. compile_with_byte_offset ptr off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> simp_tac bool_ss [compile_with_byte_offset_def] >>
  IF_CASES_TAC >- metis_tac[first_emission_return] >>
  mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `ADD`) >> simp[] >> metis_tac[]
QED

Theorem ctor_typed_memory_first_emission:
  (!ce dst dt src st a x b. compile_store_memory_typed ce dst dt src st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst src dts sts doff soff a x b. compile_typed_copy_fields ce dst src dts sts doff soff a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst dt src st n a x b. compile_copy_sarray_typed ce dst dt src st n a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst dt cap src st a x b. compile_copy_dynarray_typed ce dst dt cap src st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))) /\
  (!ce dst src dfs sfs doff soff a x b. compile_struct_typed_copy ce dst src dfs sfs doff soff a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume ctor_typed_memory_first_emission[fields_nil]:
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> metis_tac[first_emission_return]
QED
Resume ctor_typed_memory_first_emission[fields_mismatch]:
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> metis_tac[first_emission_return]
QED
Resume ctor_typed_memory_first_emission[struct_nil]:
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> metis_tac[first_emission_return]
QED
Resume ctor_typed_memory_first_emission[fields_cons]:
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_byte_offset_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_byte_offset_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> metis_tac[]
QED
Resume ctor_typed_memory_first_emission[struct_cons]:
  rpt gen_tac >> strip_tac >>
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >>
  qabbrev_tac `p = case ALOOKUP sfs name of NONE => (dt,dst_sz) | SOME (ft,sz) => (ft,sz)` >>
  PairCases_on `p` >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [GSYM markerTheory.Abbrev_def]) >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss) [LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_byte_offset_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_byte_offset_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> metis_tac[]
QED
Resume ctor_typed_memory_first_emission[dispatch]:
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dt`
  >- (asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
      mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MSTORE`) >> simp[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >> metis_tac[ctor_store_bytestring_first_emission]) >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (Cases_on `dt` >> Cases_on `st` >>
      TRY (rename1 `compile_store_memory_typed ce dst (ArrayT de db) src (ArrayT se sb)` >>
           Cases_on `db` >> Cases_on `sb`) >>
      fs[] >> simp[Once compile_store_memory_typed_def, LET_THM] >>
      metis_tac[ctor_copy_memory_first_emission]) >>
  asm_simp_tac bool_ss [Once compile_store_memory_typed_def] >>
  mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]
QED
Resume ctor_typed_memory_first_emission[sarray]:
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  IF_CASES_TAC >- metis_tac[ctor_copy_memory_first_emission] >>
  ntac 4 (ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `ASSIGN`) >> simp[] >> metis_tac[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  irule ctor_ci_mono_appends >>
  rpt (FIRST [ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind,
        conj_tac >- simp[ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_emit_inst,
          ci_mono_new_block, ci_mono_emit_op, ci_mono_comp_return, ci_mono_typed_memory_family],
        gen_tac]) >> simp[ci_mono_comp_return]
QED
Resume ctor_typed_memory_first_emission[dynarray]:
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [Once compile_store_memory_typed_def, LET_THM] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  irule ctor_ci_mono_appends >>
  rpt (FIRST [ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind,
        conj_tac >- simp[ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_emit_inst,
          ci_mono_new_block, ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
          ci_mono_compile_copy_memory_dynamic, ci_mono_typed_memory_family],
        gen_tac]) >>
  IF_CASES_TAC >>
  rpt (FIRST [ho_match_mp_tac ci_mono_bind, ho_match_mp_tac ci_mono_ignore_bind,
        conj_tac >- simp[ci_mono_fresh_label, ci_mono_fresh_var, ci_mono_emit_inst,
          ci_mono_new_block, ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
          ci_mono_compile_copy_memory_dynamic, ci_mono_typed_memory_family],
        gen_tac]) >> simp[ci_mono_comp_return, ci_mono_compile_copy_memory_dynamic]
QED
Finalise ctor_typed_memory_first_emission

Theorem ctor_store_memory_first_emission:
  !ce src dst dt st a x b. compile_store_memory ce src dst dt st a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_store_memory_def] >>
  IF_CASES_TAC
  >- (mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MSTORE`) >> simp[] >> metis_tac[]) >>
  IF_CASES_TAC >- metis_tac[ctor_store_bytestring_first_emission] >>
  IF_CASES_TAC >- metis_tac[cj 1 ctor_typed_memory_first_emission] >>
  metis_tac[ctor_copy_memory_first_emission]
QED

Theorem ctor_load_tuple_elements_first_emission:
  !ce src tys off a x b. compile_load_tuple_elements ce src tys off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> Cases_on `tys` >> simp_tac bool_ss [compile_load_tuple_elements_def, LET_THM]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `ADD`) >> simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  gen_tac >> ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_list_helpers]) >>
  simp[cs_appends_def, comp_return_def, cs_extends_refl]
QED

Theorem ctor_internal_return_first_emission:
  !ce rv rpc count ty sty tys buf a x b.
    compile_internal_return ce rv rpc count ty sty tys buf a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 8 gen_tac >> simp_tac bool_ss [compile_internal_return_def] >>
  IF_CASES_TAC
  >- (Cases_on `rv` >> simp_tac bool_ss [optionTheory.option_case_def]
      >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
      IF_CASES_TAC
      >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
      ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_load_tuple_elements_first_emission] >>
      rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  Cases_on `buf` >> simp_tac bool_ss [optionTheory.option_case_def]
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  Cases_on `rv` >> simp_tac bool_ss [optionTheory.option_case_def]
  >- (rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]) >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[ctor_store_memory_first_emission] >>
  rpt gen_tac >> strip_tac >> drule_at (Pos last) ctor_emit_inst_weak_first_emission >> simp[]
QED

Theorem ctor_internal_return_env_first_emission:
  !ce ty sty v rpc a x b. compile_internal_return_from_env ce ty sty v rpc a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_internal_return_from_env_def, ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (Cases_on `ce.ce_return_buf` >> simp_tac bool_ss [optionTheory.option_case_def]
      >- metis_tac[first_emission_return] >>
      Cases_on `x` >> simp_tac (srw_ss()) [] >>
      FIRST [metis_tac[first_emission_return],
        ho_match_mp_tac first_emission_bind >> conj_tac
        >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
        metis_tac[first_emission_return]]) >>
  gen_tac >> metis_tac[ctor_internal_return_first_emission]
QED

Theorem ctor_normalized_external_return_first_emission[local]:
  !ce ty sty v a x b.
    (do ret_op <- (if ~is_word_type ty /\
              ~(is_bytestring_type ty /\ is_bytestring_type sty) /\ sty <> ty then
         do norm_buf <- compile_alloc_buffer (type_memory_bytes ce ty);
            compile_store_memory_typed ce norm_buf.buf_operand ty v sty;
            return norm_buf.buf_operand od
       else return v);
       compile_external_return (SOME ret_op) (is_word_type ty) ce.ce_raw_return
         ce.ce_ret_enc_info ce.ce_max_return_size
         (FST ce.ce_nonreentrant) (FST (SND ce.ce_nonreentrant))
         (FST (SND (SND ce.ce_nonreentrant))) (SND (SND (SND ce.ce_nonreentrant)))
     od) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_strong >>
          ho_match_mp_tac first_emission_strong_bind >> conj_tac
          >- metis_tac[ctor_alloc_buffer_first_emission] >>
          gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
          ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
          >- (irule ctor_ci_mono_appends >> simp[ci_mono_typed_memory_family]) >>
          simp[cs_appends_def, comp_return_def, cs_extends_refl]) >>
      metis_tac[first_emission_return]) >>
  gen_tac >> metis_tac[ctor_external_return_first_emission]
QED

Theorem ctor_return_some_stmt_first_emission:
  !ce lc ty e a x b. compile_stmt ce lc ty (Return (SOME e)) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> simp_tac bool_ss [compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_lower_expr_value_first_emission] >>
  gen_tac >> Cases_on `ce.ce_return_pc` >>
  simp_tac bool_ss [optionTheory.option_case_def, LET_THM, ctor_bind_return_eq]
  >- metis_tac[ctor_normalized_external_return_first_emission] >>
  Cases_on `x` >>
  simp_tac bool_ss [compileEnvTheory.var_location_case_def, LET_THM, ctor_bind_return_eq] >>
  FIRST [metis_tac[ctor_internal_return_env_first_emission],
         metis_tac[ctor_normalized_external_return_first_emission],
         ho_match_mp_tac first_emission_bind >> conj_tac
         >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
         gen_tac >> metis_tac[ctor_internal_return_env_first_emission]]
QED

Theorem ctor_word_copy_first_emission:
  !src dst n ll sl ctor a x b. compile_word_copy_loop src dst n ll sl ctor a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 6 gen_tac >>
  simp_tac bool_ss [compile_word_copy_loop_def, compile_word_copy_loop_op_def,
                    compile_word_copy_loop_base_def, LET_THM] >>
  ntac 4 (ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `ASSIGN`) >> simp[] >> metis_tac[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- (simp[cs_appends_prims, cs_appends_emit_helpers,
                 ctor_ptr_load_appends, ctor_ptr_store_appends] >>
           ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
       rpt gen_tac) >>
  simp[cs_appends_prims, cs_appends_emit_helpers]
QED

Theorem ctor_dynarray_to_storage_first_emission:
  !src dst ew ems tr a x b. compile_dynarray_to_storage src dst ew ems tr a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_dynarray_to_storage_def] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  Cases_on `ew = 1` >> Cases_on `tr` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- simp[cs_appends_prims, cs_appends_emit_helpers, ctor_word_copy_loop_appends] >>
       rpt gen_tac) >>
  simp[cs_appends_prims, cs_appends_emit_helpers, ctor_word_copy_loop_appends]
QED

Theorem ctor_lit_byte_offset_first_emission:
  !ptr off a x b. compile_lit_byte_offset ptr off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 2 gen_tac >> simp_tac bool_ss [compile_lit_byte_offset_def] >>
  IF_CASES_TAC >- metis_tac[first_emission_return] >>
  rename1 `emit_op ADD [p; _]` >> Cases_on `p` >> simp_tac (srw_ss()) [] >>
  FIRST [metis_tac[first_emission_return],
    mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `ADD`) >> simp[] >> metis_tac[]]
QED

Theorem ctor_imm_store_words_first_emission:
  !imm src dst n off a x b. compile_imm_store_words imm src dst n off a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> Cases_on `n` >> simp_tac bool_ss [compile_imm_store_words_def]
  >- metis_tac[first_emission_return] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_lit_byte_offset_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[ctor_lit_byte_offset_appends] >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_compile_imm_store_word]) >>
  irule ctor_ci_mono_appends >> simp[ci_mono_compile_imm_store_words]
QED

Theorem ctor_assign_normalize_first_emission[local]:
  !ce guard sz dt value st a x b.
    (if guard then
       do buf <- compile_alloc_buffer sz;
          compile_store_memory_typed ce buf.buf_operand dt value st;
          comp_return buf.buf_operand od
     else comp_return value) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 6 gen_tac >> Cases_on `guard` >> simp_tac bool_ss [COND_CLAUSES]
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_alloc_buffer_first_emission] >>
      gen_tac >> ho_match_mp_tac first_emission_ignore_bind >>
      metis_tac[cj 1 ctor_typed_memory_first_emission, first_emission_return]) >>
  metis_tac[first_emission_return]
QED

Theorem ctor_assign_storage_suffix_first_emission[local]:
  !opc dst value prim di sz dl tr. opc <> PHI ==>
  !a x b.
    (if prim then emit_void opc [dst; value] else
     case di of
       SOME (ew,ems) => compile_dynarray_to_storage value dst ew ems tr
     | NONE => if sz <= 32 then
         do loaded <- emit_op MLOAD [value]; emit_void opc [dst; loaded] od
       else do compile_word_copy_loop value dst (sz DIV 32) LocMemory dl F;
               comp_return () od) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 8 gen_tac >> strip_tac >> Cases_on `prim` >> simp_tac bool_ss [COND_CLAUSES]
  >- (ho_match_mp_tac first_emission_strong >>
      metis_tac[cj 2 first_emission_emit_helpers]) >>
  Cases_on `di` >> simp_tac bool_ss [optionTheory.option_case_def]
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >>
              mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
          gen_tac >> ho_match_mp_tac first_emission_strong >>
          metis_tac[cj 2 first_emission_emit_helpers]) >>
      ho_match_mp_tac first_emission_ignore_bind >>
      metis_tac[ctor_word_copy_first_emission, first_emission_return]) >>
  Cases_on `x` >>
  simp_tac bool_ss [pairTheory.pair_case_def] >>
  metis_tac[ctor_dynarray_to_storage_first_emission]
QED

Theorem ctor_word_copy_loop_base_appends[local]:
  !src dst cnt load_loc store_loc is_ctor imm.
    cs_appends (compile_word_copy_loop_base src dst cnt load_loc store_loc is_ctor imm)
Proof
  rpt gen_tac >> rewrite_tac[compile_word_copy_loop_base_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- (simp[cs_appends_prims, cs_appends_emit_helpers,
                 ctor_ptr_load_appends, ctor_ptr_store_appends] >>
           ho_match_mp_tac cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
       rpt gen_tac) >>
  simp[cs_appends_prims, cs_appends_emit_helpers]
QED

Theorem ctor_store_immutable_bytestring_first_emission[local]:
  !imm src dst a x b.
    compile_store_immutable_bytestring imm src dst a = (x,b) ==>
    cs_extends a b /\
    (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >>
  pure_rewrite_tac[compile_store_immutable_bytestring_def,
    compile_bytestring_word_count_def, comp_bind_assoc] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- (rpt strip_tac >> drule_at Any (cj 3 first_emission_emit_helpers) >> simp[]) >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [irule cs_appends_bind >> conj_tac,
              irule cs_appends_ignore_bind >> conj_tac, gen_tac] >> BETA_TAC >>
       simp[cs_appends_emit_helpers, cs_appends_return, ctor_word_copy_loop_base_appends])
QED

Theorem ctor_assign_code_suffix_first_emission[local]:
  !imm dst value prim dt sz a x b.
    (if prim then compile_imm_store_word imm dst value else
       if is_bytestring_type dt then
         compile_store_immutable_bytestring imm value dst else
       if sz <= 32 then
         do loaded <- emit_op MLOAD [value]; compile_imm_store_word imm dst loaded od
       else compile_imm_store_words imm value dst ((sz + 31) DIV 32) 0) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 6 gen_tac >> Cases_on `prim` >> simp_tac bool_ss [COND_CLAUSES]
  >- metis_tac[ctor_imm_store_word_first_emission] >>
  IF_CASES_TAC
  >- metis_tac[ctor_store_immutable_bytestring_first_emission] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (ho_match_mp_tac first_emission_strong >>
          mp_tac (cj 3 first_emission_emit_helpers |> Q.SPEC `MLOAD`) >> simp[] >> metis_tac[]) >>
      metis_tac[ctor_imm_store_word_first_emission]) >>
  metis_tac[ctor_imm_store_words_first_emission]
QED

Theorem ctor_assign_value_first_emission:
  !ce dst dl value prim sl dt st di sz a x b.
    compile_assign_value ce dst dl value prim sl dt st di sz a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 10 gen_tac >> Cases_on `dl` >>
  simp_tac bool_ss [compile_assign_value_def, LET_THM, data_location_case_def]
  >- (Cases_on `prim` >> simp_tac bool_ss [COND_CLAUSES]
      >- (ho_match_mp_tac first_emission_strong >>
          mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MSTORE`) >> simp[] >> metis_tac[]) >>
      IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[ctor_alloc_buffer_first_emission] >>
          gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
          ho_match_mp_tac first_emission_ignore_bind >>
          metis_tac[ctor_copy_memory_first_emission, ctor_store_memory_first_emission]) >>
      metis_tac[ctor_store_memory_first_emission])
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt gen_tac >> disch_tac >> irule ctor_assign_normalize_first_emission >>
          metis_tac[]) >>
      gen_tac >> simp_tac bool_ss [compile_memory_to_storage_def] >>
      mp_tac (ctor_assign_storage_suffix_first_emission |> Q.SPEC `SSTORE`) >>
      simp[] >> metis_tac[])
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt gen_tac >> disch_tac >> irule ctor_assign_normalize_first_emission >>
          metis_tac[]) >>
      gen_tac >> simp_tac bool_ss [compile_memory_to_transient_def] >>
      mp_tac (ctor_assign_storage_suffix_first_emission |> Q.SPEC `TSTORE`) >>
      simp[] >> metis_tac[])
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- (rpt gen_tac >> disch_tac >> irule ctor_assign_normalize_first_emission >>
          metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      drule ctor_assign_code_suffix_first_emission >> simp[]) >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
  metis_tac[first_emission_return]
QED

Theorem ctor_annassign_stmt_first_emission:
  !ce lc ty id vt e a x b. compile_stmt ce lc ty (AnnAssign id vt e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 6 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[ctor_emit_local_alloca_first_emission] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_compile_expr_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[first_emission_return, ctor_unwrap_value_first_emission]) >>
  gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp_tac bool_ss [optionTheory.option_case_def]
  >- (ho_match_mp_tac first_emission_strong >>
      mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
  Cases_on `x` >> simp_tac bool_ss [var_location_case_def, LET_THM] >>
  FIRST [
    (IF_CASES_TAC
     >- (ho_match_mp_tac first_emission_strong >>
         mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MSTORE`) >> simp[] >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >> drule ctor_assign_value_first_emission >> simp[]),
    (ho_match_mp_tac first_emission_strong >>
     mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[])]
QED

Theorem ctor_snapshot_vv_first_emission[local]:
  !ce copy vv a x b. compile_snapshot_vv ce copy vv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> rewrite_tac[compile_snapshot_vv_def] >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  rpt IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_unwrap_value_first_emission] >>
      metis_tac[first_emission_return])
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_materialize_vv_first_emission] >>
      metis_tac[first_emission_return]) >>
  metis_tac[first_emission_return]
QED

Theorem ctor_baseassign_stmt_first_emission:
  !ce lc ty bt e a x b. compile_stmt ce lc ty (Assign (BaseTarget bt) e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_compile_target_first_emission] >>
      metis_tac[ctor_store_at_loc_first_emission]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_compile_expr_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[first_emission_return, ctor_snapshot_vv_first_emission]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_compile_target_first_emission] >>
  gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
  BasicProvers.TOP_CASE_TAC >> simp_tac bool_ss [optionTheory.option_case_def]
  >- (ho_match_mp_tac first_emission_strong >>
      mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> drule ctor_assign_value_first_emission >> simp[]
QED

Theorem ctor_tuple_store_all_first_emission:
  !ce tys targets vals a x b. compile_tuple_store_all ce tys targets vals a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  gen_tac >> Induct
  >- (rpt gen_tac >> Cases_on `targets` >> Cases_on `vals` >>
      simp_tac bool_ss [compile_tuple_store_all_def] >> metis_tac[first_emission_return]) >>
  ntac 3 gen_tac >> Cases_on `targets`
  >- (simp_tac bool_ss [compile_tuple_store_all_def] >> metis_tac[first_emission_return]) >>
  Cases_on `vals`
  >- (simp_tac bool_ss [compile_tuple_store_all_def] >> metis_tac[first_emission_return]) >>
  rename1 `compile_tuple_store_all ce (_::_) (target::_) (_::_)` >>
  Cases_on `target` >> simp_tac bool_ss [compile_tuple_store_all_def]
  >- (ho_match_mp_tac first_emission_bind >> conj_tac
      >- metis_tac[ctor_compile_target_first_emission] >>
      gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
      ho_match_mp_tac first_emission_ignore_bind >> conj_tac
      >- (IF_CASES_TAC
          >- (IF_CASES_TAC
              >- metis_tac[ctor_store_at_loc_first_emission] >>
              ho_match_mp_tac first_emission_strong >>
              mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
          rpt gen_tac >> strip_tac >> drule ctor_assign_value_first_emission >> simp[]) >>
      metis_tac[]) >>
  ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- (ho_match_mp_tac first_emission_strong >>
      mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ctor_tuple_unpack_first_emission:
  !ce ty stage targets src a x b. compile_tuple_unpack ce ty stage targets src a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_tuple_unpack_def, LET_THM] >>
  IF_CASES_TAC
  >- (ho_match_mp_tac first_emission_strong >>
      mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac first_emission_bind >> conj_tac
          >- metis_tac[ctor_alloc_buffer_first_emission] >>
          gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
          ho_match_mp_tac first_emission_ignore_bind >> conj_tac
          >- (ho_match_mp_tac first_emission_strong >>
              mp_tac (cj 2 first_emission_emit_helpers |> Q.SPEC `MCOPY`) >> simp[] >> metis_tac[]) >>
          metis_tac[first_emission_return]) >>
      metis_tac[first_emission_return]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >>
  metis_tac[ctor_tuple_load_all_first_emission, ctor_tuple_store_all_first_emission]
QED

Theorem ctor_tupleassign_stmt_first_emission:
  !ce lc ty targets e a x b. compile_stmt ce lc ty (Assign (TupleTarget targets) e) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 5 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_compile_expr_first_emission] >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  metis_tac[ctor_tuple_unpack_first_emission]
QED

Theorem ctor_break_stmt_first_emission:
  !ce lc ty a x b. compile_stmt ce lc ty Break a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> Cases_on `lc` >> simp_tac bool_ss [compile_stmt_def] >>
  ho_match_mp_tac first_emission_strong >>
  FIRST [
    mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `JMP`) >> simp[] >> metis_tac[],
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
    >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
    simp[comp_return_def, cs_extends_refl]]
QED

Theorem ctor_continue_stmt_first_emission:
  !ce lc ty a x b. compile_stmt ce lc ty Continue a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> Cases_on `lc` >> simp_tac bool_ss [compile_stmt_def] >>
  ho_match_mp_tac first_emission_strong >>
  FIRST [
    mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `JMP`) >> simp[] >> metis_tac[],
    ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
    >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
    simp[comp_return_def, cs_extends_refl]]
QED

Theorem ctor_if_stmt_first_emission:
  !ce lc ty e yes no a x b. compile_stmt ce lc ty (If e yes no) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 6 gen_tac >> simp_tac bool_ss [compile_stmt_def] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_lower_expr_value_first_emission] >>
  gen_tac >> ntac 3 (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `JNZ`) >> simp[] >> metis_tac[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_prims] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[compile_stmt_ci_mono]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_def, comp_get_def, cs_extends_refl] >>
  gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_prims] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[compile_stmt_ci_mono]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_def, comp_get_def, cs_extends_refl] >>
  gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]) >>
  IF_CASES_TAC >> simp[cs_appends_prims, cs_appends_return] >>
  ho_match_mp_tac cs_appends_ignore_bind >> simp[cs_appends_prims, cs_appends_return]
QED

Theorem ctor_assert_stmt_first_emission:
  !ce lc ty e why a x b. compile_stmt ce lc ty (Assert e why) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> reverse (Cases_on `why`) >> simp_tac bool_ss [compile_stmt_def]
  >- (ho_match_mp_tac first_emission_strong >>
      ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
      >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
      simp[comp_return_def, cs_extends_refl]) >>
  (ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_lower_expr_value_first_emission] >>
  gen_tac >> ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `JNZ`) >> simp[] >> metis_tac[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  rpt (FIRST [ho_match_mp_tac cs_appends_bind,
              ho_match_mp_tac cs_appends_ignore_bind] >> conj_tac
       >- (FIRST [simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return] >> NO_TAC,
                   irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]]) >>
       rpt gen_tac >> simp_tac bool_ss [ctor_bind_return_eq]) >>
  simp[cs_appends_prims, cs_appends_return])
QED


Theorem ctor_range_stmt_first_emission:
  !ce lc ty id ft lo hi bound body a x b.
    compile_stmt ce lc ty (For id ft (Range lo hi) bound body) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 9 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ntac 2 (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[ctor_lower_expr_value_first_emission] >> gen_tac) >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_declare_local_code] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[ctor_emit_local_alloca_first_emission] >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `JMP`) >> simp[] >> metis_tac[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_prims] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_prims] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (Cases_on `lo` >> simp[cs_appends_emit_helpers, cs_appends_return] >>
      Cases_on `hi` >> simp[cs_appends_emit_helpers, cs_appends_return] >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[cs_appends_emit_helpers, cs_appends_return])) >>
  gen_tac >> ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (`cs_appends (compile_range_bound_checks start_op end_op rounds bound (is_signed_type ft))`
        by (irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]) >>
      Cases_on `lo` >> simp[cs_appends_return] >>
      Cases_on `hi` >> simp[cs_appends_return] >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[cs_appends_return])) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ntac 2 (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
    >- simp[cs_appends_prims, cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ntac 2 (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
    >- simp[cs_appends_prims, cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (Cases_on `FLOOKUP body_cenv.ce_vars id` >> simp[cs_appends_emit_helpers] >>
      Cases_on `x` >> simp[cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[compile_stmt_ci_mono]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_prims] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ntac 3 (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
    >- simp[cs_appends_prims, cs_appends_emit_helpers]) >>
  simp[cs_appends_return]
QED

Theorem ctor_array_stmt_first_emission:
  !ce lc ty id ft arr bound body a x b.
    compile_stmt ce lc ty (For id ft (Array arr) bound body) a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 8 gen_tac >> simp_tac bool_ss [compile_stmt_def, LET_THM] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_compile_expr_first_emission] >>
  gen_tac >> simp_tac bool_ss [ctor_bind_return_eq] >>
  ho_match_mp_tac first_emission_bind >> conj_tac
  >- (IF_CASES_TAC >> metis_tac[ctor_ptr_load_first_emission, first_emission_return]) >>
  gen_tac >> ho_match_mp_tac first_emission_bind >> conj_tac
  >- metis_tac[ctor_declare_local_code] >>
  gen_tac >> ho_match_mp_tac first_emission_ignore_bind >> conj_tac
  >- metis_tac[ctor_emit_local_alloca_first_emission] >>
  ntac 5 (ho_match_mp_tac first_emission_bind >> conj_tac
     >- metis_tac[first_emission_fresh, ctor_fresh_label_code] >> gen_tac) >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
  >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `JMP`) >> simp[] >> metis_tac[]) >>
  rewrite_tac[GSYM cs_appends_def] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_prims] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_prims] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_return] >>
      ntac 2 (ho_match_mp_tac cs_appends_bind >> conj_tac
        >- simp[cs_appends_emit_helpers] >> gen_tac) >>
      simp[cs_appends_emit_helpers]) >>
  ntac 2 (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
    >- simp[cs_appends_prims, cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ntac 2 (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
    >- simp[cs_appends_prims, cs_appends_emit_helpers]) >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[cs_appends_emit_helpers, cs_appends_return]) >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (Cases_on `FLOOKUP body_cenv.ce_vars id` >> simp[cs_appends_emit_helpers] >>
      Cases_on `x` >> simp[cs_appends_emit_helpers] >>
      irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[compile_stmt_ci_mono]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- (irule ctor_ci_mono_appends >> simp[ci_mono_stmt_helpers]) >>
  ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
  >- simp[cs_appends_prims] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >> gen_tac >>
  ntac 3 (ho_match_mp_tac cs_appends_ignore_bind >> conj_tac
    >- simp[cs_appends_prims, cs_appends_emit_helpers]) >>
  simp[cs_appends_return]
QED

Theorem ctor_compile_stmt_first_emission:
  !ce lc ty stmt a x b. compile_stmt ce lc ty stmt a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 3 gen_tac >> Cases >>
  FIRST [
    MATCH_ACCEPT_TAC ctor_pass_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_continue_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_break_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_expr_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_if_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_assert_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_log_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_augassign_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_annassign_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_baseassign_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_tupleassign_stmt_first_emission,
    MATCH_ACCEPT_TAC ctor_append_stmt_first_emission,
    (qmatch_goalsub_rename_tac `Assign target value` >> Cases_on `target` >>
      metis_tac[ctor_baseassign_stmt_first_emission, ctor_tupleassign_stmt_first_emission]),
    (qmatch_goalsub_rename_tac `For ident ftype iterator lim stmts` >> Cases_on `iterator` >>
      metis_tac[ctor_range_stmt_first_emission, ctor_array_stmt_first_emission]),
    (rename1 `compile_stmt ce lc ty (Return opt)` >> Cases_on `opt` >>
      metis_tac[ctor_return_none_stmt_first_emission, ctor_return_some_stmt_first_emission]),
    (rename1 `compile_stmt ce lc ty (Raise why)` >> Cases_on `why` >>
      FIRST [MATCH_ACCEPT_TAC ctor_raise_bare_stmt_first_emission,
             MATCH_ACCEPT_TAC ctor_raise_unreachable_stmt_first_emission,
             MATCH_ACCEPT_TAC ctor_raise_reason_stmt_first_emission,
             (simp_tac bool_ss [compile_stmt_def] >>
              ho_match_mp_tac first_emission_strong >>
              ho_match_mp_tac first_emission_strong_ignore_bind >> conj_tac
              >- (mp_tac (cj 1 first_emission_emit_helpers |> Q.SPEC `INVALID`) >> simp[] >> metis_tac[]) >>
              simp[comp_return_def, cs_extends_refl])])]

QED

Theorem ctor_compile_stmts_first_emission:
  !ss ce lc ty a x b. compile_stmts ce lc ty ss a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  mp_tac ctor_stmts_first_emission_lift >>
  (impl_tac >- metis_tac[ctor_compile_stmt_first_emission]) >>
  simp[]
QED

(* Concrete variable-parameter return probe. Named compiler/state fixtures
   keep executable certificates small; no universal body judgment is assumed. *)
Theory bodyPtrStructLitVariableReturn
Ancestors bodyPtrStructLitReturnCertificate bodyPtrStructLitReturnBoundary
  fragGasSeqPtr finite_map ptrSafeRun ptrDiscipline venomInst
  venomState venomExecSemantics instIdxIndep codegenRel contextCodegenRel list rich_list
Libs wordsLib intLib

Definition structlit_variable_env_def:
  structlit_variable_env = (structlit_callee_env F) with
    <| ce_return_buf := SOME (PtrVar (Var "return_buffer") 160);
       ce_return_pc := SOME (PtrVar (Var "return_pc") 0) |>
End

Definition structlit_variable_compiled_def:
  structlit_variable_compiled =
    compile_stmt structlit_variable_env NoLoop (structlit_callee_type 33)
      (Return (SOME (structlit_callee_expr F))) (initial_compile_state "probe")
End

Definition structlit_variable_initial_def:
  structlit_variable_initial = structlit_callee_initial with
    <| vs_vars := FEMPTY |+ ("return_buffer",64w) |+ ("return_pc",1w);
       vs_allocas := FEMPTY |+ (100,(64,160)) |>
End

Theorem structlit_variable_instructions:
  (SND structlit_variable_compiled).cs_current_insts =
    TAKE 13 (SND (structlit_callee_return_compiled F)).cs_current_insts ++
    [mk_inst 13 MCOPY [Var "return_buffer"; Var "%0"; Lit 160w] [];
     mk_inst 14 RET [Var "return_pc"] []]
Proof
  EVAL_TAC
QED

Definition structlit_variable_state_def:
  structlit_variable_state n =
    case run_inst_seq (TAKE n (SND structlit_variable_compiled).cs_current_insts)
      structlit_variable_initial of
      OK s => s
    | _ => structlit_variable_initial
End

Theorem structlit_variable_copy_run:
  (case run_inst_seq
    (TAKE 14 (SND structlit_variable_compiled).cs_current_insts)
    structlit_variable_initial of
    OK s => SOME (lookup_var "return_pc" s, lookup_var "return_buffer" s,
                  read_memory 64 160 s)
  | _ => NONE) = SOME (SOME 1w, SOME 64w, REPLICATE 160 0w)
Proof
  EVAL_TAC
QED

Theorem structlit_variable_ret_execution:
  step_inst_base (mk_inst 14 RET [Var "return_pc"] [])
    (structlit_variable_state 14 with vs_inst_idx := 14) =
  IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
    (structlit_variable_state 14 with vs_inst_idx := 14)
Proof
  EVAL_TAC
QED

Theorem structlit_variable_ret_safe:
  !D fuel ctx fn PG G tn.
    ~ctx_has_dalloca ctx /\ op_taint tn (Var "return_pc") = {} ==>
    ptr_safe_step D 0 fuel ctx fn PG G tn
      (mk_inst 14 RET [Var "return_pc"] [])
      (structlit_variable_state 14 with vs_inst_idx := 14)
Proof
  rpt strip_tac >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, mk_inst_def,
       access_ok_def, taint_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke,
       structlit_variable_ret_execution] >>
  EVAL_TAC >> simp[]
QED

(* The caller-owned buffer is allocated but initially wholly uninitialized.
   These executable ghost prefixes follow the same successful state sequence. *)
Definition structlit_variable_prov_def:
  structlit_variable_prov 0 = FEMPTY |+ ("return_buffer",(64,160)) /\
  structlit_variable_prov (SUC n) =
    step_prov [] (structlit_variable_prov n)
      (EL n (SND structlit_variable_compiled).cs_current_insts)
      (structlit_variable_state (SUC n))
End

Definition structlit_variable_taint_def:
  structlit_variable_taint 0 =
    entry_taint with t_mem := {i | 64 <= i /\ i < 224} /\
  structlit_variable_taint (SUC n) =
    step_taint (EL n (SND structlit_variable_compiled).cs_current_insts)
      (structlit_variable_state n) (structlit_variable_state (SUC n))
      (structlit_variable_taint n)
End

Theorem structlit_variable_ret_pc_frame:
  !n. n <= 14 ==>
    FLOOKUP (structlit_variable_taint n).t_var "return_pc" = NONE
Proof
  Induct >> simp[structlit_variable_taint_def, entry_taint_def] >>
  strip_tac >>
  `n < 14` by decide_tac >>
  `~MEM "return_pc"
     (EL n (SND structlit_variable_compiled).cs_current_insts).inst_outputs` by
    (`EVERY (\i. ~MEM "return_pc" i.inst_outputs)
       (SND structlit_variable_compiled).cs_current_insts` by EVAL_TAC >>
     fs[EVERY_EL] >> first_x_assum irule >>
     simp[structlit_variable_instructions, structlit_return_instructions]) >>
  simp[step_taint_def, set_var_taint_def] >>
  Cases_on `(EL n (SND structlit_variable_compiled).cs_current_insts).inst_outputs` >>
  gvs[FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem structlit_variable_ret_pc_clean:
  op_taint (structlit_variable_taint 14) (Var "return_pc") = {}
Proof
  simp[op_taint_def, structlit_variable_ret_pc_frame]
QED

Theorem structlit_variable_ret_safe_final:
  !D fuel ctx fn.
    ~ctx_has_dalloca ctx ==>
    ptr_safe_step D 0 fuel ctx fn []
      (structlit_variable_prov 14) (structlit_variable_taint 14)
      (mk_inst 14 RET [Var "return_pc"] [])
      (structlit_variable_state 14 with vs_inst_idx := 14)
Proof
  rpt strip_tac >> irule structlit_variable_ret_safe >>
  simp[structlit_variable_ret_pc_clean]
QED

Theorem structlit_variable_allocation_results:
  FLOOKUP (structlit_variable_state 1).vs_allocas 0 = SOME (224,160) /\
  FLOOKUP (structlit_variable_state 2).vs_allocas 1 = SOME (384,32) /\
  FLOOKUP (structlit_variable_state 10).vs_allocas 9 = SOME (416,64)
Proof
  rpt conj_tac >> EVAL_TAC
QED


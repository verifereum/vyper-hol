(* Finite return-prefix certificates. Prefix states keep concrete evaluation
   separate from symbolic taint threading; no pointer-safety claim is made. *)
Theory bodyPtrStructLitReturnCertificate
Ancestors bodyPtrStructLitCalleeFixture bodyPtrStructLitGhostNormalize
  exprLoweringProps venomState venomInst ptrDiscipline ghostPcTransportPtr
  fragExecPtr allocationPtr list rich_list instIdxIndep
Libs wordsLib intLib

(* Naming return-prefix states avoids repeating the compiler and memory terms
   in each independently checked machine and ghost equation. *)
Definition structlit_return_state_def:
  structlit_return_state n =
    case run_inst_seq
      (TAKE n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      structlit_callee_initial of
      OK s => s
    | _ => structlit_callee_initial
End

Theorem structlit_return_instructions:
  (SND (structlit_callee_return_compiled F)).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 160w] ["%0"];
     mk_inst 1 ALLOCA [Lit 32w] ["%1"];
     mk_inst 2 MSTORE [Var "%1"; Lit 0w] [];
     mk_inst 3 ADD [Var "%0"; Lit 0w] ["%2"];
     mk_inst 4 MLOAD [Var "%1"] ["%3"];
     mk_inst 5 ADD [Var "%3"; Lit 31w] ["%4"];
     mk_inst 6 AND [Var "%4"; Lit (-32w)] ["%5"];
     mk_inst 7 ADD [Var "%5"; Lit 32w] ["%6"];
     mk_inst 8 MCOPY [Var "%2"; Var "%1"; Var "%6"] [];
     mk_inst 9 ALLOCA [Lit 64w] ["%7"];
     mk_inst 10 MSTORE [Var "%7"; Lit 0w] [];
     mk_inst 11 ADD [Var "%0"; Lit 96w] ["%8"];
     mk_inst 12 MCOPY [Var "%8"; Var "%7"; Lit 64w] [];
     mk_inst 13 MLOAD [Lit 32w] ["%9"];
     mk_inst 14 MLOAD [Lit 0w] ["%10"];
     mk_inst 15 MCOPY [Var "%10"; Var "%0"; Lit 160w] [];
     mk_inst 16 RET [Var "%9"] []]
Proof
  EVAL_TAC
QED

Theorem structlit_run_inst_seq_extend:
  !xs s t i u.
    run_inst_seq xs s = OK t /\ step_inst_base i t = OK u ==>
    run_inst_seq (xs ++ [i]) s = OK u
Proof
  rpt strip_tac >> drule run_inst_seq_append >>
  disch_then (qspec_then `[i]` SUBST1_TAC) >>
  simp[run_inst_seq_def]
QED

Theorem structlit_run_inst_seq_prefix_success:
  !xs ys s u. run_inst_seq (xs ++ ys) s = OK u ==>
    ?t. run_inst_seq xs s = OK t
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `ys` assume_tac) >> gvs[]
QED

Theorem structlit_return_prefix_success:
  !n. n <= 16 ==>
    run_inst_seq
      (TAKE n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      structlit_callee_initial = OK (structlit_return_state n)
Proof
  rpt strip_tac >>
  mp_tac structlit_callee_return_store_run >>
  Cases_on `run_inst_seq
    (TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts)
    structlit_callee_initial` >> simp[] >> strip_tac >>
  `TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts =
    TAKE n (SND (structlit_callee_return_compiled F)).cs_current_insts ++
    DROP n (TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts)` by
    (qspec_then `n` (qspec_then
      `TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts`
      mp_tac) TAKE_DROP >>
     pure_rewrite_tac[TAKE_TAKE_MIN] >>
     `MIN n 16 = n` by (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `TAKE 16 _ = _` (fn th =>
    qpat_x_assum `run_inst_seq _ _ = OK _`
      (mp_tac o ONCE_REWRITE_RULE [th])) >>
  disch_tac >> drule structlit_run_inst_seq_prefix_success >>
  strip_tac >> simp[structlit_return_state_def]
QED

Theorem structlit_return_step:
  !n. n < 16 ==>
    step_inst_base
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state n) = OK (structlit_return_state (SUC n))
Proof
  rpt strip_tac >>
  `n <= 16 /\ SUC n <= 16` by decide_tac >>
  qspec_then `n` mp_tac structlit_return_prefix_success >> simp[] >> strip_tac >>
  qspec_then `SUC n` mp_tac structlit_return_prefix_success >>
  simp[] >>
  `TAKE (SUC n) (SND (structlit_callee_return_compiled F)).cs_current_insts =
    TAKE n (SND (structlit_callee_return_compiled F)).cs_current_insts ++
    [EL n (SND (structlit_callee_return_compiled F)).cs_current_insts]` by
    simp[TAKE_SUC, TAKE1_DROP, structlit_return_instructions] >>
  pop_assum SUBST1_TAC >>
  drule run_inst_seq_append >> disch_then (rewrite_tac o single) >>
  simp[run_inst_seq_def] >>
  Cases_on `step_inst_base
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state n)` >> simp[]
QED

Theorem structlit_return_step_at_cursor:
  !n k. n < 16 ==>
    step_inst_base
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state n with vs_inst_idx := k) =
    OK (structlit_return_state (SUC n) with vs_inst_idx := k)
Proof
  rpt strip_tac >>
  `~is_terminator
    (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts).inst_opcode` by
    (`EVERY (\i. ~is_terminator i.inst_opcode)
        (TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts)` by
       (rewrite_tac[structlit_return_instructions] >> EVAL_TAC) >>
     `LENGTH (SND (structlit_callee_return_compiled F)).cs_current_insts = 17` by
       simp[structlit_return_instructions] >>
     fs[EVERY_EL] >>
     first_x_assum (qspec_then `n` mp_tac) >>
     simp[LENGTH_TAKE, EL_TAKE]) >>
  simp[step_inst_inst_idx_indep, structlit_return_step, exec_result_map_def]
QED

Theorem structlit_return_copy_operands:
  eval_operand (Var "%8") (structlit_return_state 12) = SOME 320w /\
  eval_operand (Var "%7") (structlit_return_state 12) = SOME 416w /\
  eval_operand (Var "%10") (structlit_return_state 15) = SOME 64w /\
  eval_operand (Var "%0") (structlit_return_state 15) = SOME 224w
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem structlit_return_array_store_operand:
  eval_operand (Var "%7") (structlit_return_state 10) = SOME 416w
Proof
  EVAL_TAC
QED


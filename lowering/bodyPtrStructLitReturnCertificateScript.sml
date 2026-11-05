(* Finite return-prefix certificates. Prefix states keep concrete evaluation
   separate from symbolic taint threading; no pointer-safety claim is made. *)
Theory bodyPtrStructLitReturnCertificate
Ancestors bodyPtrStructLitCalleeFixture bodyPtrStructLitGhostNormalize
  exprLoweringProps venomState venomInst ptrDiscipline ghostPcTransportPtr
  fragExecPtr allocationPtr list rich_list instIdxIndep venomMemProps venomInstProofs1
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

Theorem structlit_return_memory_fields:
  !n. MEM n [10;11;12;13;14;15] ==>
    (structlit_return_state (SUC n)).vs_allocas =
      (structlit_return_state n).vs_allocas /\
    (structlit_return_state (SUC n)).vs_fmp =
      (structlit_return_state n).vs_fmp
Proof
  rpt gen_tac >> strip_tac >>
  `n < 16` by (gvs[] >> decide_tac) >>
  drule structlit_return_step >> strip_tac >>
  conj_tac
  >- (irule step_inst_base_preserves_allocas >>
      qexists_tac `EL n (SND (structlit_callee_return_compiled F)).cs_current_insts` >>
      gvs[structlit_return_instructions, mk_inst_def]) >>
  irule step_inst_base_preserves_fmp_ordinary >>
  goal_assum (drule_at Any) >>
  gvs[structlit_return_instructions, mk_inst_def,
      is_terminator_def, is_alloca_op_def, is_ext_call_op_def]
QED

Theorem structlit_return_frame_writes:
  !n tn s t. MEM n [11;13;14] ==>
    step_writes (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      s t = [] /\
    written_taint tn
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts) s = {}
Proof
  simp[] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[structlit_return_instructions] >> EVAL_TAC
QED

Theorem structlit_return_memory_taint_frame:
  !n tn. MEM n [11;13;14] ==>
    !t. t = structlit_return_state (SUC n) ==>
    (step_taint
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state n) t tn).t_mem = tn.t_mem
Proof
  rpt strip_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  irule structlit_step_taint_memory_frame >>
  simp[structlit_return_frame_writes] >>
  `MEM n [10;11;12;13;14;15]` by gvs[] >>
  drule structlit_return_memory_fields >> simp[]
QED

Theorem structlit_return_array_allocation_fields:
  FLOOKUP (structlit_return_state 9).vs_allocas 9 = NONE /\
  (structlit_return_state 9).vs_alloca_next = 416
Proof
  conj_tac >> EVAL_TAC
QED

Theorem structlit_return_array_allocation_taint:
  !tn i t. t = structlit_return_state 10 /\ i < 416 ==>
    (i IN (step_taint
      (EL 9 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 9) t tn).t_mem <=> i IN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst 9 ALLOCA [Lit 64w] ["%7"])
      (structlit_return_state 9) = OK (structlit_return_state 10)` by
    (mp_tac (Q.SPEC `9` structlit_return_step) >>
     simp[structlit_return_instructions]) >>
  rewrite_tac[structlit_return_instructions] >> simp[] >>
  irule fresh_alloca_taint_below_frontier >>
  simp[structlit_return_array_allocation_fields]
QED

Theorem structlit_return_array_store_clean:
  !tn i t. t = structlit_return_state 11 /\ 416 <= i /\ i < 448 ==>
    i NOTIN (step_taint
      (EL 10 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 10) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  simp[structlit_return_instructions] >>
  irule mstore_word_clean >>
  simp[structlit_return_array_store_operand, eval_operand_def, op_taint_def]
QED

Theorem structlit_return_store_preserves_clean:
  !tn i t. t = structlit_return_state 11 /\ i NOTIN tn.t_mem ==>
    i NOTIN (step_taint
      (EL 10 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 10) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `new_site_bytes (structlit_return_state 10) (structlit_return_state 11) = {}` by
    (irule structlit_new_site_bytes_unchanged >>
     mp_tac (Q.SPEC `10` structlit_return_memory_fields) >> simp[]) >>
  simp[structlit_return_instructions, step_taint_def, mem_taint_def,
       written_taint_def, mk_inst_def,
       structlit_return_array_store_operand, op_taint_def]
QED

Theorem structlit_return_array_copy_clean:
  !tn j t. j < 32 /\ j + 416 NOTIN tn.t_mem ==>
    j + 320 NOTIN (step_taint
      (EL 12 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 12) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >> simp[structlit_return_instructions] >>
  irule structlit_mcopy_operand_byte_clean >>
  simp[structlit_return_copy_operands, eval_operand_def] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem structlit_return_array_copy_preserves_first_header:
  !tn i t. t = structlit_return_state 13 /\ i < 256 /\ i NOTIN tn.t_mem ==>
    i NOTIN (step_taint
      (EL 12 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 12) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `new_site_bytes (structlit_return_state 12) (structlit_return_state 13) = {}` by
    (irule structlit_new_site_bytes_unchanged >>
     mp_tac (Q.SPEC `12` structlit_return_memory_fields) >> simp[]) >>
  simp[structlit_return_instructions, step_taint_def, mem_taint_def,
       written_taint_def, mk_inst_def, structlit_return_copy_operands,
       eval_operand_def] >> decide_tac
QED

Theorem structlit_return_early_state:
  !n. n <= 13 ==>
    structlit_return_state n = structlit_callee_state F n
Proof
  rpt strip_tac >>
  `MIN n 13 = n` by (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `TAKE n (SND (structlit_callee_return_compiled F)).cs_current_insts =
    TAKE n (SND (structlit_callee_compiled F)).cs_current_insts` by
    (mp_tac structlit_callee_return_expression_prefix >>
     disch_then (mp_tac o AP_TERM ``TAKE n : instruction list -> instruction list``) >>
     simp[TAKE_TAKE_MIN]) >>
  simp[structlit_return_state_def, structlit_callee_state_def]
QED

Theorem structlit_return_taint_run_step:
  !n k is tn. n < 16 ==>
    structlit_callee_taint_run
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts :: is)
      (structlit_return_state n with vs_inst_idx := k) tn =
    structlit_callee_taint_run is
      (structlit_return_state (SUC n) with vs_inst_idx := SUC k)
      (step_taint
        (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
        (structlit_return_state n) (structlit_return_state (SUC n)) tn)
Proof
  rpt strip_tac >>
  simp[structlit_callee_taint_run_def, structlit_return_step_at_cursor]
QED

Theorem structlit_return_final_copy_clean:
  !tn i t. 64 <= i /\ i < 224 /\ i + 160 NOTIN tn.t_mem ==>
    i NOTIN (step_taint
      (EL 15 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 15) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >> simp[structlit_return_instructions] >>
  irule structlit_mcopy_operand_byte_clean >>
  simp[structlit_return_copy_operands, eval_operand_def] >>
  qexists_tac `i - 64` >>
  `i - 64 + 224 = i + 160` by decide_tac >> simp[]
QED

Theorem structlit_return_suffix_segment:
  TAKE 7 (DROP 9 (SND (structlit_callee_return_compiled F)).cs_current_insts) =
    MAP (\n. EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      [9;10;11;12;13;14;15]
Proof
  rewrite_tac[structlit_return_instructions] >> EVAL_TAC
QED

Theorem structlit_return_suffix_first_header:
  !tn k j. j < 32 /\ j + 224 NOTIN tn.t_mem ==>
    j + 64 NOTIN (structlit_callee_taint_run
      (TAKE 7 (DROP 9 (SND (structlit_callee_return_compiled F)).cs_current_insts))
      (structlit_return_state 9 with vs_inst_idx := k) tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[structlit_return_suffix_segment, MAP] >>
  simp[structlit_return_taint_run_step] >>
  rewrite_tac[structlit_callee_taint_run_def] >>
  irule structlit_return_final_copy_clean >> simp[] >>
  simp[structlit_return_memory_taint_frame] >>
  irule structlit_return_array_copy_preserves_first_header >> simp[] >>
  simp[structlit_return_memory_taint_frame] >>
  irule structlit_return_store_preserves_clean >> simp[] >>
  simp[structlit_return_array_allocation_taint] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem structlit_return_suffix_array_header:
  !tn k j. j < 32 ==>
    j + 160 NOTIN (structlit_callee_taint_run
      (TAKE 7 (DROP 9 (SND (structlit_callee_return_compiled F)).cs_current_insts))
      (structlit_return_state 9 with vs_inst_idx := k) tn).t_mem
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[structlit_return_suffix_segment, MAP] >>
  simp[structlit_return_taint_run_step] >>
  rewrite_tac[structlit_callee_taint_run_def] >>
  irule structlit_return_final_copy_clean >>
  simp[] >>
  simp[structlit_return_memory_taint_frame] >>
  irule structlit_return_array_copy_clean >> simp[] >>
  simp[structlit_return_memory_taint_frame] >>
  irule structlit_return_array_store_clean >> simp[]
QED

Theorem structlit_return_early_instruction:
  !n. n < 13 ==>
    EL n (SND (structlit_callee_return_compiled F)).cs_current_insts =
    EL n (SND (structlit_callee_compiled F)).cs_current_insts
Proof
  rpt strip_tac >>
  mp_tac structlit_callee_return_expression_prefix >>
  disch_then (mp_tac o AP_TERM ``EL n : instruction list -> instruction``) >>
  simp[EL_TAKE]
QED

Theorem structlit_return_bytes_copy_clean:
  !tn i t. 224 <= i /\ i < 256 /\
    (!j. 384 <= j /\ j < 416 ==> j NOTIN tn.t_mem) ==>
    i NOTIN (step_taint
      (EL 8 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 8) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  simp[structlit_return_early_instruction, structlit_return_early_state] >>
  irule structlit_callee_bytes_copy_clean >> simp[]
QED

Theorem structlit_return_header_store_clean:
  !tn i t. 384 <= i /\ i < 416 ==>
    i NOTIN (step_taint
      (EL 2 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state 2) t tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  simp[structlit_return_early_instruction, structlit_return_early_state] >>
  irule structlit_callee_header_store_clean >> simp[]
QED

Theorem structlit_return_early_memory_frame:
  !n tn. MEM n [3;4;5;6;7] ==>
    !t. t = structlit_return_state (SUC n) ==>
    (step_taint
      (EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      (structlit_return_state n) t tn).t_mem = tn.t_mem
Proof
  rpt strip_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `n < 13 /\ n <= 13 /\ SUC n <= 13` by (gvs[] >> decide_tac) >>
  simp[structlit_return_early_instruction, structlit_return_early_state,
       structlit_callee_intermediate_memory_taint]
QED

Theorem structlit_return_store_segment:
  TAKE 14 (DROP 2 (SND (structlit_callee_return_compiled F)).cs_current_insts) =
    MAP (\n. EL n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      [2;3;4;5;6;7;8] ++
    TAKE 7 (DROP 9 (SND (structlit_callee_return_compiled F)).cs_current_insts)
Proof
  rewrite_tac[structlit_return_instructions] >> EVAL_TAC
QED

Theorem structlit_return_store_segment_first_header:
  !tn k j. j < 32 ==>
    64 + j NOTIN (structlit_callee_taint_run
      (TAKE 14 (DROP 2 (SND (structlit_callee_return_compiled F)).cs_current_insts))
      (structlit_return_state 2 with vs_inst_idx := k) tn).t_mem
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[structlit_return_store_segment, MAP, APPEND] >>
  simp[structlit_return_taint_run_step] >>
  irule structlit_return_suffix_first_header >> simp[] >>
  irule structlit_return_bytes_copy_clean >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[structlit_return_early_memory_frame] >>
  irule structlit_return_header_store_clean >> simp[]
QED

Theorem structlit_return_store_segment_array_header:
  !tn k j. j < 32 ==>
    j + 160 NOTIN (structlit_callee_taint_run
      (TAKE 14 (DROP 2 (SND (structlit_callee_return_compiled F)).cs_current_insts))
      (structlit_return_state 2 with vs_inst_idx := k) tn).t_mem
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[structlit_return_store_segment, MAP, APPEND] >>
  simp[structlit_return_taint_run_step] >>
  irule structlit_return_suffix_array_header >> simp[]
QED

Theorem structlit_return_initial_cursor:
  structlit_callee_initial = structlit_return_state 0 with vs_inst_idx := 0
Proof
  EVAL_TAC
QED

Theorem structlit_return_full_segment:
  TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts =
    MAP (\n. EL n (SND (structlit_callee_return_compiled F)).cs_current_insts) [0;1] ++
    TAKE 14 (DROP 2 (SND (structlit_callee_return_compiled F)).cs_current_insts)
Proof
  rewrite_tac[structlit_return_instructions] >> EVAL_TAC
QED

Theorem structlit_return_clean_headers:
  !tn j. j < 32 ==>
    j + 64 NOTIN (structlit_callee_taint_run
      (TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      structlit_callee_initial tn).t_mem /\
    j + 160 NOTIN (structlit_callee_taint_run
      (TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts)
      structlit_callee_initial tn).t_mem
Proof
  rpt gen_tac >> disch_tac >>
  rewrite_tac[structlit_return_full_segment, MAP, APPEND] >>
  once_rewrite_tac[structlit_return_initial_cursor] >>
  BETA_TAC >>
  dep_rewrite.DEP_REWRITE_TAC [structlit_return_taint_run_step] >>
  simp[] >>
  dep_rewrite.DEP_REWRITE_TAC [structlit_return_taint_run_step] >>
  simp[] >> conj_tac
  >- metis_tac[arithmeticTheory.ADD_COMM,
       structlit_return_store_segment_first_header] >>
  irule structlit_return_store_segment_array_header >> simp[]
QED


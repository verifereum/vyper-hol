(* Concrete variable-parameter return probe. Named compiler/state fixtures
   keep executable certificates small; no universal body judgment is assumed. *)
Theory bodyPtrStructLitVariableReturn
Ancestors bodyPtrStructLitReturnCertificate bodyPtrStructLitReturnBoundary
  fragGasSeqPtr finite_map ptrSafeRun ptrDiscipline venomInst typedCopyPtr bodyPtrStructLitGhostNormalize
  venomState venomExecSemantics instIdxIndep codegenRel contextCodegenRel list rich_list allocationPtr exprLoweringProps
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


Theorem structlit_variable_prov_1:
  structlit_variable_prov 1 =
    FEMPTY |+ ("return_buffer",(64,160)) |+ ("%0",(224,160))
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``1``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, structlit_variable_allocation_results] >>
  simp[structlit_variable_prov_def]
QED

Theorem structlit_variable_prov_2:
  structlit_variable_prov 2 =
    FEMPTY |+ ("return_buffer",(64,160)) |+ ("%0",(224,160))
      |+ ("%1",(384,32))
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``2``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_1,
       structlit_variable_instructions, structlit_return_instructions,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       structlit_variable_allocation_results]
QED

Theorem structlit_variable_prov_3:
  structlit_variable_prov 3 = structlit_variable_prov 2
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``3``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem structlit_variable_prov_4:
  structlit_variable_prov 4 =
    FEMPTY |+ ("return_buffer",(64,160)) |+ ("%0",(224,160))
      |+ ("%1",(384,32)) |+ ("%2",(224,160))
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``4``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_3,
       structlit_variable_prov_2, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem structlit_variable_prov_5:
  structlit_variable_prov 5 = structlit_variable_prov 4
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``5``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, structlit_variable_prov_4,
       fmap_EQ_THM, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem structlit_variable_prov_6:
  structlit_variable_prov 6 = structlit_variable_prov 4
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``6``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_5,
       structlit_variable_prov_4, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, first_prov_def, op_prov_def, mk_inst_def,
       fmap_EQ_THM, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem structlit_variable_prov_7:
  structlit_variable_prov 7 = structlit_variable_prov 4
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``7``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_6,
       structlit_variable_prov_4, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, fmap_EQ_THM, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem structlit_variable_prov_8:
  structlit_variable_prov 8 = structlit_variable_prov 4
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``8``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_7,
       structlit_variable_prov_4, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, first_prov_def, op_prov_def, mk_inst_def,
       fmap_EQ_THM, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem structlit_variable_prov_9:
  structlit_variable_prov 9 = structlit_variable_prov 4
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``9``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_8,
       structlit_variable_instructions, structlit_return_instructions,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem structlit_variable_prov_10:
  structlit_variable_prov 10 =
    FEMPTY |+ ("return_buffer",(64,160)) |+ ("%0",(224,160))
      |+ ("%1",(384,32)) |+ ("%2",(224,160)) |+ ("%7",(416,64))
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``10``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_9,
       structlit_variable_prov_4, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, structlit_variable_allocation_results]
QED

Theorem structlit_variable_prov_11:
  structlit_variable_prov 11 = structlit_variable_prov 10
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``11``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem structlit_variable_prov_12:
  structlit_variable_prov 12 =
    FEMPTY |+ ("return_buffer",(64,160)) |+ ("%0",(224,160))
      |+ ("%1",(384,32)) |+ ("%2",(224,160)) |+ ("%7",(416,64))
      |+ ("%8",(224,160))
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``12``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_11,
       structlit_variable_prov_10, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem structlit_variable_prov_13:
  structlit_variable_prov 13 = structlit_variable_prov 12
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``13``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_instructions,
       structlit_return_instructions, step_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem structlit_variable_prov_14:
  structlit_variable_prov 14 = structlit_variable_prov 12
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``14``])) >>
  simp[Once structlit_variable_prov_def, structlit_variable_prov_13,
       structlit_variable_instructions, structlit_return_instructions,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem structlit_variable_prefix_success:
  !n. n <= 14 ==>
    run_inst_seq (TAKE n (SND structlit_variable_compiled).cs_current_insts)
      structlit_variable_initial = OK (structlit_variable_state n)
Proof
  rpt strip_tac >> mp_tac structlit_variable_copy_run >>
  Cases_on `run_inst_seq
    (TAKE 14 (SND structlit_variable_compiled).cs_current_insts)
    structlit_variable_initial` >> simp[] >> strip_tac >>
  `TAKE 14 (SND structlit_variable_compiled).cs_current_insts =
    TAKE n (SND structlit_variable_compiled).cs_current_insts ++
    DROP n (TAKE 14 (SND structlit_variable_compiled).cs_current_insts)` by
    (qspec_then `n` (qspec_then
       `TAKE 14 (SND structlit_variable_compiled).cs_current_insts`
       mp_tac) TAKE_DROP >>
     pure_rewrite_tac[TAKE_TAKE_MIN] >>
     `MIN n 14 = n` by (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `TAKE 14 _ = _` (fn th =>
    qpat_x_assum `run_inst_seq _ _ = OK _`
      (mp_tac o ONCE_REWRITE_RULE [th])) >>
  disch_tac >> drule structlit_run_inst_seq_prefix_success >>
  strip_tac >> simp[structlit_variable_state_def]
QED

Theorem structlit_variable_steps:
  !n. MEM n [0;1;2;3;4;5;6;7;8;9;10;11;12;13] ==>
    step_inst_base (EL n (SND structlit_variable_compiled).cs_current_insts)
      (structlit_variable_state n) = OK (structlit_variable_state (SUC n))
Proof
  rpt gen_tac >> strip_tac >>
  `n < 14` by (gvs[] >> decide_tac) >>
  `n <= 14 /\ SUC n <= 14` by decide_tac >>
  qspec_then `n` mp_tac structlit_variable_prefix_success >> simp[] >> strip_tac >>
  qspec_then `SUC n` mp_tac structlit_variable_prefix_success >> simp[] >>
  `TAKE (SUC n) (SND structlit_variable_compiled).cs_current_insts =
    TAKE n (SND structlit_variable_compiled).cs_current_insts ++
    [EL n (SND structlit_variable_compiled).cs_current_insts]` by
    simp[TAKE_SUC, TAKE1_DROP, structlit_variable_instructions,
         structlit_return_instructions] >>
  pop_assum SUBST1_TAC >> drule run_inst_seq_append >>
  disch_then (rewrite_tac o single) >> simp[run_inst_seq_def] >>
  Cases_on `step_inst_base
    (EL n (SND structlit_variable_compiled).cs_current_insts)
    (structlit_variable_state n)` >> simp[]
QED

Theorem structlit_variable_initial_allocation_fields:
  structlit_variable_state 0 = structlit_variable_initial /\
  FLOOKUP (structlit_variable_state 0).vs_allocas 0 = NONE /\
  (structlit_variable_state 0).vs_alloca_next = 224 /\
  FLOOKUP (structlit_variable_state 1).vs_allocas 1 = NONE /\
  (structlit_variable_state 1).vs_alloca_next = 384
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_taint_1:
  structlit_variable_taint 1 = (structlit_variable_taint 0) with
    <| t_mem := (structlit_variable_taint 0).t_mem UNION {i | 224 <= i /\ i < 384};
       t_var := (structlit_variable_taint 0).t_var |+ ("%0",{}) |>
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``1``])) >>
  simp[Once structlit_variable_taint_def] >>
  mp_tac (Q.SPEC `0` structlit_variable_steps) >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  strip_tac >> drule_at Any fresh_alloca_ghost >>
  simp[structlit_variable_initial_allocation_fields] >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `structlit_variable_taint 0`] mp_tac) >>
  simp[]
QED

Theorem structlit_variable_taint_2:
  structlit_variable_taint 2 = (structlit_variable_taint 1) with
    <| t_mem := (structlit_variable_taint 1).t_mem UNION {i | 384 <= i /\ i < 416};
       t_var := (structlit_variable_taint 1).t_var |+ ("%1",{}) |>
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``2``])) >>
  simp[Once structlit_variable_taint_def] >>
  mp_tac (Q.SPEC `1` structlit_variable_steps) >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  strip_tac >> drule_at Any fresh_alloca_ghost >>
  simp[structlit_variable_initial_allocation_fields] >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `structlit_variable_taint 1`] mp_tac) >>
  simp[]
QED

Theorem structlit_variable_store_2_fields:
  lookup_var "%1" (structlit_variable_state 2) = SOME 384w
Proof
  EVAL_TAC
QED

Theorem structlit_variable_store_2_state:
  structlit_variable_state 3 = mstore 384 0w (structlit_variable_state 2)
Proof
  mp_tac (Q.SPEC `2` structlit_variable_steps) >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  simp[Once step_inst_base_def, mk_inst_def] >>
  simp[exec_write2_def, eval_operand_def, structlit_variable_store_2_fields]
QED

Theorem structlit_variable_taint_3:
  (structlit_variable_taint 3).t_mem =
    (structlit_variable_taint 2).t_mem DIFF {i | 384 <= i /\ i < 416} /\
  (structlit_variable_taint 3).t_var = (structlit_variable_taint 2).t_var
Proof
  pure_rewrite_tac[numLib.num_CONV ``3``] >>
  simp[Ntimes structlit_variable_taint_def 2, structlit_variable_instructions,
       structlit_return_instructions] >>
  `lookup_var "%1" (structlit_variable_state 2) = SOME 384w` by
    simp[structlit_variable_store_2_fields] >>
  drule mstore_ghost_frame >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `structlit_variable_taint 2`] mp_tac) >>
  disch_then (qspec_then `2` mp_tac) >>
  disch_then (qspec_then `Lit 0w` mp_tac) >>
  simp[eval_operand_def, op_taint_def, GSYM structlit_variable_store_2_state]
QED

Theorem structlit_variable_header_clean_3:
  !i. 384 <= i /\ i < 416 ==> i NOTIN (structlit_variable_taint 3).t_mem
Proof
  simp[structlit_variable_taint_3]
QED

Theorem structlit_variable_add_3_frame:
  (structlit_variable_state 4).vs_allocas = (structlit_variable_state 3).vs_allocas /\
  (structlit_variable_state 4).vs_fmp = (structlit_variable_state 3).vs_fmp
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_taint_4:
  (structlit_variable_taint 4).t_mem = (structlit_variable_taint 3).t_mem /\
  (structlit_variable_taint 4).t_var = (structlit_variable_taint 3).t_var |+ ("%2",{})
Proof
  pure_rewrite_tac[numLib.num_CONV ``4``] >>
  simp[Ntimes structlit_variable_taint_def 2, structlit_variable_instructions,
       structlit_return_instructions] >>
  conj_tac
  >- (irule structlit_step_taint_memory_frame >>
      simp[structlit_variable_add_3_frame, step_writes_def,
           source_memory_write_ranges_def, written_taint_def, mk_inst_def]) >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
       eval_operand_def] >>
  Cases_on `lookup_var "%0" (structlit_variable_state 3)` >> simp[]
QED

Theorem structlit_variable_load_4_fields:
  lookup_var "%1" (structlit_variable_state 4) = SOME 384w
Proof
  EVAL_TAC
QED

Theorem structlit_variable_load_4_clean:
  op_taint (structlit_variable_taint 5) (Var "%3") = {}
Proof
  pure_rewrite_tac[numLib.num_CONV ``5``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions, step_taint_def, mk_inst_def,
       set_var_taint_def, out_taint_def, eval_operand_def,
       structlit_variable_load_4_fields, op_taint_def, FLOOKUP_UPDATE,
       structlit_variable_taint_4, mem_word_taint_def, pred_setTheory.EXTENSION] >>
  gen_tac >> Cases_on `x < 32` >> simp[] >>
  irule structlit_variable_header_clean_3 >> decide_tac
QED

Theorem structlit_variable_pure_fields:
  !n. MEM n [4;5;6;7] ==>
    (structlit_variable_state (SUC n)).vs_allocas =
      (structlit_variable_state n).vs_allocas /\
    (structlit_variable_state (SUC n)).vs_fmp =
      (structlit_variable_state n).vs_fmp
Proof
  rpt gen_tac >> simp[] >> strip_tac >> gvs[] >> conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_pure_memory_frame:
  !n. MEM n [4;5;6;7] ==>
    (structlit_variable_taint (SUC n)).t_mem =
      (structlit_variable_taint n).t_mem
Proof
  rpt strip_tac >> simp[Once structlit_variable_taint_def] >>
  irule structlit_step_taint_memory_frame >>
  drule structlit_variable_pure_fields >> strip_tac >> simp[] >>
  gvs[] >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  simp[step_writes_def, source_memory_write_ranges_def,
       written_taint_def, mk_inst_def]
QED

Theorem structlit_variable_arithmetic_clean:
  op_taint (structlit_variable_taint 6) (Var "%4") = {} /\
  op_taint (structlit_variable_taint 7) (Var "%5") = {} /\
  op_taint (structlit_variable_taint 8) (Var "%6") = {}
Proof
  rpt conj_tac >>
  pure_rewrite_tac[numLib.num_CONV ``6``, numLib.num_CONV ``7``,
                   numLib.num_CONV ``8``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
       op_taint_def, FLOOKUP_UPDATE, eval_operand_def] >>
  BasicProvers.CASE_TAC >> simp[]
QED

Theorem structlit_variable_memory_8:
  (structlit_variable_taint 8).t_mem = {i | 64 <= i /\ i < 384}
Proof
  map_every (fn n => qspec_then n (assume_tac o SRULE [])
    structlit_variable_pure_memory_frame) [`4`, `5`, `6`, `7`] >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[structlit_variable_taint_4, structlit_variable_taint_3,
       structlit_variable_taint_2, structlit_variable_taint_1] >>
  simp[Once structlit_variable_taint_def, entry_taint_def,
       pred_setTheory.EXTENSION] >> decide_tac
QED

Theorem structlit_variable_copy_8_fields:
  lookup_var "%2" (structlit_variable_state 8) = SOME 224w /\
  lookup_var "%1" (structlit_variable_state 8) = SOME 384w /\
  lookup_var "%6" (structlit_variable_state 8) = SOME 32w /\
  (structlit_variable_state 9).vs_allocas = (structlit_variable_state 8).vs_allocas /\
  (structlit_variable_state 9).vs_fmp = (structlit_variable_state 8).vs_fmp
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_memory_9:
  (structlit_variable_taint 9).t_mem =
    {i | 64 <= i /\ i < 224 \/ 256 <= i /\ i < 384}
Proof
  `new_site_bytes (structlit_variable_state 8) (structlit_variable_state 9) = {}` by
    (irule structlit_new_site_bytes_unchanged >> simp[structlit_variable_copy_8_fields]) >>
  pure_rewrite_tac[numLib.num_CONV ``9``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       eval_operand_def, structlit_variable_copy_8_fields, mk_inst_def,
       structlit_variable_memory_8, range_bytes_def, pred_setTheory.EXTENSION] >>
  decide_tac
QED

Theorem structlit_variable_allocation_9_fields:
  FLOOKUP (structlit_variable_state 9).vs_allocas 9 = NONE /\
  (structlit_variable_state 9).vs_alloca_next = 416
Proof
  conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_taint_10:
  structlit_variable_taint 10 = (structlit_variable_taint 9) with
    <| t_mem := (structlit_variable_taint 9).t_mem UNION {i | 416 <= i /\ i < 480};
       t_var := (structlit_variable_taint 9).t_var |+ ("%7",{}) |>
Proof
  CONV_TAC (LAND_CONV (REWRITE_CONV [numLib.num_CONV ``10``])) >>
  simp[Once structlit_variable_taint_def] >>
  mp_tac (Q.SPEC `9` structlit_variable_steps) >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  strip_tac >> drule_at Any fresh_alloca_ghost >>
  simp[structlit_variable_allocation_9_fields] >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `structlit_variable_taint 9`] mp_tac) >>
  simp[]
QED

Theorem structlit_variable_store_10_fields:
  lookup_var "%7" (structlit_variable_state 10) = SOME 416w
Proof
  EVAL_TAC
QED

Theorem structlit_variable_store_10_state:
  structlit_variable_state 11 = mstore 416 0w (structlit_variable_state 10)
Proof
  mp_tac (Q.SPEC `10` structlit_variable_steps) >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  simp[Once step_inst_base_def, mk_inst_def] >>
  simp[exec_write2_def, eval_operand_def, structlit_variable_store_10_fields]
QED

Theorem structlit_variable_memory_11:
  (structlit_variable_taint 11).t_mem =
    {i | 64 <= i /\ i < 224 \/ 256 <= i /\ i < 384 \/ 448 <= i /\ i < 480}
Proof
  pure_rewrite_tac[numLib.num_CONV ``11``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions] >>
  `lookup_var "%7" (structlit_variable_state 10) = SOME 416w` by
    simp[structlit_variable_store_10_fields] >>
  drule mstore_ghost_frame >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `structlit_variable_taint 10`] mp_tac) >>
  disch_then (qspec_then `10` mp_tac) >>
  disch_then (qspec_then `Lit 0w` mp_tac) >>
  simp[eval_operand_def, op_taint_def, GSYM structlit_variable_store_10_state] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp[structlit_variable_taint_10, structlit_variable_memory_9,
       pred_setTheory.EXTENSION] >> decide_tac
QED

Theorem structlit_variable_add_11_frame:
  (structlit_variable_state 12).vs_allocas = (structlit_variable_state 11).vs_allocas /\
  (structlit_variable_state 12).vs_fmp = (structlit_variable_state 11).vs_fmp
Proof
  conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_memory_12:
  (structlit_variable_taint 12).t_mem = (structlit_variable_taint 11).t_mem
Proof
  pure_rewrite_tac[numLib.num_CONV ``12``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions] >>
  irule structlit_step_taint_memory_frame >>
  simp[structlit_variable_add_11_frame, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, mk_inst_def]
QED

Theorem structlit_variable_copy_12_fields:
  lookup_var "%8" (structlit_variable_state 12) = SOME 320w /\
  lookup_var "%7" (structlit_variable_state 12) = SOME 416w /\
  (structlit_variable_state 13).vs_allocas = (structlit_variable_state 12).vs_allocas /\
  (structlit_variable_state 13).vs_fmp = (structlit_variable_state 12).vs_fmp
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_memory_13:
  (structlit_variable_taint 13).t_mem =
    {i | 64 <= i /\ i < 224 \/ 256 <= i /\ i < 320 \/
         352 <= i /\ i < 384 \/ 448 <= i /\ i < 480}
Proof
  `new_site_bytes (structlit_variable_state 12) (structlit_variable_state 13) = {}` by
    (irule structlit_new_site_bytes_unchanged >> simp[structlit_variable_copy_12_fields]) >>
  pure_rewrite_tac[numLib.num_CONV ``13``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       eval_operand_def, structlit_variable_copy_12_fields, mk_inst_def,
       structlit_variable_memory_12, structlit_variable_memory_11,
       range_bytes_def, pred_setTheory.EXTENSION] >>
  Omega.OMEGA_TAC
QED

Theorem structlit_variable_copy_13_fields:
  lookup_var "return_buffer" (structlit_variable_state 13) = SOME 64w /\
  lookup_var "%0" (structlit_variable_state 13) = SOME 224w /\
  (structlit_variable_state 14).vs_allocas = (structlit_variable_state 13).vs_allocas /\
  (structlit_variable_state 14).vs_fmp = (structlit_variable_state 13).vs_fmp
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem structlit_variable_memory_14:
  (structlit_variable_taint 14).t_mem =
    {i | 96 <= i /\ i < 160 \/ 192 <= i /\ i < 224 \/
         256 <= i /\ i < 320 \/ 352 <= i /\ i < 384 \/ 448 <= i /\ i < 480}
Proof
  `new_site_bytes (structlit_variable_state 13) (structlit_variable_state 14) = {}` by
    (irule structlit_new_site_bytes_unchanged >> simp[structlit_variable_copy_13_fields]) >>
  pure_rewrite_tac[numLib.num_CONV ``14``] >>
  simp[Once structlit_variable_taint_def, structlit_variable_instructions,
       structlit_return_instructions] >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       eval_operand_def, structlit_variable_copy_13_fields, mk_inst_def,
       structlit_variable_memory_13, range_bytes_def, pred_setTheory.EXTENSION] >>
  gen_tac >> eq_tac
  >- (strip_tac >> gvs[] >> decide_tac) >>
  strip_tac >> simp[] >>
  qexists_tac `x - 64` >> decide_tac
QED

Theorem structlit_variable_output_clean:
  !n. MEM n [0;1;2;3;4;5;6;7;8;9;10;11;12;13] ==>
    out_taint (structlit_variable_taint n)
      (EL n (SND structlit_variable_compiled).cs_current_insts)
      (structlit_variable_state n) = {}
Proof
  rpt gen_tac >> simp[] >> strip_tac >> gvs[] >>
  simp[structlit_variable_instructions, structlit_return_instructions] >>
  simp[out_taint_def, mk_inst_def, eval_operand_def,
       structlit_variable_load_4_fields]
  >~ [`mem_word_taint _ _ = {}`]
  >- (simp[structlit_variable_taint_4, mem_word_taint_def,
           pred_setTheory.EXTENSION] >>
      gen_tac >> Cases_on `x < 32` >> simp[] >>
      irule structlit_variable_header_clean_3 >> decide_tac) >>
  BasicProvers.CASE_TAC >> simp[]
QED

Theorem structlit_variable_vars_clean:
  !n x. n <= 14 ==> op_taint (structlit_variable_taint n) (Var x) = {}
Proof
  Induct >> simp[structlit_variable_taint_def, entry_taint_def, op_taint_def] >>
  rpt strip_tac >>
  `n < 14 /\ n <= 14` by decide_tac >>
  `MEM n [0;1;2;3;4;5;6;7;8;9;10;11;12;13]` by
    (simp[] >> decide_tac) >>
  drule structlit_variable_output_clean >> strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[op_taint_def] >> strip_tac >>
  simp[Once structlit_variable_taint_def, step_taint_def] >>
  Cases_on `(EL n (SND structlit_variable_compiled).cs_current_insts).inst_outputs` >>
  simp[set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  rename1 `_ = h::outs` >> Cases_on `outs` >>
  simp[set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `h = x` >> simp[] >>
  Cases_on `x = h'` >> simp[] >> Cases_on `MEM x t` >> simp[]
QED

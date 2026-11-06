Theory bodyPtrPopFullFrameExecution
Ancestors
  bodyPtrPopFullFrameEntry bodyPtrPopFullFrameProbe bodyPtrPopFullFrameRuntime
  fragGasSeqPtr ptrDiscipline venomInst venomState vyperValue

Theorem pop_full_frame_compiled_value:
  FST pop_full_frame_compiled =
    LocatedValue (BaseT (UintT 256))
      <| ptr_operand := Var "%13"; ptr_location := LocStorage; ptr_buf := NONE |>
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_full_frame_compiled_pc:
  (SND pop_full_frame_compiled).cs_current_bb = "internal 0 take()_runtime" /\
  LENGTH (SND pop_full_frame_compiled).cs_current_insts = 11
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

(* This is precisely the expression slice, excluding the unwrap and RET. *)
Definition pop_full_frame_code_def:
  pop_full_frame_code =
    [mk_inst 10 SLOAD [Lit 0w] ["%7"];
     mk_inst 11 ISZERO [Var "%7"] ["%8"];
     mk_inst 12 ISZERO [Var "%8"] ["%9"];
     mk_inst 13 ASSERT [Var "%9"] [];
     mk_inst 14 SUB [Var "%7"; Lit 1w] ["%10"];
     mk_inst 15 SSTORE [Lit 0w; Var "%10"] [];
     mk_inst 16 ADD [Lit 0w; Lit 1w] ["%11"];
     mk_inst 17 MUL [Var "%10"; Lit 1w] ["%12"];
     mk_inst 18 ADD [Var "%11"; Var "%12"] ["%13"]]
End

(* Concrete endpoint record: the single length store and seven SSA results. *)
Definition pop_full_frame_end_def:
  pop_full_frame_end = pop_full_frame_ss with
    <| vs_vars := pop_full_frame_ss.vs_vars |+
         ("%7",1w) |+ ("%8",0w) |+ ("%9",1w) |+ ("%10",0w) |+
         ("%11",1w) |+ ("%12",0w) |+ ("%13",1w);
       vs_accounts := (0w =+
         ((pop_full_frame_ss.vs_accounts 0w) with storage :=
           (0w =+ 0w) (pop_full_frame_ss.vs_accounts 0w).storage))
         pop_full_frame_ss.vs_accounts |>
End

Theorem pop_full_frame_run:
  run_inst_seq pop_full_frame_code pop_full_frame_ss = OK pop_full_frame_end
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_full_frame_seq_ptr:
  inst_seq_ptr (cx_dead pop_full_frame_cx) 0 pop_full_frame_context
    pop_full_frame_fn PG pop_full_frame_G entry_taint
    pop_full_frame_code pop_full_frame_ss pop_full_frame_G
    (entry_taint with t_var := FEMPTY |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{}))
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``ptr_inst_ok``, ``pop_full_frame_context``, ``pop_full_frame_fn``,
     ``cx_dead``]) >>
  simp_tac bool_ss [ptrSafeRunTheory.ptr_inst_ok_def,
                    pop_full_frame_no_dalloca] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``cx_dead``, ``pop_full_frame_context``, ``pop_full_frame_fn``]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt conj_tac >> gen_tac >> Cases_on `op` >> simp[] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem pop_full_frame_code_counts:
  LENGTH pop_full_frame_code = 9 /\
  FILTER (\i. i.inst_opcode = GAS) pop_full_frame_code = [] /\
  pop_full_frame_ss.vs_inst_idx = 2
Proof
  EVAL_TAC
QED

Theorem pop_full_frame_execution:
  gas_path_ptr (cx_dead pop_full_frame_cx) 0 pop_full_frame_context
    pop_full_frame_fn PG pop_full_frame_G entry_taint pop_full_frame_ss 0
    pop_full_frame_G
    (entry_taint with t_var := FEMPTY |+ ("%7",{}) |+ ("%8",{}) |+
      ("%9",{}) |+ ("%10",{}) |+ ("%11",{}) |+ ("%12",{}) |+ ("%13",{}))
    (OK (pop_full_frame_end with vs_inst_idx := 11))
Proof
  qspecl_then [`pop_full_frame_code`, `pop_full_frame_ss`,
                `pop_full_frame_end`]
    (irule o SRULE [pop_full_frame_run, pop_full_frame_code_counts])
    run_inst_seq_gas_path_ptr >>
  simp[pop_full_frame_seq_ptr] >>
  simp[pop_full_frame_blocks, pop_full_frame_code_def,
       pop_full_frame_ss_def, init_venom_state_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC >> simp[]
QED

Theorem pop_full_frame_execution_pc:
  (pop_full_frame_end with vs_inst_idx := 11).vs_current_bb =
    (SND pop_full_frame_compiled).cs_current_bb /\
  (pop_full_frame_end with vs_inst_idx := 11).vs_inst_idx =
    LENGTH (SND pop_full_frame_compiled).cs_current_insts /\
  eval_operand (Var "%13") pop_full_frame_end = SOME 1w
Proof
  simp[pop_full_frame_compiled_pc, pop_full_frame_end_def,
       pop_full_frame_ss_def, init_venom_state_def] >> EVAL_TAC
QED

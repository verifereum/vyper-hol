Theory bodyPtrBytestringBuiltinsOrderRun
Ancestors
  bodyPtrBytestringBuiltinsOrderProbe bodyPtrBytestringBuiltinsEndpoint
  vyperCompiler compileVyper

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:160)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``];

(* Concrete compilation fixture; the input array occupies bytes 128..223. *)
Definition order_run_env_def:
  order_run_env =
    (build_compile_env [] External Nonpayable "f"
      [("arr", ArrayT (BaseT AddressT) (Dynamic 2))] NoneT [] F)
    with ce_vars := FEMPTY |+ ("arr", MemLoc 128 96)
End

(* Keep the actual compiler output, rather than a hand-written program. *)
Definition order_run_compiled_def:
  order_run_compiled = compile_expr order_run_env
    (BaseT (BytesT (Dynamic 1))) order_probe_expr
    (initial_compile_state "entry")
End

Theorem order_run_compilation:
  FST order_run_compiled =
    LocatedValue (BaseT (BytesT (Dynamic 1)))
      <|ptr_operand := Var "%1"; ptr_location := LocMemory; ptr_buf := NONE|> /\
  (SND order_run_compiled).cs_blocks = [] /\
  (SND order_run_compiled).cs_current_bb = "entry" /\
  MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
    (SND order_run_compiled).cs_current_insts =
    [(MLOAD,[Lit 128w],["%0"]);
     (ALLOCA,[Lit 64w],["%1"]);
     (ADD,[Var "%1";Lit 32w],["%2"]);
     (MLOAD,[Lit 128w],["%3"]);
     (ISZERO,[Var "%3"],["%4"]);
     (ISZERO,[Var "%4"],["%5"]);
     (ASSERT,[Var "%5"],[]);
     (SUB,[Var "%3";Lit 1w],["%6"]);
     (MSTORE,[Lit 128w;Var "%6"],[]);
     (ADD,[Lit 128w;Lit 32w],["%7"]);
     (MUL,[Var "%6";Lit 32w],["%8"]);
     (ADD,[Var "%7";Var "%8"],["%9"]);
     (MLOAD,[Var "%9"],["%10"]);
     (EXTCODESIZE,[Var "%10"],["%11"]);
     (ADD,[Var "%0";Lit 1w],["%12"]);
     (LT,[Var "%12";Var "%0"],["%13"]);
     (GT,[Var "%12";Var "%11"],["%14"]);
     (OR,[Var "%13";Var "%14"],["%15"]);
     (ISZERO,[Var "%15"],["%16"]);
     (ASSERT,[Var "%16"],[]);
     (EXTCODECOPY,[Var "%10";Var "%2";Var "%0";Lit 1w],[]);
     (MSTORE,[Var "%1";Lit 1w],[])]
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
    fcpLib.INDEX_CONV ``dimindex(:8)``]
QED

(* Observe exactly the emitted straight-line fragment at a STOP continuation. *)
Definition order_run_fn_def:
  order_run_fn = mk_raw_function "f"
    [<|bb_label := "entry";
       bb_instructions := (SND order_run_compiled).cs_current_insts ++
         [<|inst_id := 22; inst_opcode := STOP; inst_operands := []; inst_outputs := []|>]|>]
End

(* The array is disjoint from the output allocation at 256. *)
Definition order_run_start_def:
  order_run_start =
    (init_venom_state "entry") with
      <|vs_memory := REPLICATE 159 0w ++ [2w] ++
                      REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [2w];
        vs_alloca_next := 256;
        vs_accounts := update_account 2w
          (empty_account_state with code := [10w;20w;30w]) empty_accounts|>
End

Theorem order_run_start_array:
  mload 128 order_run_start = 2w /\
  mload 160 order_run_start = 1w /\
  mload 192 order_run_start = 2w
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
    fcpLib.INDEX_CONV ``dimindex(:8)``]
QED


Theorem order_run_instructions:
  (SND order_run_compiled).cs_current_insts =
    [mk_inst 0 MLOAD [Lit 128w] ["%0"];
     mk_inst 1 ALLOCA [Lit 64w] ["%1"];
     mk_inst 2 ADD [Var "%1";Lit 32w] ["%2"];
     mk_inst 3 MLOAD [Lit 128w] ["%3"];
     mk_inst 4 ISZERO [Var "%3"] ["%4"];
     mk_inst 5 ISZERO [Var "%4"] ["%5"];
     mk_inst 6 ASSERT [Var "%5"] [];
     mk_inst 7 SUB [Var "%3";Lit 1w] ["%6"];
     mk_inst 8 MSTORE [Lit 128w;Var "%6"] [];
     mk_inst 9 ADD [Lit 128w;Lit 32w] ["%7"];
     mk_inst 10 MUL [Var "%6";Lit 32w] ["%8"];
     mk_inst 11 ADD [Var "%7";Var "%8"] ["%9"];
     mk_inst 12 MLOAD [Var "%9"] ["%10"];
     mk_inst 13 EXTCODESIZE [Var "%10"] ["%11"];
     mk_inst 14 ADD [Var "%0";Lit 1w] ["%12"];
     mk_inst 15 LT [Var "%12";Var "%0"] ["%13"];
     mk_inst 16 GT [Var "%12";Var "%11"] ["%14"];
     mk_inst 17 OR [Var "%13";Var "%14"] ["%15"];
     mk_inst 18 ISZERO [Var "%15"] ["%16"];
     mk_inst 19 ASSERT [Var "%16"] [];
     mk_inst 20 EXTCODECOPY [Var "%10";Var "%2";Var "%0";Lit 1w] [];
     mk_inst 21 MSTORE [Var "%1";Lit 1w] []]
Proof
  EVAL_TAC >> simp[]
QED

(* Explicit step snapshots prevent repeated evaluation of preceding instructions. *)
Definition order_run_s1_def:
  order_run_s1 = order_run_start with
    <|vs_vars := FEMPTY |+ ("%0",2w); vs_inst_idx := 1|>
End

Theorem order_run_step0:
  step_inst_base (mk_inst 0 MLOAD [Lit 128w] ["%0"]) order_run_start =
    OK (order_run_s1 with vs_inst_idx := 0)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256, order_run_start_array] >>
  simp[venomStateTheory.update_var_def, order_run_s1_def, order_run_start_def,
       venomStateTheory.init_venom_state_def]
QED

(* Snapshot after allocation: no memory is written by ALLOCA. *)
Definition order_run_s2_def:
  order_run_s2 = order_run_start with
    <|vs_vars := FEMPTY |+ ("%0",2w) |+ ("%1",256w);
      vs_inst_idx := 2; vs_allocas := FEMPTY |+ (1,(256,64));
      vs_alloca_next := 320|>
End

Theorem order_run_step1:
  step_inst_base (mk_inst 1 ALLOCA [Lit 64w] ["%1"]) order_run_s1 =
    OK (order_run_s2 with vs_inst_idx := 1)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256] >>
  simp[order_run_s1_def, order_run_s2_def,
       venomStateTheory.update_var_def] >>
  simp[order_run_start_def, venomStateTheory.init_venom_state_def]
QED

(* Snapshot after computing the output payload address. *)
Definition order_run_s3_def:
  order_run_s3 = order_run_s2 with
    <|vs_vars := order_run_s2.vs_vars |+ ("%2",288w); vs_inst_idx := 3|>
End

Theorem order_run_step2:
  step_inst_base (mk_inst 2 ADD [Var "%1";Lit 32w] ["%2"]) order_run_s2 =
    OK (order_run_s3 with vs_inst_idx := 2)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s3_def, order_run_s2_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.word_add_n2w]
QED

(* Second length read still precedes the mutation of the array. *)
Definition order_run_s4_def:
  order_run_s4 = order_run_s3 with
    <|vs_vars := order_run_s3.vs_vars |+ ("%3",2w); vs_inst_idx := 4|>
End

Theorem order_run_s3_array:
  mload 128 order_run_s3 = 2w
Proof
  mp_tac (cj 1 order_run_start_array) >>
  simp[order_run_s3_def, order_run_s2_def, venomStateTheory.mload_def,
       venomStateTheory.read_memory_def]
QED

Theorem order_run_step3:
  step_inst_base (mk_inst 3 MLOAD [Lit 128w] ["%3"]) order_run_s3 =
    OK (order_run_s4 with vs_inst_idx := 3)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256, order_run_s3_array] >>
  simp[order_run_s4_def, venomStateTheory.update_var_def, order_run_s3_def]
QED

(* Boolean tests of the nonempty array length. *)
Definition order_run_s5_def:
  order_run_s5 = order_run_s4 with
    <|vs_vars := order_run_s4.vs_vars |+ ("%4",0w); vs_inst_idx := 5|>
End

Theorem order_run_step4:
  step_inst_base (mk_inst 4 ISZERO [Var "%3"] ["%4"]) order_run_s4 =
    OK (order_run_s5 with vs_inst_idx := 4)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s5_def, order_run_s4_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, venomExecSemanticsTheory.bool_to_word_def,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

(* Assertion operand after the second zero test. *)
Definition order_run_s6_def:
  order_run_s6 = order_run_s5 with
    <|vs_vars := order_run_s5.vs_vars |+ ("%5",1w); vs_inst_idx := 6|>
End

Theorem order_run_step5:
  step_inst_base (mk_inst 5 ISZERO [Var "%4"] ["%5"]) order_run_s5 =
    OK (order_run_s6 with vs_inst_idx := 5)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s6_def, order_run_s5_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, venomExecSemanticsTheory.bool_to_word_def]
QED

(* Successful assertion changes only the instruction cursor. *)
Definition order_run_s7_def:
  order_run_s7 = order_run_s6 with vs_inst_idx := 7
End

Theorem order_run_step6:
  step_inst_base (mk_inst 6 ASSERT [Var "%5"] []) order_run_s6 =
    OK (order_run_s7 with vs_inst_idx := 6)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s7_def, order_run_s6_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

(* Decremented length is one, before it is stored back to the array. *)
Definition order_run_s8_def:
  order_run_s8 = order_run_s7 with
    <|vs_vars := order_run_s7.vs_vars |+ ("%6",1w); vs_inst_idx := 8|>
End

Theorem order_run_step7:
  step_inst_base (mk_inst 7 SUB [Var "%3";Lit 1w] ["%6"]) order_run_s7 =
    OK (order_run_s8 with vs_inst_idx := 7)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s8_def, order_run_s7_def, order_run_s6_def,
       order_run_s5_def, order_run_s4_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV)
QED

(* Explicit memory update for Pop's length store; no execution is hidden here. *)
Definition order_run_s9_def:
  order_run_s9 = order_run_s8 with
    <|vs_memory := TAKE 128 order_run_s8.vs_memory ++
        word_to_bytes (1w:bytes32) T ++ DROP 160 order_run_s8.vs_memory;
      vs_inst_idx := 9|>
End

Theorem order_run_s8_memory_length:
  LENGTH order_run_s8.vs_memory = 224
Proof
  simp[order_run_s8_def, order_run_s7_def, order_run_s6_def,
       order_run_s5_def, order_run_s4_def, order_run_s3_def,
       order_run_s2_def, order_run_start_def]
QED

Theorem order_run_step8:
  step_inst_base (mk_inst 8 MSTORE [Lit 128w;Var "%6"] []) order_run_s8 =
    OK (order_run_s9 with vs_inst_idx := 8)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%6" order_run_s8 = SOME 1w` by
    simp[order_run_s8_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[venomStateTheory.mstore_def, order_run_s8_memory_length,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  simp[order_run_s9_def, order_run_s8_def]
QED

(* Explicit address arithmetic snapshots for the popped element. *)
Definition order_run_s10_def:
  order_run_s10 = order_run_s9 with
    <|vs_vars := order_run_s9.vs_vars |+ ("%7",160w); vs_inst_idx := 10|>
End

Theorem order_run_step9:
  step_inst_base (mk_inst 9 ADD [Lit 128w;Lit 32w] ["%7"]) order_run_s9 =
    OK (order_run_s10 with vs_inst_idx := 9)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.word_add_n2w] >>
  simp[order_run_s10_def, order_run_s9_def, venomStateTheory.update_var_def]
QED

Definition order_run_s11_def:
  order_run_s11 = order_run_s10 with
    <|vs_vars := order_run_s10.vs_vars |+ ("%8",32w); vs_inst_idx := 11|>
End

Theorem order_run_step10:
  step_inst_base (mk_inst 10 MUL [Var "%6";Lit 32w] ["%8"]) order_run_s10 =
    OK (order_run_s11 with vs_inst_idx := 10)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%6" order_run_s10 = SOME 1w` by
    simp[order_run_s10_def, order_run_s9_def, order_run_s8_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s11_def, order_run_s10_def, venomStateTheory.update_var_def]
QED

Definition order_run_s12_def:
  order_run_s12 = order_run_s11 with
    <|vs_vars := order_run_s11.vs_vars |+ ("%9",192w); vs_inst_idx := 12|>
End

Theorem order_run_step11:
  step_inst_base (mk_inst 11 ADD [Var "%7";Var "%8"] ["%9"]) order_run_s11 =
    OK (order_run_s12 with vs_inst_idx := 11)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s12_def, order_run_s11_def, order_run_s10_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.word_add_n2w]
QED

(* Pop loads the last array element, whose address is two. *)
Definition order_run_s13_def:
  order_run_s13 = order_run_s12 with
    <|vs_vars := order_run_s12.vs_vars |+ ("%10",2w); vs_inst_idx := 13|>
End

Theorem order_run_s12_array:
  mload 192 order_run_s12 = 2w
Proof
  simp[venomStateTheory.mload_def, venomStateTheory.read_memory_def,
       order_run_s12_def, order_run_s11_def, order_run_s10_def,
       order_run_s9_def] >>
  simp[order_run_s8_def, order_run_s7_def, order_run_s6_def,
       order_run_s5_def, order_run_s4_def, order_run_s3_def,
       order_run_s2_def] >>
  simp[order_run_start_def] >> EVAL_TAC
QED

Theorem order_run_step12:
  step_inst_base (mk_inst 12 MLOAD [Var "%9"] ["%10"]) order_run_s12 =
    OK (order_run_s13 with vs_inst_idx := 12)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%9" order_run_s12 = SOME 192w` by
    simp[order_run_s12_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
       order_run_s12_array] >>
  simp[order_run_s13_def, order_run_s12_def, venomStateTheory.update_var_def]
QED

(* External code length for the popped address. *)
Definition order_run_s14_def:
  order_run_s14 = order_run_s13 with
    <|vs_vars := order_run_s13.vs_vars |+ ("%11",3w); vs_inst_idx := 14|>
End

Theorem order_run_s13_accounts:
  order_run_s13.vs_accounts = order_run_start.vs_accounts
Proof
  simp[order_run_s13_def, order_run_s12_def, order_run_s11_def] >>
  simp[order_run_s10_def, order_run_s9_def, order_run_s8_def] >>
  simp[order_run_s7_def, order_run_s6_def, order_run_s5_def] >>
  simp[order_run_s4_def, order_run_s3_def, order_run_s2_def]
QED

Theorem order_run_step13:
  step_inst_base (mk_inst 13 EXTCODESIZE [Var "%10"] ["%11"]) order_run_s13 =
    OK (order_run_s14 with vs_inst_idx := 13)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%10" order_run_s13 = SOME 2w` by
    simp[order_run_s13_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s13_accounts] >>
  `LENGTH (lookup_account (2w:address) order_run_start.vs_accounts).code = 3` by
    EVAL_TAC >>
  simp[order_run_s14_def, order_run_s13_def, venomStateTheory.update_var_def]
QED

(* Bounds are checked using the length read before Pop. *)
Definition order_run_s15_def:
  order_run_s15 = order_run_s14 with
    <|vs_vars := order_run_s14.vs_vars |+ ("%12",3w); vs_inst_idx := 15|>
End

Theorem order_run_s14_start_operand:
  lookup_var "%0" order_run_s14 = SOME 2w
Proof
  simp[venomStateTheory.lookup_var_def, order_run_s14_def,
       order_run_s13_def, order_run_s12_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s11_def, order_run_s10_def, order_run_s9_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s8_def, order_run_s7_def, order_run_s6_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s5_def, order_run_s4_def, order_run_s3_def,
       order_run_s2_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_run_step14:
  step_inst_base (mk_inst 14 ADD [Var "%0";Lit 1w] ["%12"]) order_run_s14 =
    OK (order_run_s15 with vs_inst_idx := 14)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_run_s14_start_operand,
       wordsTheory.word_add_n2w] >>
  simp[order_run_s15_def, order_run_s14_def, venomStateTheory.update_var_def]
QED

(* The end bound does not overflow the original start. *)
Definition order_run_s16_def:
  order_run_s16 = order_run_s15 with
    <|vs_vars := order_run_s15.vs_vars |+ ("%13",0w); vs_inst_idx := 16|>
End

Theorem order_run_step15:
  step_inst_base (mk_inst 15 LT [Var "%12";Var "%0"] ["%13"]) order_run_s15 =
    OK (order_run_s16 with vs_inst_idx := 15)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%12" order_run_s15 = SOME 3w` by
    simp[order_run_s15_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_var "%0" order_run_s15 = SOME 2w` by
    (mp_tac order_run_s14_start_operand >>
     simp[order_run_s15_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[] >>
  simp[order_run_s16_def, order_run_s15_def, venomStateTheory.update_var_def]
QED

(* The end bound equals the external code size. *)
Definition order_run_s17_def:
  order_run_s17 = order_run_s16 with
    <|vs_vars := order_run_s16.vs_vars |+ ("%14",0w); vs_inst_idx := 17|>
End

Theorem order_run_step16:
  step_inst_base (mk_inst 16 GT [Var "%12";Var "%11"] ["%14"]) order_run_s16 =
    OK (order_run_s17 with vs_inst_idx := 16)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%12" order_run_s16 = SOME 3w` by
    simp[order_run_s16_def, order_run_s15_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_var "%11" order_run_s16 = SOME 3w` by
    simp[order_run_s16_def, order_run_s15_def, order_run_s14_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[] >>
  simp[order_run_s17_def, order_run_s16_def, venomStateTheory.update_var_def]
QED

(* Both bound-error flags are zero. *)
Definition order_run_s18_def:
  order_run_s18 = order_run_s17 with
    <|vs_vars := order_run_s17.vs_vars |+ ("%15",0w); vs_inst_idx := 18|>
End

Theorem order_run_step17:
  step_inst_base (mk_inst 17 OR [Var "%13";Var "%14"] ["%15"]) order_run_s17 =
    OK (order_run_s18 with vs_inst_idx := 17)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%13" order_run_s17 = SOME 0w` by
    simp[order_run_s17_def, order_run_s16_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_var "%14" order_run_s17 = SOME 0w` by
    simp[order_run_s17_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[] >>
  simp[order_run_s18_def, order_run_s17_def, venomStateTheory.update_var_def]
QED

(* The bound assertion succeeds. *)
Definition order_run_s19_def:
  order_run_s19 = order_run_s18 with
    <|vs_vars := order_run_s18.vs_vars |+ ("%16",1w); vs_inst_idx := 19|>
End

Theorem order_run_step18:
  step_inst_base (mk_inst 18 ISZERO [Var "%15"] ["%16"]) order_run_s18 =
    OK (order_run_s19 with vs_inst_idx := 18)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%15" order_run_s18 = SOME 0w` by
    simp[order_run_s18_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[] >>
  simp[order_run_s19_def, order_run_s18_def, venomStateTheory.update_var_def]
QED

(* Successful bound assertion advances only the cursor. *)
Definition order_run_s20_def:
  order_run_s20 = order_run_s19 with vs_inst_idx := 20
End

Theorem order_run_step19:
  step_inst_base (mk_inst 19 ASSERT [Var "%16"] []) order_run_s19 =
    OK (order_run_s20 with vs_inst_idx := 19)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_run_s20_def, order_run_s19_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem order_run_s20_copy_operands:
  lookup_var "%10" order_run_s20 = SOME 2w /\
  lookup_var "%2" order_run_s20 = SOME 288w /\
  lookup_var "%0" order_run_s20 = SOME 2w
Proof
  simp[venomStateTheory.lookup_var_def, order_run_s20_def,
       order_run_s19_def, order_run_s18_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s17_def, order_run_s16_def, order_run_s15_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s14_def, order_run_s13_def, order_run_s12_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s11_def, order_run_s10_def, order_run_s9_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s8_def, order_run_s7_def, order_run_s6_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s5_def, order_run_s4_def, order_run_s3_def,
       order_run_s2_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_run_s20_accounts:
  order_run_s20.vs_accounts = order_run_start.vs_accounts
Proof
  simp[order_run_s20_def, order_run_s19_def, order_run_s18_def] >>
  simp[order_run_s17_def, order_run_s16_def, order_run_s15_def] >>
  simp[order_run_s14_def, order_run_s13_accounts]
QED

(* Explicit expanded-memory snapshot for the external-code byte copy. *)
Definition order_run_s21_def:
  order_run_s21 = order_run_s20 with
    <|vs_memory := TAKE 288 (order_run_s20.vs_memory ++ REPLICATE 65 0w) ++
        [30w] ++ DROP 289 (order_run_s20.vs_memory ++ REPLICATE 65 0w);
      vs_inst_idx := 21|>
End

Theorem order_run_s20_memory_length:
  LENGTH order_run_s20.vs_memory = 224
Proof
  simp[order_run_s20_def, order_run_s19_def, order_run_s18_def] >>
  simp[order_run_s17_def, order_run_s16_def, order_run_s15_def] >>
  simp[order_run_s14_def, order_run_s13_def, order_run_s12_def] >>
  simp[order_run_s11_def, order_run_s10_def, order_run_s9_def,
       order_run_s8_memory_length, byteTheory.LENGTH_word_to_bytes,
       venomMemPropsTheory.dimindex_256]
QED

Theorem order_run_step20:
  step_inst_base (mk_inst 20 EXTCODECOPY
    [Var "%10";Var "%2";Var "%0";Lit 1w] []) order_run_s20 =
    OK (order_run_s21 with vs_inst_idx := 20)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_run_s20_copy_operands,
       order_run_s20_accounts] >>
  `(lookup_account (2w:address) order_run_start.vs_accounts).code =
     [10w;20w;30w]` by EVAL_TAC >>
  simp[venomStateTheory.write_memory_with_expansion_def,
       order_run_s20_memory_length] >>
  simp[order_run_s21_def, order_run_s20_def]
QED

(* Final bytestring length header, preserving the copied data byte. *)
Definition order_run_s22_def:
  order_run_s22 = order_run_s21 with
    <|vs_memory := TAKE 256 order_run_s21.vs_memory ++
        word_to_bytes (1w:bytes32) T ++ DROP 288 order_run_s21.vs_memory;
      vs_inst_idx := 22|>
End

Theorem order_run_s21_buffer_operand:
  lookup_var "%1" order_run_s21 = SOME 256w
Proof
  simp[venomStateTheory.lookup_var_def, order_run_s21_def, order_run_s20_def,
       order_run_s19_def, order_run_s18_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s17_def, order_run_s16_def, order_run_s15_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s14_def, order_run_s13_def, order_run_s12_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s11_def, order_run_s10_def, order_run_s9_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s8_def, order_run_s7_def, order_run_s6_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_run_s5_def, order_run_s4_def, order_run_s3_def,
       order_run_s2_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_run_step21:
  step_inst_base (mk_inst 21 MSTORE [Var "%1";Lit 1w] []) order_run_s21 =
    OK (order_run_s22 with vs_inst_idx := 21)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_run_s21_buffer_operand] >>
  `LENGTH order_run_s21.vs_memory = 289` by
    simp[order_run_s21_def, order_run_s20_memory_length] >>
  simp[venomStateTheory.mstore_def,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  simp[order_run_s22_def, order_run_s21_def]
QED

Theorem order_run_output_byte:
  read_memory 288 1 order_run_s22 = [30w]
Proof
  simp[venomStateTheory.read_memory_def, order_run_s22_def,
       listTheory.DROP_APPEND, byteTheory.LENGTH_word_to_bytes,
       venomMemPropsTheory.dimindex_256] >>
  simp[order_run_s21_def, order_run_s20_memory_length,
       listTheory.DROP_APPEND] >>
  simp[listTheory.DROP_LENGTH_TOO_LONG, listTheory.LENGTH_TAKE,
       byteTheory.LENGTH_word_to_bytes, venomMemPropsTheory.dimindex_256,
       order_run_s20_memory_length]
QED

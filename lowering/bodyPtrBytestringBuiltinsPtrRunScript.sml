Theory bodyPtrBytestringBuiltinsPtrRun
Ancestors
  bodyPtrBytestringBuiltinsSourceFrame bodyPtrBytestringBuiltinsOrderRun compileEnv

(* A named pre-existing pointer cannot collide with percent-number temporaries.
   Keep this legal local binding separate from the earlier MemLoc experiment. *)
Definition order_ptr_env_def:
  order_ptr_env = order_run_env with
    ce_vars := FEMPTY |+ ("arr", PtrVar (Var "arr_ptr") 96)
End

(* Compile the actual expression using the compatible local binding. *)
Definition order_ptr_compiled_def:
  order_ptr_compiled = compile_expr order_ptr_env
    (BaseT (BytesT (Dynamic 1))) order_probe_expr
    (initial_compile_state "entry")
End

(* Initialize the pre-existing pointer, retaining the old concrete memory. *)
Definition order_ptr_start_def:
  order_ptr_start = order_run_start with
    vs_vars := FEMPTY |+ ("arr_ptr",128w)
End

Theorem order_ptr_freshness:
  not_fresh_at (initial_compile_state "entry") "arr_ptr" /\
  fresh_vars_wrt (initial_compile_state "entry") order_ptr_start /\
  lookup_var "arr_ptr" order_ptr_start = SOME 128w
Proof
  simp[not_fresh_at_def, fresh_vars_wrt_def, order_ptr_start_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_ptr_instructions:
  (SND order_ptr_compiled).cs_current_insts =
    [mk_inst 0 MLOAD [Var "arr_ptr"] ["%0"];
     mk_inst 1 ALLOCA [Lit 64w] ["%1"];
     mk_inst 2 ADD [Var "%1";Lit 32w] ["%2"];
     mk_inst 3 MLOAD [Var "arr_ptr"] ["%3"];
     mk_inst 4 ISZERO [Var "%3"] ["%4"];
     mk_inst 5 ISZERO [Var "%4"] ["%5"];
     mk_inst 6 ASSERT [Var "%5"] [];
     mk_inst 7 SUB [Var "%3";Lit 1w] ["%6"];
     mk_inst 8 MSTORE [Var "arr_ptr";Var "%6"] [];
     mk_inst 9 ADD [Var "arr_ptr";Lit 32w] ["%7"];
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

Theorem order_ptr_result:
  FST order_ptr_compiled =
    LocatedValue (BaseT (BytesT (Dynamic 1)))
      <|ptr_operand := Var "%1"; ptr_location := LocMemory; ptr_buf := NONE|> /\
  (SND order_ptr_compiled).cs_blocks = [] /\
  (SND order_ptr_compiled).cs_current_bb = "entry"
Proof
  EVAL_TAC >> simp[]
QED

Theorem order_ptr_start_array:
  mload 128 order_ptr_start = 2w /\
  mload 160 order_ptr_start = 1w /\
  mload 192 order_ptr_start = 2w
Proof
  mp_tac order_run_start_array >>
  simp[order_ptr_start_def, venomStateTheory.mload_def]
QED

(* Concrete first snapshot retains the initialized local pointer. *)
Definition order_ptr_s1_def:
  order_ptr_s1 = order_ptr_start with
    <|vs_vars := order_ptr_start.vs_vars |+ ("%0",2w); vs_inst_idx := 1|>
End

Theorem order_ptr_step0:
  step_inst_base (mk_inst 0 MLOAD [Var "arr_ptr"] ["%0"]) order_ptr_start =
    OK (order_ptr_s1 with vs_inst_idx := 0)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_ptr_freshness,
       wordsTheory.w2n_n2w, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256, order_ptr_start_array] >>
  simp[venomStateTheory.update_var_def, order_ptr_s1_def,
       order_ptr_start_def, order_run_start_def,
       venomStateTheory.init_venom_state_def]
QED

(* Allocation leaves the input memory and pre-existing pointer unchanged. *)
Definition order_ptr_s2_def:
  order_ptr_s2 = order_ptr_start with
    <|vs_vars := order_ptr_start.vs_vars |+ ("%0",2w) |+ ("%1",256w);
      vs_inst_idx := 2; vs_allocas := FEMPTY |+ (1,(256,64));
      vs_alloca_next := 320|>
End

Theorem order_ptr_step1:
  step_inst_base (mk_inst 1 ALLOCA [Lit 64w] ["%1"]) order_ptr_s1 =
    OK (order_ptr_s2 with vs_inst_idx := 1)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256] >>
  simp[order_ptr_s1_def, order_ptr_s2_def,
       venomStateTheory.update_var_def] >>
  simp[order_ptr_start_def, order_run_start_def,
       venomStateTheory.init_venom_state_def]
QED

(* Next straight-line snapshots expose only the changed variable map. *)
Definition order_ptr_s3_def:
  order_ptr_s3 = order_ptr_s2 with
    <|vs_vars := order_ptr_s2.vs_vars |+ ("%2",288w); vs_inst_idx := 3|>
End

Theorem order_ptr_step2:
  step_inst_base (mk_inst 2 ADD [Var "%1";Lit 32w] ["%2"]) order_ptr_s2 =
    OK (order_ptr_s3 with vs_inst_idx := 2)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s3_def, order_ptr_s2_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.word_add_n2w]
QED

Definition order_ptr_s4_def:
  order_ptr_s4 = order_ptr_s3 with
    <|vs_vars := order_ptr_s3.vs_vars |+ ("%3",2w); vs_inst_idx := 4|>
End

Theorem order_ptr_step3:
  step_inst_base (mk_inst 3 MLOAD [Var "arr_ptr"] ["%3"]) order_ptr_s3 =
    OK (order_ptr_s4 with vs_inst_idx := 3)
Proof
  `lookup_var "arr_ptr" order_ptr_s3 = SOME 128w` by
    simp[venomStateTheory.lookup_var_def, order_ptr_s3_def,
         order_ptr_s2_def, order_ptr_start_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `mload 128 order_ptr_s3 = 2w` by
    (mp_tac order_ptr_start_array >>
     simp[order_ptr_s3_def, order_ptr_s2_def, venomStateTheory.mload_def]) >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256] >>
  simp[order_ptr_s4_def, venomStateTheory.update_var_def,
       order_ptr_s3_def, order_ptr_s2_def]
QED

(* Boolean guard snapshots for the nonempty Pop. *)
Definition order_ptr_s5_def:
  order_ptr_s5 = order_ptr_s4 with
    <|vs_vars := order_ptr_s4.vs_vars |+ ("%4",0w); vs_inst_idx := 5|>
End

Theorem order_ptr_step4:
  step_inst_base (mk_inst 4 ISZERO [Var "%3"] ["%4"]) order_ptr_s4 =
    OK (order_ptr_s5 with vs_inst_idx := 4)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s5_def, order_ptr_s4_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, venomExecSemanticsTheory.bool_to_word_def,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Definition order_ptr_s6_def:
  order_ptr_s6 = order_ptr_s5 with
    <|vs_vars := order_ptr_s5.vs_vars |+ ("%5",1w); vs_inst_idx := 6|>
End

Theorem order_ptr_step5:
  step_inst_base (mk_inst 5 ISZERO [Var "%4"] ["%5"]) order_ptr_s5 =
    OK (order_ptr_s6 with vs_inst_idx := 5)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s6_def, order_ptr_s5_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, venomExecSemanticsTheory.bool_to_word_def]
QED

Definition order_ptr_s7_def:
  order_ptr_s7 = order_ptr_s6 with vs_inst_idx := 7
End

Theorem order_ptr_step6:
  step_inst_base (mk_inst 6 ASSERT [Var "%5"] []) order_ptr_s6 =
    OK (order_ptr_s7 with vs_inst_idx := 6)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s7_def, order_ptr_s6_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Definition order_ptr_s8_def:
  order_ptr_s8 = order_ptr_s7 with
    <|vs_vars := order_ptr_s7.vs_vars |+ ("%6",1w); vs_inst_idx := 8|>
End

Theorem order_ptr_step7:
  step_inst_base (mk_inst 7 SUB [Var "%3";Lit 1w] ["%6"]) order_ptr_s7 =
    OK (order_ptr_s8 with vs_inst_idx := 7)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s8_def, order_ptr_s7_def, order_ptr_s6_def,
       order_ptr_s5_def, order_ptr_s4_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV)
QED

(* Pop stores the decremented length without changing the pointer variable. *)
Definition order_ptr_s9_def:
  order_ptr_s9 = order_ptr_s8 with
    <|vs_memory := TAKE 128 order_ptr_s8.vs_memory ++
        word_to_bytes (1w:bytes32) T ++ DROP 160 order_ptr_s8.vs_memory;
      vs_inst_idx := 9|>
End

Theorem order_ptr_s8_memory_length:
  LENGTH order_ptr_s8.vs_memory = 224
Proof
  simp[order_ptr_s8_def, order_ptr_s7_def, order_ptr_s6_def,
       order_ptr_s5_def, order_ptr_s4_def, order_ptr_s3_def,
       order_ptr_s2_def, order_ptr_start_def, order_run_start_def]
QED

Theorem order_ptr_s8_arr:
  lookup_var "arr_ptr" order_ptr_s8 = SOME 128w
Proof
  simp[venomStateTheory.lookup_var_def, order_ptr_s8_def,
       order_ptr_s7_def, order_ptr_s6_def, order_ptr_s5_def,
       order_ptr_s4_def, order_ptr_s3_def, order_ptr_s2_def,
       order_ptr_start_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_ptr_step8:
  step_inst_base (mk_inst 8 MSTORE [Var "arr_ptr";Var "%6"] []) order_ptr_s8 =
    OK (order_ptr_s9 with vs_inst_idx := 8)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_ptr_s8_arr] >>
  `lookup_var "%6" order_ptr_s8 = SOME 1w` by
    simp[order_ptr_s8_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[venomStateTheory.mstore_def, order_ptr_s8_memory_length,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  simp[order_ptr_s9_def, order_ptr_s8_def]
QED

Definition order_ptr_s10_def:
  order_ptr_s10 = order_ptr_s9 with
    <|vs_vars := order_ptr_s9.vs_vars |+ ("%7",160w); vs_inst_idx := 10|>
End

Theorem order_ptr_step9:
  step_inst_base (mk_inst 9 ADD [Var "arr_ptr";Lit 32w] ["%7"]) order_ptr_s9 =
    OK (order_ptr_s10 with vs_inst_idx := 9)
Proof
  `lookup_var "arr_ptr" order_ptr_s9 = SOME 128w` by
    (mp_tac order_ptr_s8_arr >>
     simp[order_ptr_s9_def, venomStateTheory.lookup_var_def]) >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, wordsTheory.word_add_n2w] >>
  simp[order_ptr_s10_def, order_ptr_s9_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s11_def:
  order_ptr_s11 = order_ptr_s10 with
    <|vs_vars := order_ptr_s10.vs_vars |+ ("%8",32w); vs_inst_idx := 11|>
End

Theorem order_ptr_step10:
  step_inst_base (mk_inst 10 MUL [Var "%6";Lit 32w] ["%8"]) order_ptr_s10 =
    OK (order_ptr_s11 with vs_inst_idx := 10)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%6" order_ptr_s10 = SOME 1w` by
    simp[order_ptr_s10_def, order_ptr_s9_def, order_ptr_s8_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s11_def, order_ptr_s10_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s12_def:
  order_ptr_s12 = order_ptr_s11 with
    <|vs_vars := order_ptr_s11.vs_vars |+ ("%9",192w); vs_inst_idx := 12|>
End

Theorem order_ptr_step11:
  step_inst_base (mk_inst 11 ADD [Var "%7";Var "%8"] ["%9"]) order_ptr_s11 =
    OK (order_ptr_s12 with vs_inst_idx := 11)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s12_def, order_ptr_s11_def, order_ptr_s10_def,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.word_add_n2w]
QED

(* The popped last element is the external address two. *)
Definition order_ptr_s13_def:
  order_ptr_s13 = order_ptr_s12 with
    <|vs_vars := order_ptr_s12.vs_vars |+ ("%10",2w); vs_inst_idx := 13|>
End

Theorem order_ptr_s12_array:
  mload 192 order_ptr_s12 = 2w
Proof
  simp[venomStateTheory.mload_def, venomStateTheory.read_memory_def,
       order_ptr_s12_def, order_ptr_s11_def, order_ptr_s10_def,
       order_ptr_s9_def] >>
  simp[order_ptr_s8_def, order_ptr_s7_def, order_ptr_s6_def,
       order_ptr_s5_def, order_ptr_s4_def, order_ptr_s3_def,
       order_ptr_s2_def, order_ptr_start_def] >>
  simp[order_run_start_def] >> EVAL_TAC
QED

Theorem order_ptr_step12:
  step_inst_base (mk_inst 12 MLOAD [Var "%9"] ["%10"]) order_ptr_s12 =
    OK (order_ptr_s13 with vs_inst_idx := 12)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%9" order_ptr_s12 = SOME 192w` by
    simp[order_ptr_s12_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
       order_ptr_s12_array] >>
  simp[order_ptr_s13_def, order_ptr_s12_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s14_def:
  order_ptr_s14 = order_ptr_s13 with
    <|vs_vars := order_ptr_s13.vs_vars |+ ("%11",3w); vs_inst_idx := 14|>
End

Theorem order_ptr_s13_accounts:
  order_ptr_s13.vs_accounts = order_run_start.vs_accounts
Proof
  simp[order_ptr_s13_def, order_ptr_s12_def, order_ptr_s11_def] >>
  simp[order_ptr_s10_def, order_ptr_s9_def, order_ptr_s8_def] >>
  simp[order_ptr_s7_def, order_ptr_s6_def, order_ptr_s5_def] >>
  simp[order_ptr_s4_def, order_ptr_s3_def, order_ptr_s2_def,
       order_ptr_start_def]
QED

Theorem order_ptr_step13:
  step_inst_base (mk_inst 13 EXTCODESIZE [Var "%10"] ["%11"]) order_ptr_s13 =
    OK (order_ptr_s14 with vs_inst_idx := 13)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%10" order_ptr_s13 = SOME 2w` by
    simp[order_ptr_s13_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s13_accounts] >>
  `LENGTH (lookup_account (2w:address) order_run_start.vs_accounts).code = 3` by
    EVAL_TAC >>
  simp[order_ptr_s14_def, order_ptr_s13_def, venomStateTheory.update_var_def]
QED

(* Bounds still use the length read before Pop. *)
Definition order_ptr_s15_def:
  order_ptr_s15 = order_ptr_s14 with
    <|vs_vars := order_ptr_s14.vs_vars |+ ("%12",3w); vs_inst_idx := 15|>
End

Theorem order_ptr_s14_start_operand:
  lookup_var "%0" order_ptr_s14 = SOME 2w
Proof
  simp[venomStateTheory.lookup_var_def, order_ptr_s14_def,
       order_ptr_s13_def, order_ptr_s12_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s11_def, order_ptr_s10_def, order_ptr_s9_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s8_def, order_ptr_s7_def, order_ptr_s6_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s5_def, order_ptr_s4_def, order_ptr_s3_def,
       order_ptr_s2_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_ptr_step14:
  step_inst_base (mk_inst 14 ADD [Var "%0";Lit 1w] ["%12"]) order_ptr_s14 =
    OK (order_ptr_s15 with vs_inst_idx := 14)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_ptr_s14_start_operand,
       wordsTheory.word_add_n2w] >>
  simp[order_ptr_s15_def, order_ptr_s14_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s16_def:
  order_ptr_s16 = order_ptr_s15 with
    <|vs_vars := order_ptr_s15.vs_vars |+ ("%13",0w); vs_inst_idx := 16|>
End

Theorem order_ptr_step15:
  step_inst_base (mk_inst 15 LT [Var "%12";Var "%0"] ["%13"]) order_ptr_s15 =
    OK (order_ptr_s16 with vs_inst_idx := 15)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%12" order_ptr_s15 = SOME 3w` by
    simp[order_ptr_s15_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_var "%0" order_ptr_s15 = SOME 2w` by
    (mp_tac order_ptr_s14_start_operand >>
     simp[order_ptr_s15_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[] >>
  simp[order_ptr_s16_def, order_ptr_s15_def, venomStateTheory.update_var_def]
QED

(* The requested end equals the external code size. *)
Definition order_ptr_s17_def:
  order_ptr_s17 = order_ptr_s16 with
    <|vs_vars := order_ptr_s16.vs_vars |+ ("%14",0w); vs_inst_idx := 17|>
End

Theorem order_ptr_step16:
  step_inst_base (mk_inst 16 GT [Var "%12";Var "%11"] ["%14"]) order_ptr_s16 =
    OK (order_ptr_s17 with vs_inst_idx := 16)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%12" order_ptr_s16 = SOME 3w` by
    simp[order_ptr_s16_def, order_ptr_s15_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_var "%11" order_ptr_s16 = SOME 3w` by
    simp[order_ptr_s16_def, order_ptr_s15_def, order_ptr_s14_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[] >>
  simp[order_ptr_s17_def, order_ptr_s16_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s18_def:
  order_ptr_s18 = order_ptr_s17 with
    <|vs_vars := order_ptr_s17.vs_vars |+ ("%15",0w); vs_inst_idx := 18|>
End

Theorem order_ptr_step17:
  step_inst_base (mk_inst 17 OR [Var "%13";Var "%14"] ["%15"]) order_ptr_s17 =
    OK (order_ptr_s18 with vs_inst_idx := 17)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%13" order_ptr_s17 = SOME 0w` by
    simp[order_ptr_s17_def, order_ptr_s16_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `lookup_var "%14" order_ptr_s17 = SOME 0w` by
    simp[order_ptr_s17_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[] >>
  simp[order_ptr_s18_def, order_ptr_s17_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s19_def:
  order_ptr_s19 = order_ptr_s18 with
    <|vs_vars := order_ptr_s18.vs_vars |+ ("%16",1w); vs_inst_idx := 19|>
End

Theorem order_ptr_step18:
  step_inst_base (mk_inst 18 ISZERO [Var "%15"] ["%16"]) order_ptr_s18 =
    OK (order_ptr_s19 with vs_inst_idx := 18)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_pure1_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  `lookup_var "%15" order_ptr_s18 = SOME 0w` by
    simp[order_ptr_s18_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[] >>
  simp[order_ptr_s19_def, order_ptr_s18_def, venomStateTheory.update_var_def]
QED

Definition order_ptr_s20_def:
  order_ptr_s20 = order_ptr_s19 with vs_inst_idx := 20
End

Theorem order_ptr_step19:
  step_inst_base (mk_inst 19 ASSERT [Var "%16"] []) order_ptr_s19 =
    OK (order_ptr_s20 with vs_inst_idx := 19)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def] >>
  simp[order_ptr_s20_def, order_ptr_s19_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem order_ptr_s20_copy_operands:
  lookup_var "%10" order_ptr_s20 = SOME 2w /\
  lookup_var "%2" order_ptr_s20 = SOME 288w /\
  lookup_var "%0" order_ptr_s20 = SOME 2w
Proof
  simp[venomStateTheory.lookup_var_def, order_ptr_s20_def,
       order_ptr_s19_def, order_ptr_s18_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s17_def, order_ptr_s16_def, order_ptr_s15_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s14_def, order_ptr_s13_def, order_ptr_s12_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s11_def, order_ptr_s10_def, order_ptr_s9_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s8_def, order_ptr_s7_def, order_ptr_s6_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s5_def, order_ptr_s4_def, order_ptr_s3_def,
       order_ptr_s2_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_ptr_s20_accounts:
  order_ptr_s20.vs_accounts = order_run_start.vs_accounts
Proof
  simp[order_ptr_s20_def, order_ptr_s19_def, order_ptr_s18_def] >>
  simp[order_ptr_s17_def, order_ptr_s16_def, order_ptr_s15_def] >>
  simp[order_ptr_s14_def, order_ptr_s13_accounts]
QED

(* Expanded-memory snapshot after copying the observed external-code byte. *)
Definition order_ptr_s21_def:
  order_ptr_s21 = order_ptr_s20 with
    <|vs_memory := TAKE 288 (order_ptr_s20.vs_memory ++ REPLICATE 65 0w) ++
        [30w] ++ DROP 289 (order_ptr_s20.vs_memory ++ REPLICATE 65 0w);
      vs_inst_idx := 21|>
End

Theorem order_ptr_s20_memory_length:
  LENGTH order_ptr_s20.vs_memory = 224
Proof
  simp[order_ptr_s20_def, order_ptr_s19_def, order_ptr_s18_def] >>
  simp[order_ptr_s17_def, order_ptr_s16_def, order_ptr_s15_def] >>
  simp[order_ptr_s14_def, order_ptr_s13_def, order_ptr_s12_def] >>
  simp[order_ptr_s11_def, order_ptr_s10_def, order_ptr_s9_def,
       order_ptr_s8_memory_length, byteTheory.LENGTH_word_to_bytes,
       venomMemPropsTheory.dimindex_256]
QED

Theorem order_ptr_step20:
  step_inst_base (mk_inst 20 EXTCODECOPY
    [Var "%10";Var "%2";Var "%0";Lit 1w] []) order_ptr_s20 =
    OK (order_ptr_s21 with vs_inst_idx := 20)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_ptr_s20_copy_operands,
       order_ptr_s20_accounts] >>
  `(lookup_account (2w:address) order_run_start.vs_accounts).code =
     [10w;20w;30w]` by EVAL_TAC >>
  simp[venomStateTheory.write_memory_with_expansion_def,
       order_ptr_s20_memory_length] >>
  simp[order_ptr_s21_def, order_ptr_s20_def]
QED

(* Snapshot of the final bytestring header store. *)
Definition order_ptr_s22_def:
  order_ptr_s22 = order_ptr_s21 with
    <|vs_memory := TAKE 256 order_ptr_s21.vs_memory ++
        word_to_bytes (1w:bytes32) T ++ DROP 288 order_ptr_s21.vs_memory;
      vs_inst_idx := 22|>
End

Theorem order_ptr_s21_buffer_operand:
  lookup_var "%1" order_ptr_s21 = SOME 256w
Proof
  simp[venomStateTheory.lookup_var_def, order_ptr_s21_def, order_ptr_s20_def,
       order_ptr_s19_def, order_ptr_s18_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s17_def, order_ptr_s16_def, order_ptr_s15_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s14_def, order_ptr_s13_def, order_ptr_s12_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s11_def, order_ptr_s10_def, order_ptr_s9_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s8_def, order_ptr_s7_def, order_ptr_s6_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[order_ptr_s5_def, order_ptr_s4_def, order_ptr_s3_def,
       order_ptr_s2_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem order_ptr_step21:
  step_inst_base (mk_inst 21 MSTORE [Var "%1";Lit 1w] []) order_ptr_s21 =
    OK (order_ptr_s22 with vs_inst_idx := 21)
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def, venomInstTheory.mk_inst_def,
       venomStateTheory.eval_operand_def, order_ptr_s21_buffer_operand] >>
  `LENGTH order_ptr_s21.vs_memory = 289` by
    simp[order_ptr_s21_def, order_ptr_s20_memory_length] >>
  simp[venomStateTheory.mstore_def,
       wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  simp[order_ptr_s22_def, order_ptr_s21_def]
QED

Theorem order_ptr_output_byte:
  read_memory 288 1 order_ptr_s22 = [30w]
Proof
  simp[venomStateTheory.read_memory_def, order_ptr_s22_def,
       listTheory.DROP_APPEND, byteTheory.LENGTH_word_to_bytes,
       venomMemPropsTheory.dimindex_256] >>
  simp[order_ptr_s21_def, order_ptr_s20_memory_length,
       listTheory.DROP_APPEND] >>
  simp[listTheory.DROP_LENGTH_TOO_LONG, listTheory.LENGTH_TAKE,
       byteTheory.LENGTH_word_to_bytes, venomMemPropsTheory.dimindex_256,
       order_ptr_s20_memory_length]
QED

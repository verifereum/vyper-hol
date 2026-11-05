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

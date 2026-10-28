(* Intermediate context and code generation expression, checked by the
   pipeline, readiness, and bytecode parity theorems. *)
Theory foldedValueParityAbiInput
Ancestors foldedValueParityCompute

Definition enc_mid_const_context_def[nocompute]:
  enc_mid_const_context =
    <|ctx_functions :=
                        [<|fn_name := "__entry";
                           fn_blocks :=
                             [<|bb_label := "__entry";
                                bb_instructions :=
                                  [<|inst_id := 54; inst_opcode := ASSIGN; inst_operands := [Lit 4w];
                                     inst_outputs := ["formal_var_0"]|>;
                                   <|inst_id := 0; inst_opcode := CALLDATASIZE; inst_operands := [];
                                     inst_outputs := ["%0"]|>;
                                   <|inst_id := 1; inst_opcode := LT;
                                     inst_operands := [Var "%0"; Var "formal_var_0"];
                                     inst_outputs := ["%1"]|>;
                                   <|inst_id := 2; inst_opcode := ISZERO; inst_operands := [Var "%1"];
                                     inst_outputs := ["%2"]|>;
                                   <|inst_id := 3; inst_opcode := JNZ;
                                     inst_operands :=
                                       [Var "%2"; Label "@dispatch_1"; Label "formal_label_0"];
                                     inst_outputs := []|>]|>;
                              <|bb_label := "@dispatch_1";
                                bb_instructions :=
                                  [<|inst_id := 55; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_1"]|>;
                                   <|inst_id := 4; inst_opcode := CALLDATALOAD;
                                     inst_operands := [Var "formal_var_1"]; inst_outputs := ["%3"]|>;
                                   <|inst_id := 56; inst_opcode := ASSIGN; inst_operands := [Lit 224w];
                                     inst_outputs := ["formal_var_2"]|>;
                                   <|inst_id := 5; inst_opcode := SHR;
                                     inst_operands := [Var "formal_var_2"; Var "%3"];
                                     inst_outputs := ["%4"]|>;
                                   <|inst_id := 57; inst_opcode := ASSIGN;
                                     inst_operands := [Lit 0xB3DE648Bw]; inst_outputs := ["formal_var_3"]|>;
                                   <|inst_id := 6; inst_opcode := EQ;
                                     inst_operands := [Var "formal_var_3"; Var "%4"];
                                     inst_outputs := ["%5"]|>;
                                   <|inst_id := 7; inst_opcode := JNZ;
                                     inst_operands := [Var "%5"; Label "fn_f"; Label "formal_label_1"];
                                     inst_outputs := []|>]|>;
                              <|bb_label := "fn_f";
                                bb_instructions :=
                                  [<|inst_id := 10; inst_opcode := CALLVALUE; inst_operands := [];
                                     inst_outputs := ["%6"]|>;
                                   <|inst_id := 11; inst_opcode := ISZERO; inst_operands := [Var "%6"];
                                     inst_outputs := ["%7"]|>;
                                   <|inst_id := 12; inst_opcode := ASSERT; inst_operands := [Var "%7"];
                                     inst_outputs := []|>;
                                   <|inst_id := 58; inst_opcode := ASSIGN; inst_operands := [Lit 36w];
                                     inst_outputs := ["formal_var_4"]|>;
                                   <|inst_id := 13; inst_opcode := CALLDATASIZE; inst_operands := [];
                                     inst_outputs := ["%8"]|>;
                                   <|inst_id := 14; inst_opcode := LT;
                                     inst_operands := [Var "%8"; Var "formal_var_4"];
                                     inst_outputs := ["%9"]|>;
                                   <|inst_id := 15; inst_opcode := ISZERO; inst_operands := [Var "%9"];
                                     inst_outputs := ["%10"]|>;
                                   <|inst_id := 16; inst_opcode := ASSERT; inst_operands := [Var "%10"];
                                     inst_outputs := []|>;
                                   <|inst_id := 59; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_5"]|>;
                                   <|inst_id := 60; inst_opcode := ASSIGN; inst_operands := [Lit 4w];
                                     inst_outputs := ["formal_var_6"]|>;
                                   <|inst_id := 18; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_6"; Var "formal_var_5"];
                                     inst_outputs := ["%12"]|>;
                                   <|inst_id := 19; inst_opcode := CALLDATALOAD;
                                     inst_operands := [Var "%12"]; inst_outputs := ["%13"]|>;
                                   <|inst_id := 17; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["%11"]|>;
                                   <|inst_id := 61; inst_opcode := ASSIGN; inst_operands := [Var "%11"];
                                     inst_outputs := ["formal_var_7"]|>;
                                   <|inst_id := 20; inst_opcode := MSTORE;
                                     inst_operands := [Var "formal_var_7"; Var "%13"]; inst_outputs := []|>;
                                   <|inst_id := 62; inst_opcode := ASSIGN; inst_operands := [Var "%11"];
                                     inst_outputs := ["formal_var_8"]|>;
                                   <|inst_id := 21; inst_opcode := MLOAD;
                                     inst_operands := [Var "formal_var_8"]; inst_outputs := ["%14"]|>;
                                   <|inst_id := 22; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["%15"]|>;
                                   <|inst_id := 63; inst_opcode := ASSIGN; inst_operands := [Var "%15"];
                                     inst_outputs := ["formal_var_9"]|>;
                                   <|inst_id := 23; inst_opcode := MSTORE;
                                     inst_operands := [Var "formal_var_9"; Var "%14"]; inst_outputs := []|>;
                                   <|inst_id := 68; inst_opcode := ASSIGN;
                                     inst_operands :=
                                       [Lit
                                          0xDEADBEEF00000000000000000000000000000000000000000000000000000000w];
                                     inst_outputs := ["formal_var_14"]|>;
                                   <|inst_id := 24; inst_opcode := ASSIGN; inst_operands := [Lit 160w];
                                     inst_outputs := ["%16"]|>;
                                   <|inst_id := 67; inst_opcode := ASSIGN; inst_operands := [Var "%16"];
                                     inst_outputs := ["formal_var_13"]|>;
                                   <|inst_id := 66; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["formal_var_12"]|>;
                                   <|inst_id := 26; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_12"; Var "formal_var_13"];
                                     inst_outputs := ["%18"]|>;
                                   <|inst_id := 27; inst_opcode := MSTORE;
                                     inst_operands := [Var "%18"; Var "formal_var_14"]; inst_outputs := []|>;
                                   <|inst_id := 69; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["formal_var_15"]|>;
                                   <|inst_id := 70; inst_opcode := ASSIGN; inst_operands := [Var "%15"];
                                     inst_outputs := ["formal_var_16"]|>;
                                   <|inst_id := 65; inst_opcode := ASSIGN; inst_operands := [Var "%16"];
                                     inst_outputs := ["formal_var_11"]|>;
                                   <|inst_id := 64; inst_opcode := ASSIGN; inst_operands := [Lit 36w];
                                     inst_outputs := ["formal_var_10"]|>;
                                   <|inst_id := 25; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_10"; Var "formal_var_11"];
                                     inst_outputs := ["%17"]|>;
                                   <|inst_id := 28; inst_opcode := MCOPY;
                                     inst_operands := [Var "%17"; Var "formal_var_16"; Var "formal_var_15"];
                                     inst_outputs := []|>;
                                   <|inst_id := 71; inst_opcode := ASSIGN; inst_operands := [Lit 4w];
                                     inst_outputs := ["formal_var_17"]|>;
                                   <|inst_id := 72; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["formal_var_18"]|>;
                                   <|inst_id := 29; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_18"; Var "formal_var_17"];
                                     inst_outputs := ["%19"]|>;
                                   <|inst_id := 73; inst_opcode := ASSIGN; inst_operands := [Var "%16"];
                                     inst_outputs := ["formal_var_19"]|>;
                                   <|inst_id := 30; inst_opcode := MSTORE;
                                     inst_operands := [Var "formal_var_19"; Var "%19"]; inst_outputs := []|>;
                                   <|inst_id := 74; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["formal_var_20"]|>;
                                   <|inst_id := 32; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["%21"]|>;
                                   <|inst_id := 75; inst_opcode := ASSIGN; inst_operands := [Var "%21"];
                                     inst_outputs := ["formal_var_21"]|>;
                                   <|inst_id := 33; inst_opcode := MSTORE;
                                     inst_operands := [Var "formal_var_21"; Var "formal_var_20"];
                                     inst_outputs := []|>;
                                   <|inst_id := 80; inst_opcode := ASSIGN; inst_operands := [Var "%21"];
                                     inst_outputs := ["formal_var_26"]|>;
                                   <|inst_id := 36; inst_opcode := MLOAD;
                                     inst_operands := [Var "formal_var_26"]; inst_outputs := ["%24"]|>;
                                   <|inst_id := 77; inst_opcode := ASSIGN; inst_operands := [Var "%16"];
                                     inst_outputs := ["formal_var_23"]|>;
                                   <|inst_id := 76; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_22"]|>;
                                   <|inst_id := 34; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_22"; Var "formal_var_23"];
                                     inst_outputs := ["%22"]|>;
                                   <|inst_id := 83; inst_opcode := ASSIGN; inst_operands := [Var "%22"];
                                     inst_outputs := ["formal_var_29"]|>;
                                   <|inst_id := 38; inst_opcode := MLOAD;
                                     inst_operands := [Var "formal_var_29"]; inst_outputs := ["%26"]|>;
                                   <|inst_id := 88; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_34"]|>;
                                   <|inst_id := 84; inst_opcode := ASSIGN; inst_operands := [Var "%26"];
                                     inst_outputs := ["formal_var_30"]|>;
                                   <|inst_id := 85; inst_opcode := ASSIGN; inst_operands := [Lit 31w];
                                     inst_outputs := ["formal_var_31"]|>;
                                   <|inst_id := 39; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_31"; Var "formal_var_30"];
                                     inst_outputs := ["%27"]|>;
                                   <|inst_id := 86; inst_opcode := ASSIGN;
                                     inst_operands :=
                                       [Lit
                                          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w];
                                     inst_outputs := ["formal_var_32"]|>;
                                   <|inst_id := 40; inst_opcode := AND;
                                     inst_operands := [Var "formal_var_32"; Var "%27"];
                                     inst_outputs := ["%28"]|>;
                                   <|inst_id := 81; inst_opcode := ASSIGN; inst_operands := [Var "%24"];
                                     inst_outputs := ["formal_var_27"]|>;
                                   <|inst_id := 31; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["%20"]|>;
                                   <|inst_id := 82; inst_opcode := ASSIGN; inst_operands := [Var "%20"];
                                     inst_outputs := ["formal_var_28"]|>;
                                   <|inst_id := 37; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_28"; Var "formal_var_27"];
                                     inst_outputs := ["%25"]|>;
                                   <|inst_id := 87; inst_opcode := ASSIGN; inst_operands := [Var "%25"];
                                     inst_outputs := ["formal_var_33"]|>;
                                   <|inst_id := 41; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_33"; Var "%28"];
                                     inst_outputs := ["%29"]|>;
                                   <|inst_id := 42; inst_opcode := MSTORE;
                                     inst_operands := [Var "%29"; Var "formal_var_34"]; inst_outputs := []|>;
                                   <|inst_id := 89; inst_opcode := ASSIGN; inst_operands := [Var "%26"];
                                     inst_outputs := ["formal_var_35"]|>;
                                   <|inst_id := 90; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["formal_var_36"]|>;
                                   <|inst_id := 43; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_36"; Var "formal_var_35"];
                                     inst_outputs := ["%30"]|>;
                                   <|inst_id := 91; inst_opcode := ASSIGN; inst_operands := [Var "%22"];
                                     inst_outputs := ["formal_var_37"]|>;
                                   <|inst_id := 92; inst_opcode := ASSIGN; inst_operands := [Var "%25"];
                                     inst_outputs := ["formal_var_38"]|>;
                                   <|inst_id := 44; inst_opcode := MCOPY;
                                     inst_operands := [Var "formal_var_38"; Var "formal_var_37"; Var "%30"];
                                     inst_outputs := []|>;
                                   <|inst_id := 97; inst_opcode := ASSIGN; inst_operands := [Var "%24"];
                                     inst_outputs := ["formal_var_43"]|>;
                                   <|inst_id := 79; inst_opcode := ASSIGN; inst_operands := [Var "%20"];
                                     inst_outputs := ["formal_var_25"]|>;
                                   <|inst_id := 78; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_24"]|>;
                                   <|inst_id := 35; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_24"; Var "formal_var_25"];
                                     inst_outputs := ["%23"]|>;
                                   <|inst_id := 48; inst_opcode := MSTORE;
                                     inst_operands := [Var "%23"; Var "formal_var_43"]; inst_outputs := []|>;
                                   <|inst_id := 93; inst_opcode := ASSIGN; inst_operands := [Var "%26"];
                                     inst_outputs := ["formal_var_39"]|>;
                                   <|inst_id := 94; inst_opcode := ASSIGN; inst_operands := [Lit 31w];
                                     inst_outputs := ["formal_var_40"]|>;
                                   <|inst_id := 45; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_40"; Var "formal_var_39"];
                                     inst_outputs := ["%31"]|>;
                                   <|inst_id := 95; inst_opcode := ASSIGN;
                                     inst_operands :=
                                       [Lit
                                          0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w];
                                     inst_outputs := ["formal_var_41"]|>;
                                   <|inst_id := 46; inst_opcode := AND;
                                     inst_operands := [Var "formal_var_41"; Var "%31"];
                                     inst_outputs := ["%32"]|>;
                                   <|inst_id := 96; inst_opcode := ASSIGN; inst_operands := [Lit 32w];
                                     inst_outputs := ["formal_var_42"]|>;
                                   <|inst_id := 47; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_42"; Var "%32"];
                                     inst_outputs := ["%33"]|>;
                                   <|inst_id := 98; inst_opcode := ASSIGN; inst_operands := [Var "%24"];
                                     inst_outputs := ["formal_var_44"]|>;
                                   <|inst_id := 49; inst_opcode := ADD;
                                     inst_operands := [Var "formal_var_44"; Var "%33"];
                                     inst_outputs := ["%34"]|>;
                                   <|inst_id := 99; inst_opcode := ASSIGN; inst_operands := [Var "%21"];
                                     inst_outputs := ["formal_var_45"]|>;
                                   <|inst_id := 50; inst_opcode := MSTORE;
                                     inst_operands := [Var "formal_var_45"; Var "%34"]; inst_outputs := []|>;
                                   <|inst_id := 100; inst_opcode := ASSIGN; inst_operands := [Var "%21"];
                                     inst_outputs := ["formal_var_46"]|>;
                                   <|inst_id := 51; inst_opcode := MLOAD;
                                     inst_operands := [Var "formal_var_46"]; inst_outputs := ["%35"]|>;
                                   <|inst_id := 101; inst_opcode := ASSIGN; inst_operands := [Var "%20"];
                                     inst_outputs := ["formal_var_47"]|>;
                                   <|inst_id := 52; inst_opcode := RETURN;
                                     inst_operands := [Var "formal_var_47"; Var "%35"]; inst_outputs := []|>]|>;
                              <|bb_label := "@fallback_0";
                                bb_instructions :=
                                  [<|inst_id := 102; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_48"]|>;
                                   <|inst_id := 103; inst_opcode := ASSIGN; inst_operands := [Lit 0w];
                                     inst_outputs := ["formal_var_49"]|>;
                                   <|inst_id := 53; inst_opcode := REVERT;
                                     inst_operands := [Var "formal_var_49"; Var "formal_var_48"];
                                     inst_outputs := []|>]|>;
                              <|bb_label := "formal_label_0";
                                bb_instructions :=
                                  [<|inst_id := 104; inst_opcode := JMP;
                                     inst_operands := [Label "@fallback_0"]; inst_outputs := []|>]|>;
                              <|bb_label := "formal_label_1";
                                bb_instructions :=
                                  [<|inst_id := 105; inst_opcode := JMP;
                                     inst_operands := [Label "@fallback_0"]; inst_outputs := []|>]|>];
                           fn_call_abi :=
                             <|ica_has_memory_return_buffer := NONE; ica_user_return_count := NONE|>;
                           fn_noinline := F; fn_forced_alloc_positions := FEMPTY; fn_eom := SOME 228;
                           fn_fmp_signature := SOME <|fms_has_fmp_param := F; fms_publishes := F|> |>];
                      ctx_entry := SOME "__entry"; ctx_global_reserved := []|>
End

Definition enc_mid_const_codegen_def[nocompute]:
  enc_mid_const_codegen : byte list option =
    OPTION_MAP assemble
               (case
                  generate_context_plan
                    enc_mid_const_context
                of
                  NONE => NONE
                | SOME plan =>
                  if
                    EVERY (asm_inst_target_safe (K T))
                      (execute_plan plan.cp_initial_fmp
                         (FLAT (MAP spill_region_sr_plan plan.cp_regions) ⧺
                          [SOLabel "revert"; SOPush (Lit 0w); SOEmit "DUP1"; SOEmit "REVERT"]) ⧺
                       [AsmDataHeader "code_end"])
                  then
                    SOME
                      (execute_plan plan.cp_initial_fmp
                         (FLAT (MAP spill_region_sr_plan plan.cp_regions) ⧺
                          [SOLabel "revert"; SOPush (Lit 0w); SOEmit "DUP1"; SOEmit "REVERT"]) ⧺
                       [AsmDataHeader "code_end"])
                  else NONE)
End

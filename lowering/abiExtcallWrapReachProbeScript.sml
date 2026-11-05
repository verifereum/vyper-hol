(* Concrete reachability probe; does not assert the simulation preconditions. *)
Theory abiExtcallWrapReachProbe
Ancestors
  abiDecoderWrapProbe exprLowering allocLimits selectorDispatch extCallOracleStep

Definition reach_cenv_def:
  reach_cenv = (ARB : compile_env) with
    <| ce_struct_fields := FEMPTY;
       ce_method_id := (\name tys. w2n (calldata_method_id (function_selector name []))) |>
End

Definition reach_return_def:
  reach_return = BaseT (BytesT (Dynamic 32))
End

Definition reach_wrapped_def:
  reach_wrapped = if needs_external_call_wrap reach_return
                  then TupleT [reach_return] else reach_return
End

Definition reach_compile_def:
  reach_compile = compile_external_call_kwargs reach_cenv (Lit 256w) [] []
    (SUM (MAP (type_memory_bytes reach_cenv) []))
    (abi_size_bound reach_cenv.ce_struct_fields (TupleT []))
    (reach_cenv.ce_method_id "probe" [])
    (abi_size_bound reach_cenv.ce_struct_fields reach_wrapped)
    (abi_static_size reach_cenv.ce_struct_fields reach_wrapped)
    (type_memory_bytes reach_cenv reach_return)
    T (Lit 0w) (Lit 10000w) T F (Lit 0w) reach_return reach_return
    (type_to_abi_enc_info reach_cenv.ce_struct_fields reach_cenv (TupleT []))
    (type_to_abi_dec_info reach_cenv.ce_struct_fields reach_cenv reach_wrapped)
    wrap_probe_start
End

Theorem reach_sizes:
  abi_size_bound reach_cenv.ce_struct_fields (TupleT []) = 0 /\
  abi_size_bound reach_cenv.ce_struct_fields reach_wrapped = 96 /\
  abi_static_size reach_cenv.ce_struct_fields reach_wrapped = 32 /\
  type_memory_bytes reach_cenv reach_return = 64 /\
  type_to_abi_dec_info reach_cenv.ce_struct_fields reach_cenv reach_wrapped =
    DecComplex T [(DecBytestring 32,32,64)]
Proof
  EVAL_TAC
QED

Theorem reach_alloc_limits:
  ext_call_alloc_ok reach_cenv (ExtCall T T ("probe",[],reach_return) []) []
Proof
  EVAL_TAC
QED

Theorem reach_compiler_probe:
  FST reach_compile = Var "%5"
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

(* Empty initial memory gives the real first ALLOCA base zero. *)
Definition reach_bytes_def:
  reach_bytes = REPLICATE 31 (255w:word8) ++ [224w]
End

Definition reach_outcome_def:
  reach_outcome = <| co_created := 0w; co_success := T;
    co_returnData := reach_bytes; co_accounts := empty_accounts;
    co_tStorage := empty_transient_storage; co_logs := []; co_toDelete := [] |>
End

Definition reach_state_def:
  reach_state = (init_venom_state "entry") with vs_outcomes := [reach_outcome]
End

Definition reach_func_def:
  reach_func = (ARB : ir_function) with fn_blocks :=
    (SND reach_compile).cs_blocks ++
    [<| bb_label := (SND reach_compile).cs_current_bb;
        bb_instructions := (SND reach_compile).cs_current_insts |>]
End

Theorem reach_source_rejects:
  LENGTH reach_bytes = 32 /\
  evaluate_abi_decode_return FEMPTY reach_return reach_bytes = INR "abi_decode invalid"
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

Definition reach_after_entry_def:
  reach_after_entry = case run_block 0 (ARB : venom_context)
    (THE (lookup_block "entry" reach_func.fn_blocks)) reach_state of
    OK s => s | _ => ARB
End

Theorem reach_entry_runs:
  run_block 0 ctx (THE (lookup_block "entry" reach_func.fn_blocks)) reach_state =
    OK reach_after_entry
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem reach_entry_facts:
  reach_after_entry.vs_memory = reach_bytes /\
  reach_after_entry.vs_returndata = reach_bytes /\
  reach_after_entry.vs_current_bb = "@extcall_cont_1" /\
  reach_after_entry.vs_alloca_next = 128 /\
  FLOOKUP reach_after_entry.vs_allocas 0 = SOME (0,128) /\
  reach_after_entry.vs_outcomes = [] /\
  ~reach_after_entry.vs_halted
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem reach_cont_probe:
  ?t. run_inst_seq (SND reach_compile).cs_current_insts reach_after_entry = OK t
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Definition reach_final_def:
  reach_final = case run_inst_seq (SND reach_compile).cs_current_insts
    reach_after_entry of OK s => s | _ => ARB
End

Theorem reach_cont_runs:
  run_inst_seq (SND reach_compile).cs_current_insts reach_after_entry = OK reach_final
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem reach_final_facts:
  eval_operand (FST reach_compile) reach_final = SOME 128w /\
  mload 128 reach_final = 0w /\
  reach_final.vs_alloca_next = 192 /\
  FLOOKUP reach_final.vs_allocas 9 = SOME (128,64) /\
  ~reach_final.vs_halted /\
  reach_final.vs_returndata = reach_bytes
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem reach_allocation_and_copy:
  reach_state.vs_memory = [] /\
  reach_state.vs_alloca_next = 0 /\
  0 + 128 <= 128 /\ 128 + 64 = 192 /\ 192 < 2 ** 64 /\
  read_memory 0 32 reach_after_entry = reach_bytes /\
  eval_operand (Var "%0") reach_after_entry = SOME 0w /\
  eval_operand (Var "%2") reach_after_entry = SOME 1w /\
  LENGTH reach_after_entry.vs_requests = 1 /\
  (HD reach_after_entry.vs_requests).cr_target = 256w /\
  (HD reach_after_entry.vs_requests).cr_static /\
  (HD reach_after_entry.vs_requests).cr_data_len = 4
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem reach_operational_mismatch:
  evaluate_abi_decode_return FEMPTY reach_return reach_bytes = INR "abi_decode invalid" /\
  run_block 0 ctx (THE (lookup_block "entry" reach_func.fn_blocks)) reach_state =
    OK reach_after_entry /\
  lookup_block reach_after_entry.vs_current_bb reach_func.fn_blocks =
    SOME <| bb_label := "@extcall_cont_1";
            bb_instructions := (SND reach_compile).cs_current_insts |> /\
  run_inst_seq (SND reach_compile).cs_current_insts reach_after_entry = OK reach_final /\
  eval_operand (FST reach_compile) reach_final = SOME 128w /\
  mload 128 reach_final = 0w /\
  ~(?a t. run_inst_seq (SND reach_compile).cs_current_insts
      reach_after_entry = Abort a t)
Proof
  simp[reach_source_rejects, reach_entry_runs, reach_cont_runs, reach_final_facts] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

(* This is operational helper reachability only. Not yet supplied:
   well_formed_cenv, expr_body_pre (typing, scope, compiler/function shape,
   allocation and no-effect obligations), expr_sim_inv/state_rel and the
   three operand case judgments for a full compile_call. The ordinary
   byte-list memory mode here starts empty; the helper has explicit gas,
   so it contains no GAS opcode. No claim is made about the default-GAS
   compile_call wrapper or exclusion of its existential simulation post.
   A decoder repair must prevent dynamic pointer addition wrap and keep
   every head/length read inside the original input interval. *)

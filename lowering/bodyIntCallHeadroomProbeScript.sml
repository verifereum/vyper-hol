(* Checked diagnostics for the return-buffer headroom supplier, not a
   counterexample to body_intcall_case. *)
Theory bodyIntCallHeadroomProbe
Ancestors
  compileVyper compileEnv exprLowering exprLoweringProps supportedTypes
  vyperCompiler moduleLowering words

Theorem small_memory_return_metadata:
  !sft.
    compute_func_info sft (ArrayT (BaseT (UintT 256)) (Fixed 1)) 32
      [ArrayT (BaseT (UintT 256)) (Fixed 1)] = (0,32,[F]) /\
    compute_func_info sft (BaseT (BytesT (Dynamic 0))) 32
      [BaseT (BytesT (Dynamic 0))] = (0,32,[F]) /\
    compute_func_info sft (BaseT (StringT 0)) 32
      [BaseT (StringT 0)] = (0,32,[F]) /\
    compute_func_info sft (ArrayT (BaseT (UintT 256)) (Dynamic 0)) 32
      [ArrayT (BaseT (UintT 256)) (Dynamic 0)] = (0,32,[F])
Proof
  simp[compute_func_info_def, returns_stack_count_def,
       compute_pass_via_stack_def, is_word_type_def]
QED

Theorem small_memory_return_sizes:
  !ce.
    type_memory_bytes ce (ArrayT (BaseT (UintT 256)) (Fixed 1)) = 32 /\
    type_memory_bytes ce (BaseT (BytesT (Dynamic 0))) = 32 /\
    type_memory_bytes ce (BaseT (StringT 0)) = 32 /\
    type_memory_bytes ce (ArrayT (BaseT (UintT 256)) (Dynamic 0)) = 32 /\
    type_memory_bytes ce (TupleT []) = 0 /\
    type_memory_bytes ce (ArrayT (BaseT (UintT 256)) (Fixed 0)) = 0
Proof
  simp[type_memory_bytes_def]
QED

Theorem small_memory_return_supported:
  !tops.
    supported_value_type tops (ArrayT (BaseT (UintT 256)) (Fixed 1)) /\
    supported_value_type tops (BaseT (BytesT (Dynamic 0))) /\
    supported_value_type tops (BaseT (StringT 0)) /\
    supported_value_type tops (ArrayT (BaseT (UintT 256)) (Dynamic 0)) /\
    ~supported_value_type tops (TupleT []) /\
    ~supported_value_type tops (ArrayT (BaseT (UintT 256)) (Fixed 0))
Proof
  simp[supported_value_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def,
       supported_int_width_def]
QED

(* A single-word aggregate is memory-passed, not a stack word. These named
   fixtures keep compiler evaluation bounded and make the generated source
   signature explicit. *)
Definition headroom_probe_type_def:
  headroom_probe_type = ArrayT (BaseT (UintT 256)) (Fixed 1)
End

Definition headroom_probe_tops_def:
  headroom_probe_tops =
    [FunctionDecl Internal Pure F F "callee"
       [("x", headroom_probe_type)] [] headroom_probe_type
       [Return (SOME (Name headroom_probe_type "x"))];
     FunctionDecl Internal Pure F F "caller"
       [("x",headroom_probe_type)] [] headroom_probe_type
       [Return (SOME (Call headroom_probe_type (IntCall (NONE,"callee"))
          [Name headroom_probe_type "x"] NONE))]]
End

Theorem headroom_probe_generated_metadata:
  build_func_info (K []) headroom_probe_tops "callee" = (0,32,[F])
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Definition headroom_probe_callee_env_def:
  headroom_probe_callee_env =
    build_compile_env headroom_probe_tops Internal Pure "callee"
      [("x",headroom_probe_type)] headroom_probe_type
      [Return (SOME (Name headroom_probe_type "x"))] F
End

Definition headroom_probe_caller_env_def:
  headroom_probe_caller_env =
    build_compile_env headroom_probe_tops Internal Pure "caller"
      [("x",headroom_probe_type)] headroom_probe_type [] F
End

Theorem headroom_probe_caller_allocations:
  let st = SND (compile_expr headroom_probe_caller_env headroom_probe_type
      (Call headroom_probe_type (IntCall (NONE,"callee"))
        [Name headroom_probe_type "x"] NONE)
      (initial_compile_state "caller")) in
  MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) st.cs_current_insts) = [32;32]
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem headroom_probe_callee_allocations:
  let st = SND (compile_internal_function headroom_probe_callee_env
      [("x",F)] T F 0 F F F 0
      [Return (SOME (Name headroom_probe_type "x"))]
      (SOME headroom_probe_type) (initial_compile_state "callee")) in
  MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) st.cs_current_insts) = []
Proof
  EVAL_TAC >> simp[dimword_def]
QED

(* Unlike the direct-return-argument example, a reverting callee needs no
   memory-passed argument. Its caller has only the 32-byte return buffer.
   This tests the proposed budget supplier, not the simulation theorem. *)
Definition headroom_revert_tops_def:
  headroom_revert_tops =
    [FunctionDecl Internal Pure F F "callee" [] [] headroom_probe_type
       [Raise RaiseBare];
     FunctionDecl Internal Pure F F "caller" [] [] headroom_probe_type
       [Return (SOME (Call headroom_probe_type (IntCall (NONE,"callee"))
          [] NONE))]]
End

Definition headroom_revert_env_def:
  headroom_revert_env name =
    build_compile_env headroom_revert_tops Internal Pure name []
      headroom_probe_type [] F
End

Definition headroom_revert_caller_state_def:
  headroom_revert_caller_state =
    SND (compile_internal_function (headroom_revert_env "caller")
      [] T F 0 F F F 0
      [Return (SOME (Call headroom_probe_type (IntCall (NONE,"callee"))
          [] NONE))] (SOME headroom_probe_type)
      (initial_compile_state "caller"))
End

Definition headroom_revert_callee_state_def:
  headroom_revert_callee_state =
    SND (compile_internal_function (headroom_revert_env "callee")
      [] T F 0 F F F 0 [Raise RaiseBare] (SOME headroom_probe_type)
      (initial_compile_state "callee"))
End

Theorem headroom_revert_generated_budget:
  build_func_info (K []) headroom_revert_tops "callee" = (0,32,[]) /\
  MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA)
      (headroom_revert_caller_state.cs_current_insts ++
       FLAT (MAP (\b. b.bb_instructions)
         headroom_revert_caller_state.cs_blocks))) = [32] /\
  MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA)
      (headroom_revert_callee_state.cs_current_insts ++
       FLAT (MAP (\b. b.bb_instructions)
         headroom_revert_callee_state.cs_blocks))) = []
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem headroom_32_credit_insufficient:
  let frontier = dimword (:256) - 33 in
    frontier + 1 * 32 < dimword (:256) /\
    ~(frontier + 64 < dimword (:256))
Proof
  simp[dimword_def]
QED

Theorem headroom_revert_unit_budget:
  let caller_ctx = FST (extract_context "caller" headroom_revert_caller_state) in
  let callee_ctx = FST (extract_context "callee" headroom_revert_callee_state) in
  unit_alloca_frame
    (caller_ctx with ctx_functions :=
       caller_ctx.ctx_functions ++ callee_ctx.ctx_functions) = 32
Proof
  EVAL_TAC >> simp[dimword_def]
QED

(* Diagnostic conclusion: the direct-return-argument caller pays 32 for the
   return buffer and 32 for argument staging. That second allocation is NOT
   compulsory for all memory-return signatures: the no-argument reverting
   example above emits just 32 bytes in the entire two-function unit.
   headroom_32_credit_insufficient witnesses only the numeric room conjunct
   at a near-limit frontier. No body_inv, stmt_state_rel, successful source
   return, or complete lower_vyper_runtime_unit witness is asserted here.
   In particular this is not falsehood evidence for body_intcall_case. *)

(* The existing valueCopy size-bound entry point needs only a TYPE-size
   bound, not a destination-address bound. This arithmetic supplies it from
   the compiler's normal allocation limit even in the 32-byte diagnostic. *)
Theorem alloc_limit_supplies_copy_size_slack:
  !sz. sz < 2 ** 64 ==> sz + 64 < dimword (:256)
Proof
  simp[dimword_def] >> rpt strip_tac >> decide_tac
QED

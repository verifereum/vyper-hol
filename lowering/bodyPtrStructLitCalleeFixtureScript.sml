(* Named concrete source fixtures keep evaluation terms small.  They are
   actual expression/statement compiler inputs, not hand-written machine code.
   Full run and ghost certificates are separate obligations. *)
Theory bodyPtrStructLitCalleeFixture
Ancestors compileVyper exprLowering stmtLowering compileEnv vyperAST list
  exprLoweringProps venomState ptrDiscipline
Libs wordsLib intLib

Definition structlit_callee_type_def:
  structlit_callee_type n =
    TupleT [BaseT (BytesT (Dynamic n)); ArrayT (BaseT BoolT) (Dynamic 1)]
End

Definition structlit_callee_expr_def:
  structlit_callee_expr singleton =
    Builtin (structlit_callee_type 33) (MakeArray NONE (Fixed 2))
      [Literal (BaseT (BytesT (Dynamic 33))) (BytesL []);
       Builtin (ArrayT (BaseT BoolT) (Dynamic 1))
         (MakeArray (SOME (BaseT BoolT)) (Dynamic 1))
         (if singleton then [Literal (BaseT BoolT) (BoolL T)] else [])]
End

Definition structlit_callee_env_def:
  structlit_callee_env singleton =
    build_compile_env [] Internal Pure "structlit_probe" []
      (structlit_callee_type 33)
      [Return (SOME (structlit_callee_expr singleton))] F
End

Definition structlit_callee_compiled_def:
  structlit_callee_compiled singleton =
    lower_value compile_expr (structlit_callee_env singleton)
      (structlit_callee_type 33) (structlit_callee_expr singleton)
      (initial_compile_state "probe")
End

Theorem structlit_callee_source_type:
  !b. expr_type (structlit_callee_expr b) = structlit_callee_type 33
Proof
  simp[structlit_callee_expr_def, expr_type_def]
QED

Theorem structlit_callee_expression_shape:
  MAP (\i. i.inst_opcode)
    (SND (structlit_callee_compiled F)).cs_current_insts =
    [ALLOCA; ALLOCA; MSTORE; ADD; MLOAD; ADD; AND; ADD; MCOPY;
     ALLOCA; MSTORE; ADD; MCOPY]
Proof
  EVAL_TAC
QED

(* The internal-call frame reserves words 0 and 32 for the return-buffer
   pointer and return PC, followed by a 160-byte caller return buffer.
   Named initial state is needed for concrete evaluation of the protocol. *)
Definition structlit_callee_initial_def:
  structlit_callee_initial =
    (write_memory 0 (REPLICATE 31 0w ++ [64w] ++ REPLICATE 31 0w ++ [1w])
      (init_venom_state "probe")) with
       <| vs_alloca_next := 224; vs_fmp := 4096w;
          vs_initial_fmp := 4096w; vs_call_entry_fmp := 4096w |>
End

(* Concrete execution fixture, evaluated through the real instruction semantics. *)
Definition structlit_callee_run_def:
  structlit_callee_run b =
    run_inst_seq (SND (structlit_callee_compiled b)).cs_current_insts
      structlit_callee_initial
End

Theorem structlit_callee_empty_run:
  (case structlit_callee_run F of
     OK s => SOME (s.vs_fmp, lookup_var "%0" s, LENGTH s.vs_memory)
   | _ => NONE) = SOME (4096w, SOME 224w, 448)
Proof
  EVAL_TAC
QED

Theorem structlit_callee_singleton_run:
  (case structlit_callee_run T of
     OK s => SOME (lookup_var "%0" s, LENGTH s.vs_memory,
                   read_memory 320 64 s)
   | _ => NONE) = SOME (SOME 224w, 480,
       REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [1w])
Proof
  EVAL_TAC
QED

(* The statement fixture includes the real internal-return protocol. *)
Definition structlit_callee_return_compiled_def:
  structlit_callee_return_compiled b =
    compile_stmt (structlit_callee_env b) NoLoop (structlit_callee_type 33)
      (Return (SOME (structlit_callee_expr b))) (initial_compile_state "probe")
End

Theorem structlit_callee_return_shape:
  MAP (\i. i.inst_opcode)
    (SND (structlit_callee_return_compiled F)).cs_current_insts =
    [ALLOCA; ALLOCA; MSTORE; ADD; MLOAD; ADD; AND; ADD; MCOPY;
     ALLOCA; MSTORE; ADD; MCOPY; MLOAD; MLOAD; MCOPY; RET]
Proof
  EVAL_TAC
QED

Theorem structlit_callee_return_expression_prefix:
  TAKE 13 (SND (structlit_callee_return_compiled F)).cs_current_insts =
    (SND (structlit_callee_compiled F)).cs_current_insts
Proof
  EVAL_TAC
QED

Theorem structlit_callee_return_store_run:
  (case run_inst_seq
     (TAKE 16 (SND (structlit_callee_return_compiled F)).cs_current_insts)
     structlit_callee_initial of
     OK s => SOME (lookup_var "%9" s, lookup_var "%10" s,
                   read_memory 64 160 s)
   | _ => NONE) = SOME (SOME 1w, SOME 64w, REPLICATE 160 0w)
Proof
  EVAL_TAC
QED

(* Experimental executable ghost projection: inst_seq_ptr is relational and
   does not compute its output taint.  This fold follows exactly its successful
   transitions, and is used only for concrete fixture certificates. *)
Definition structlit_callee_taint_run_def:
  structlit_callee_taint_run [] s tn = tn /\
  structlit_callee_taint_run (i::is) s tn =
    case step_inst_base i s of
      OK u => structlit_callee_taint_run is
        (u with vs_inst_idx := SUC s.vs_inst_idx) (step_taint i s u tn)
    | _ => tn
End

Theorem structlit_callee_empty_header_probe:
  320 NOTIN
    (structlit_callee_taint_run
      (SND (structlit_callee_compiled F)).cs_current_insts
      structlit_callee_initial entry_taint).t_mem
Proof
  EVAL_TAC >> simp[] >> rpt gen_tac >>
  Cases_on `aid = 9` >> Cases_on `aid = 1` >> Cases_on `aid = 0` >> simp[]
QED


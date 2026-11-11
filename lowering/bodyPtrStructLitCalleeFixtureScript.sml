(* Named concrete source fixtures keep evaluation terms small.  They are
   actual expression/statement compiler inputs, not hand-written machine code.
   Full run and ghost certificates are separate obligations. *)
Theory bodyPtrStructLitCalleeFixture
Ancestors compileVyper exprLowering stmtLowering compileEnv vyperAST list
  exprLoweringProps venomState ptrDiscipline bodyPtrStructLitGhostNormalize
  fragExecPtr allocationPtr ghostPcTransportPtr
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


Theorem structlit_callee_first_instruction:
  HD (SND (structlit_callee_compiled F)).cs_current_insts =
    mk_inst 0 ALLOCA [Lit 160w] ["%0"]
Proof
  EVAL_TAC
QED

(* Prefix states isolate concrete machine computation from symbolic ghost
   normalization; the fallback is irrelevant to successful-step certificates. *)
Definition structlit_callee_state_def:
  structlit_callee_state b n =
    case run_inst_seq (TAKE n (SND (structlit_callee_compiled b)).cs_current_insts)
           structlit_callee_initial of
      OK s => s
    | _ => structlit_callee_initial
End

Theorem structlit_callee_first_ghost:
  !s1 PG G tn.
    step_inst_base (HD (SND (structlit_callee_compiled F)).cs_current_insts)
      structlit_callee_initial = OK s1 ==>
    step_prov PG G (HD (SND (structlit_callee_compiled F)).cs_current_insts) s1 =
      G |+ ("%0",(224,160)) /\
    step_taint (HD (SND (structlit_callee_compiled F)).cs_current_insts)
      structlit_callee_initial s1 tn =
      tn with <| t_mem := tn.t_mem UNION {i | 224 <= i /\ i < 384};
                 t_var := tn.t_var |+ ("%0",{}) |>
Proof
  rpt gen_tac >> rewrite_tac[structlit_callee_first_instruction] >> strip_tac >>
  drule_at Any fresh_alloca_ghost >>
  simp[structlit_callee_initial_def, init_venom_state_def,
       write_memory_def] >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >> simp[]
QED

Theorem structlit_callee_header_store_instruction:
  EL 2 (SND (structlit_callee_compiled F)).cs_current_insts =
    mk_inst 2 MSTORE [Var "%1"; Lit 0w] []
Proof
  EVAL_TAC
QED

Theorem structlit_callee_header_store_address:
  eval_operand (Var "%1") (structlit_callee_state F 2) = SOME 384w
Proof
  EVAL_TAC
QED

Theorem structlit_callee_header_store_clean:
  !tn s1 i. 384 <= i /\ i < 416 ==>
    i NOTIN (step_taint
      (EL 2 (SND (structlit_callee_compiled F)).cs_current_insts)
      (structlit_callee_state F 2) s1 tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[structlit_callee_header_store_instruction] >>
  irule mstore_word_clean >>
  simp[structlit_callee_header_store_address, eval_operand_def, op_taint_def]
QED

Theorem structlit_callee_bytes_copy_instruction:
  EL 8 (SND (structlit_callee_compiled F)).cs_current_insts =
    mk_inst 8 MCOPY [Var "%2"; Var "%1"; Var "%6"] []
Proof
  EVAL_TAC
QED

Theorem structlit_callee_bytes_copy_operands:
  eval_operand (Var "%2") (structlit_callee_state F 8) = SOME 224w /\
  eval_operand (Var "%1") (structlit_callee_state F 8) = SOME 384w /\
  eval_operand (Var "%6") (structlit_callee_state F 8) = SOME 32w
Proof
  EVAL_TAC
QED

Theorem structlit_callee_bytes_copy_clean:
  !tn s1.
    (!j. 384 <= j /\ j < 416 ==> j NOTIN tn.t_mem) ==>
    !i. 224 <= i /\ i < 256 ==>
      i NOTIN (step_taint
        (EL 8 (SND (structlit_callee_compiled F)).cs_current_insts)
        (structlit_callee_state F 8) s1 tn).t_mem
Proof
  rpt gen_tac >> disch_tac >> gen_tac >> strip_tac >>
  rewrite_tac[structlit_callee_bytes_copy_instruction] >>
  irule structlit_mcopy_operand_range_clean >>
  simp[structlit_callee_bytes_copy_operands]
QED

Theorem structlit_callee_store_to_copy_steps:
  !n k. MEM n [2;3;4;5;6;7;8] ==>
    step_inst_base (EL n (SND (structlit_callee_compiled F)).cs_current_insts)
      (structlit_callee_state F n with vs_inst_idx := k) =
    OK (structlit_callee_state F (SUC n) with vs_inst_idx := k)
Proof
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem structlit_callee_intermediate_memory_fields:
  !n. MEM n [3;4;5;6;7] ==>
    (structlit_callee_state F (SUC n)).vs_allocas =
      (structlit_callee_state F n).vs_allocas /\
    (structlit_callee_state F (SUC n)).vs_fmp =
      (structlit_callee_state F n).vs_fmp
Proof
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem structlit_callee_intermediate_writes:
  !n tn. MEM n [3;4;5;6;7] ==>
    step_writes (EL n (SND (structlit_callee_compiled F)).cs_current_insts)
      (structlit_callee_state F n) (structlit_callee_state F (SUC n)) = [] /\
    written_taint tn (EL n (SND (structlit_callee_compiled F)).cs_current_insts)
      (structlit_callee_state F n) = {}
Proof
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem structlit_callee_intermediate_memory_taint:
  !n tn. MEM n [3;4;5;6;7] ==>
    !t. t = structlit_callee_state F (SUC n) ==>
    (step_taint (EL n (SND (structlit_callee_compiled F)).cs_current_insts)
      (structlit_callee_state F n) t tn).t_mem = tn.t_mem
Proof
  rpt strip_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
  irule structlit_step_taint_memory_frame >>
  simp[structlit_callee_intermediate_memory_fields,
       structlit_callee_intermediate_writes]
QED

Theorem structlit_callee_taint_run_step:
  !n k is tn. MEM n [2;3;4;5;6;7;8] ==>
    structlit_callee_taint_run
      (EL n (SND (structlit_callee_compiled F)).cs_current_insts :: is)
      (structlit_callee_state F n with vs_inst_idx := k) tn =
    structlit_callee_taint_run is
      (structlit_callee_state F (SUC n) with vs_inst_idx := SUC k)
      (step_taint (EL n (SND (structlit_callee_compiled F)).cs_current_insts)
         (structlit_callee_state F n) (structlit_callee_state F (SUC n)) tn)
Proof
  rpt strip_tac >>
  simp[structlit_callee_taint_run_def, structlit_callee_store_to_copy_steps]
QED

Theorem structlit_callee_store_to_copy_segment:
  TAKE 7 (DROP 2 (SND (structlit_callee_compiled F)).cs_current_insts) =
    MAP (\n. EL n (SND (structlit_callee_compiled F)).cs_current_insts)
        [2;3;4;5;6;7;8]
Proof
  EVAL_TAC
QED

Theorem structlit_callee_store_start_idx:
  structlit_callee_state F 2 with vs_inst_idx := 0 = structlit_callee_state F 2
Proof
  EVAL_TAC
QED

Theorem structlit_callee_store_to_copy_clean:
  !tn i. 224 <= i /\ i < 256 ==>
    i NOTIN (structlit_callee_taint_run
      (TAKE 7 (DROP 2 (SND (structlit_callee_compiled F)).cs_current_insts))
      (structlit_callee_state F 2) tn).t_mem
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[structlit_callee_store_to_copy_segment, MAP] >>
  once_rewrite_tac[GSYM structlit_callee_store_start_idx] >>
  simp[structlit_callee_taint_run_step] >>
  rewrite_tac[structlit_callee_taint_run_def] >>
  irule structlit_callee_bytes_copy_clean >>
  simp[structlit_callee_intermediate_memory_taint,
       structlit_callee_header_store_clean]
QED

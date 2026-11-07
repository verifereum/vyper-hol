Theory bodyPtrBytestringBuiltinsConcatFrameProbe
Ancestors bodyPtrBytestringBuiltinsConcatAdmissionProbe

(* The bare fixture cannot represent order_ptr_source's arr local.  This
   closed frame instead has no locals; block 1 supplies a valid hash window. *)
Definition concat_frame_env_def:
  concat_frame_env = build_compile_env [] External Nonpayable "f" [] NoneT [] F
End

Definition concat_frame_cx_def:
  concat_frame_cx = order_ptr_cx with txn :=
    (order_ptr_cx.txn with <|block_number := 1; block_hashes := [0w]|>)
End

Definition concat_frame_source_def:
  concat_frame_source = vyperState$empty_state with outcomes := SOME []
End

Definition concat_frame_start_def:
  concat_frame_start = (init_venom_state "entry") with
    <|vs_alloca_next := 256;
      vs_block_ctx := ((init_venom_state "entry").vs_block_ctx with
        <|bc_number := 1w; bc_blockhash := K 0w|>)|>
End

Theorem concat_frame_call_context:
  call_ctx_rel concat_frame_cx.txn concat_frame_start.vs_call_ctx
    concat_frame_start.vs_tx_ctx concat_frame_start.vs_block_ctx
Proof
  EVAL_TAC >> simp[]
QED

Theorem concat_frame_state_rel:
  !func. state_rel func concat_frame_env concat_frame_cx
    concat_frame_source concat_frame_start
Proof
  gen_tac >>
  simp[compileEnvTheory.state_rel_def, concat_frame_call_context] >>
  EVAL_TAC >> simp[]
QED

Theorem concat_frame_ghost:
  ghost_inv NONE concat_frame_env concat_frame_cx concat_frame_source
    FEMPTY entry_taint concat_frame_start
Proof
  EVAL_TAC >> simp[]
QED

(* A STOP continuation makes the concrete fragment a complete function. *)
Definition concat_frame_fn_def:
  concat_frame_fn = mk_raw_function "f"
    [<|bb_label := "entry";
       bb_instructions := (SND concat_probe_compiled).cs_current_insts ++
         [mk_inst 16 STOP [] []]|>]
End

Definition concat_frame_ctx_def:
  concat_frame_ctx = order_frame_unit.cu_context with
    ctx_functions := [concat_frame_fn]
End

Theorem concat_frame_alloca_inv:
  alloca_inv concat_frame_start
Proof
  EVAL_TAC >> simp[]
QED

(* body_inv fixes the execution context to an actual lowered unit.  The
   empty-program unit cannot host this synthetic function. *)
Theorem concat_frame_function_absent:
  lookup_function concat_frame_fn.fn_name
    order_frame_unit.cu_context.ctx_functions = NONE
Proof
  EVAL_TAC >> simp[listTheory.INDEX_FIND_def]
QED

Theorem concat_frame_empty_unit_no_state:
  !s. ~stmt_state_rel order_frame_unit.cu_context concat_frame_fn
    concat_frame_env concat_frame_cx concat_frame_source s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.alloca_room_def, concat_frame_function_absent]
QED

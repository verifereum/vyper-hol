(* Live generated LOG probe. Independent of the admitted correctness root. *)
Theory logFrameChecks
Ancestors
  codegen stackPlanGenCompute stackPlanTypes planExec symbolResolve
  codegenRel asmSem venomExecSemantics venomInst venomState
  frameOutcome callTrace vfmExecution vfmContext vfmOperation vfmConstants
  list finite_map words
Libs wordsLib finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;

Definition log_probe_fn_def:
  log_probe_fn = (mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [instruction 0 MSTORE [Lit 0w; Lit 7w] [];
       instruction 1 LOG [Lit 1w; Lit 9w; Lit 32w; Lit 0w] [];
       instruction 2 STOP [] []] |>]) with fn_eom := SOME 32
End
Definition log_probe_ctx_def:
  log_probe_ctx = mk_venom_context [log_probe_fn] (SOME "main")
End
Theorem log_probe_plan:
  ?cp. generate_context_plan log_probe_ctx = SOME cp
Proof
  EVAL_TAC >> simp[stackModelTheory.stack_find_def] >> EVAL_TAC >>
  simp[listTheory.SET_TO_LIST_THM] >> EVAL_TAC
QED

Definition log_probe_prog_def:
  log_probe_prog = [AsmLabel "entry"; AsmPush [7w]; AsmPush [];
    AsmOp "MSTORE"; AsmPush [9w]; AsmPush [32w]; AsmPush [];
    AsmOp "LOG1"; AsmOp "STOP"; AsmLabel "revert"; AsmPush [];
    AsmOp "DUP1"; AsmOp "REVERT"]
End
Theorem log_probe_generated:
  OPTION_MAP (\cp. execute_plan cp.cp_initial_fmp (context_plan_ops cp))
    (generate_context_plan log_probe_ctx) = SOME log_probe_prog
Proof
  EVAL_TAC >> simp[stackModelTheory.stack_find_def] >> EVAL_TAC >>
  simp[listTheory.SET_TO_LIST_THM] >> EVAL_TAC
QED

Definition log_probe_asm_def:
  log_probe_asm = <| as_stack := []; as_memory := []; as_accounts := empty_accounts;
    as_transient := empty_transient_storage; as_returndata := [];
    as_logs := []; as_pc := 0; as_call_ctx := empty_call_context;
    as_tx_ctx := empty_tx_context; as_block_ctx := empty_block_context;
    as_code := []; as_prev_hashes := []; as_outcomes := [];
    as_requests := []; as_gas_readings := [] |>
End
Definition log_probe_es_def:
  log_probe_es = make_asm_call_state log_probe_asm 0w 10000 0 []
    (assemble log_probe_prog) F
End

Theorem log_probe_code:
  assemble log_probe_prog =
    [0x5bw;0x60w;7w;0x5fw;0x52w;0x60w;9w;0x60w;32w;0x5fw;
     0xa1w;0w;0x5bw;0x5fw;0x80w;0xfdw]
Proof
  EVAL_TAC
QED

Theorem log_probe_parsed:
  parse_code 0 FEMPTY (assemble log_probe_prog) =
    FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [7w]) |+ (3, Push 0 []) |+
    (4, MStore) |+ (5, Push 1 [9w]) |+ (7, Push 1 [32w]) |+ (9, Push 0 []) |+
    (10, Log 1) |+ (11, Stop) |+ (12, JumpDest) |+ (13, Push 0 []) |+
    (14, Dup 0) |+ (15, Revert)
Proof
  simp[log_probe_code] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, opcode_def, dimword_8] >>
  simp[Once parse_code_def] >> EVAL_TAC
QED
val () = computeLib.add_funs [log_probe_code, log_probe_parsed];

(* Runtime evaluation is deliberately not asserted here: a direct EVAL of
   run_call exceeds the tactic budget. A staged step/OWHILE boundary is needed
   to avoid re-expanding the full fresh frame and parser at every step. *)

val _ = List.app (fn (name,th) =>
  if null (List.filter (fn s => s <> "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("oracle dependency in " ^ name)) (DB.thms "logFrameChecks");

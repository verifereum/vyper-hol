(*
 * Label-symbolic assembly semantics and the finalizer contract
 *
 * An assembly finalizer (such as the final assembly optimizer) deletes
 * instructions and renames label pushes, so every later code address
 * moves. This semantics runs an asm_inst program with label values kept
 * symbolic: AsmPushLabel l pushes Lab l 0 and AsmPushOfst l d pushes
 * Lab l d, instead of a resolved byte offset. A program whose run never
 * inspects a label value numerically then behaves the same before and
 * after the finalizer, and the contract compares the two runs.
 *
 * Everything that isn't about labels is the concrete gasless semantics
 * of asmSem: a step hands its concrete operands to asm_step_op and lifts
 * the result back. GAS readings and call outcomes are oracle lists in the
 * state, so both programs consume the same ones.
 *
 * Label values may be used only like this; anything else is SymBad:
 *   - stack shuffles (POP, DUPn, SWAPn) move them freely;
 *   - JUMP, and JUMPI when it jumps, take Lab l 0 for a code label
 *     (AsmLabel l) and go to that label; JUMPI's condition is concrete,
 *     and when it is zero the target is ignored, as in asm_jumpi;
 *   - ADD of Lab l d and a concrete w, in either order, gives
 *     Lab l (d + w2n w) when l is a data header (AsmDataHeader l); deltas
 *     stay below 2^255, so the concrete address never wraps;
 *   - CODECOPY from Lab l d, for a data header l, copies from the bytes
 *     the data environment gives for l; the environment is a parameter,
 *     shared by the program and its finalized version;
 *   - MSTORE writes one to memory, which records it byte by byte in a side
 *     map; MLOAD of 32 intact bytes of one label value gives it back.
 * Reading memory that holds label bytes in any other way is SymBad, and a
 * write over label bytes forgets them. Reading the code bytes themselves
 * (CODESIZE, CODECOPY from a concrete offset) is SymBad too, since the
 * finalizer changes them. EXTCODE* read the accounts, which both programs
 * share, so they stay concrete.
 *
 * TOP-LEVEL:
 *   sval, sym_state, sym_result — values, states and results
 *   sym_step, sym_run          — single step and fuel-based run
 *   asm_static_wf              — static label and data-layout well-formedness
 *   label_disciplined          — no label misuse from a start state
 *   asm_refines                — the contract between two programs
 *   finalizer_correct          — a finalizer's outputs refine its inputs
 *)

Theory asmSymSem
Ancestors
  asmSem asmWf asmOptimizer

(* ===== Values, states, results ===== *)

Datatype:
  sval = Val bytes32 | Lab string num
End

(* sym_base holds everything but the stack, which is sym_stack;
   sym_base.as_stack stays []. sym_mem_labels maps a memory byte holding
   part of a label value to (label, delta, byte index in the word); the
   byte itself in sym_base.as_memory is a placeholder. *)
Datatype:
  sym_state = <|
    sym_base : asm_state;
    sym_stack : sval list;
    sym_mem_labels : num |-> (string # num # num)
  |>
End

(* SymError is an ordinary failure, as AsmError; SymBad is a label misuse. *)
Datatype:
  sym_result =
    | SymOK sym_state
    | SymHalt sym_state
    | SymRevert sym_state
    | SymFault sym_state
    | SymError string
    | SymBad string
End

Definition sval_val_def:
  sval_val (Val w) = SOME w ∧
  sval_val (Lab _ _) = NONE
End

Definition sym_init_def:
  sym_init (s : asm_state) =
    <| sym_base := s with <| as_stack := []; as_pc := 0; as_code := [] |>;
       sym_stack := MAP Val s.as_stack;
       sym_mem_labels := FEMPTY |>
End

(* ===== Operand counts and memory ranges of the concrete opcodes ===== *)

(* Stack items each opcode of asm_step_op pops, apart from DUPn and SWAPn,
   which sym_step_op shuffles itself. *)
Definition asm_op_arity_table_def:
  asm_op_arity_table : (string # num) list = [
    ("ADD", 2); ("MUL", 2); ("SUB", 2); ("DIV", 2); ("SDIV", 2);
    ("MOD", 2); ("SMOD", 2); ("EXP", 2); ("ADDMOD", 3); ("MULMOD", 3);
    ("LT", 2); ("GT", 2); ("SLT", 2); ("SGT", 2); ("EQ", 2);
    ("ISZERO", 1);
    ("AND", 2); ("OR", 2); ("XOR", 2); ("NOT", 1); ("SHL", 2); ("SHR", 2);
    ("SAR", 2); ("SIGNEXTEND", 2); ("BYTE", 2);
    ("POP", 1); ("MLOAD", 1); ("MSTORE", 2); ("MSTORE8", 2); ("MCOPY", 3);
    ("MSIZE", 0); ("SLOAD", 1); ("SSTORE", 2); ("TLOAD", 1); ("TSTORE", 2);
    ("SHA3", 2);
    ("JUMP", 1); ("JUMPI", 2); ("JUMPDEST", 0); ("STOP", 0); ("RETURN", 2);
    ("REVERT", 2); ("INVALID", 0);
    ("CALL", 7); ("STATICCALL", 6); ("DELEGATECALL", 6); ("CREATE", 3);
    ("CREATE2", 4); ("SELFDESTRUCT", 1);
    ("CALLDATACOPY", 3); ("RETURNDATACOPY", 3); ("CODECOPY", 3);
    ("EXTCODECOPY", 4);
    ("CALLER", 0); ("ADDRESS", 0); ("CALLVALUE", 0); ("GAS", 0);
    ("CALLDATASIZE", 0); ("CALLDATALOAD", 1); ("ORIGIN", 0);
    ("GASPRICE", 0); ("CHAINID", 0); ("COINBASE", 0); ("TIMESTAMP", 0);
    ("NUMBER", 0); ("PREVRANDAO", 0); ("GASLIMIT", 0); ("BASEFEE", 0);
    ("BLOBBASEFEE", 0); ("BLOCKHASH", 1); ("BLOBHASH", 1); ("BALANCE", 1);
    ("SELFBALANCE", 0); ("CODESIZE", 0); ("EXTCODESIZE", 1);
    ("EXTCODEHASH", 1); ("RETURNDATASIZE", 0);
    ("LOG0", 2); ("LOG1", 3); ("LOG2", 4); ("LOG3", 5); ("LOG4", 6)]
End

(* Unknown opcodes get 0: asm_step_op fails on them whatever the stack. *)
Definition asm_op_arity_def:
  asm_op_arity name =
    case ALOOKUP asm_op_arity_table name of SOME n => n | NONE => 0
End

Definition in_mem_range_def:
  in_mem_range off sz (i : num) ⇔ off ≤ i ∧ i < off + sz
End

(* Memory bytes an opcode may read, given its operands (top first). A call
   writes only the returned prefix of its output range, so that range is
   counted here rather than as a write: label bytes there are SymBad, not
   forgotten. *)
Definition asm_op_mem_reads_def:
  asm_op_mem_reads name (args : bytes32 list) =
    let a = λn. w2n (EL n args) in
    if name = "MLOAD" then in_mem_range (a 0) 32
    else if MEM name ["SHA3"; "RETURN"; "REVERT"] ∨
            IS_SOME (ALOOKUP log_table name) then in_mem_range (a 0) (a 1)
    else if MEM name ["MCOPY"; "CREATE"; "CREATE2"] then
      in_mem_range (a 1) (a 2)
    else if name = "CALL" then
      (λi. in_mem_range (a 3) (a 4) i ∨ in_mem_range (a 5) (a 6) i)
    else if MEM name ["STATICCALL"; "DELEGATECALL"] then
      (λi. in_mem_range (a 2) (a 3) i ∨ in_mem_range (a 4) (a 5) i)
    else (λi. F)
End

(* Memory bytes an opcode overwrites exactly. *)
Definition asm_op_mem_writes_def:
  asm_op_mem_writes name (args : bytes32 list) =
    let a = λn. w2n (EL n args) in
    if name = "MSTORE" then in_mem_range (a 0) 32
    else if name = "MSTORE8" then in_mem_range (a 0) 1
    else if MEM name ["MCOPY"; "CALLDATACOPY"; "RETURNDATACOPY"; "CODECOPY"]
      then in_mem_range (a 0) (a 2)
    else if name = "EXTCODECOPY" then in_mem_range (a 1) (a 3)
    else (λi. F)
End

Definition mem_labels_hit_def:
  mem_labels_hit (m : num |-> (string # num # num)) P ⇔
    ∃i. i ∈ FDOM m ∧ P i
End

Definition mem_labels_clear_def:
  mem_labels_clear (m : num |-> (string # num # num)) P =
    DRESTRICT m (λi. ¬P i)
End

(* The label value whose 32 bytes are intact at off, if any. *)
Definition mem_label_at_def:
  mem_label_at (m : num |-> (string # num # num)) off =
    case FLOOKUP m off of
      SOME (l, d, j) =>
        if j = 0 ∧
           EVERY (λi. FLOOKUP m (off + i) = SOME (l, d, i)) (COUNT_LIST 32)
        then SOME (l, d) else NONE
    | NONE => NONE
End

(* ===== Steps ===== *)

Definition sym_set_stack_def:
  sym_set_stack stk ss =
    SymOK (ss with <| sym_base := asm_next ss.sym_base; sym_stack := stk |>)
End

(* Lift a concrete step that ran on the top k stack items. *)
Definition sym_lift_def:
  sym_lift k labs ss r =
    let lift = λs. ss with <| sym_base := s with as_stack := [];
                              sym_stack := MAP Val s.as_stack ++
                                           DROP k ss.sym_stack;
                              sym_mem_labels := labs |> in
    case r of
      AsmOK s => SymOK (lift s)
    | AsmHalt s => SymHalt (lift s)
    | AsmRevert s => SymRevert (lift s)
    | AsmFault s => SymFault (lift s)
    | AsmError e => SymError e
End

(* An opcode on concrete operands: the concrete step, provided it reads no
   label bytes in memory; label bytes it overwrites are forgotten. *)
Definition sym_step_concrete_def:
  sym_step_concrete name ss =
    let k = asm_op_arity name in
    if LENGTH ss.sym_stack < k then
      SymError (name ++ ": stack underflow")
    else
      case OPT_MMAP sval_val (TAKE k ss.sym_stack) of
        NONE => SymBad ("label value used by " ++ name)
      | SOME args =>
          if mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args)
          then SymBad ("label bytes read by " ++ name)
          else
            sym_lift k
              (mem_labels_clear ss.sym_mem_labels
                 (asm_op_mem_writes name args)) ss
              (asm_step_op FEMPTY name (ss.sym_base with as_stack := args))
End

Definition sym_data_label_def:
  sym_data_label p (env : string |-> byte list) l ⇔
    MEM (AsmDataHeader l) p ∧ l ∈ FDOM env
End

Definition sym_jump_dest_def:
  sym_jump_dest p (Lab l d) = (if d = 0 then INDEX_OF (AsmLabel l) p
                               else NONE) ∧
  sym_jump_dest p (Val _) = NONE
End

Definition sym_jump_def:
  sym_jump p ss =
    case ss.sym_stack of
      dest :: stk =>
        (case sym_jump_dest p dest of
           SOME pc => SymOK (ss with <| sym_base := ss.sym_base with
                                          as_pc := pc;
                                        sym_stack := stk |>)
         | NONE => SymBad "jump target")
    | [] => SymError "jump: stack underflow"
End

Definition sym_jumpi_def:
  sym_jumpi p ss =
    case ss.sym_stack of
      dest :: Val c :: stk =>
        if c = 0w then sym_set_stack stk ss
        else
          (case sym_jump_dest p dest of
             SOME pc => SymOK (ss with <| sym_base := ss.sym_base with
                                            as_pc := pc;
                                          sym_stack := stk |>)
           | NONE => SymBad "jumpi target")
    | _ :: Lab _ _ :: _ => SymBad "jumpi condition"
    | _ => SymError "jumpi: stack underflow"
End

(* Deltas stay below 2^255, so a label's address plus its delta never wraps
   in the concrete semantics. *)
Definition sym_delta_ok_def:
  sym_delta_ok (d : num) ⇔ d < dimword (:256) DIV 2
End

Definition sym_push_lab_def:
  sym_push_lab l d stk ss =
    if sym_delta_ok d then sym_set_stack (Lab l d :: stk) ss
    else SymBad "label delta too large"
End

Definition sym_add_def:
  sym_add p env ss =
    case ss.sym_stack of
      Lab l d :: Val w :: stk =>
        if sym_data_label p env l then sym_push_lab l (d + w2n w) stk ss
        else SymBad "ADD on a code label"
    | Val w :: Lab l d :: stk =>
        if sym_data_label p env l then sym_push_lab l (d + w2n w) stk ss
        else SymBad "ADD on a code label"
    | _ => sym_step_concrete "ADD" ss
End

(* MSTORE of a label value: placeholder bytes in sym_base, the label in
   sym_mem_labels. *)
Definition sym_mstore_def:
  sym_mstore ss =
    case ss.sym_stack of
      Val off :: Lab l d :: stk =>
        sym_lift 2
          (ss.sym_mem_labels |++
             GENLIST (λi. (w2n off + i, (l, d, i))) 32) ss
          (asm_mstore (ss.sym_base with as_stack := [off; 0w]))
    | _ => sym_step_concrete "MSTORE" ss
End

Definition sym_mload_def:
  sym_mload ss =
    case ss.sym_stack of
      Val off :: stk =>
        (case mem_label_at ss.sym_mem_labels (w2n off) of
           SOME (l, d) =>
             SymOK (ss with <|
               sym_base := asm_next (ss.sym_base with as_memory :=
                 asm_expand_memory (w2n off + 32) ss.sym_base.as_memory);
               sym_stack := Lab l d :: stk |>)
         | NONE => sym_step_concrete "MLOAD" ss)
    | _ => sym_step_concrete "MLOAD" ss
End

Definition sym_codecopy_def:
  sym_codecopy p env ss =
    case ss.sym_stack of
      Val dst :: Lab l d :: Val sz :: stk =>
        if sym_data_label p env l then
          sym_lift 3
            (mem_labels_clear ss.sym_mem_labels
               (in_mem_range (w2n dst) (w2n sz))) ss
            (asm_copy_to_mem (DROP d (env ' l))
               (ss.sym_base with as_stack := [dst; 0w; sz]))
        else SymBad "CODECOPY from a code label"
    | _ =>
        if LENGTH ss.sym_stack < 3 then SymError "codecopy: stack underflow"
        else SymBad "CODECOPY of the code bytes"
End

Definition sym_dup_def:
  sym_dup n ss =
    if n < LENGTH ss.sym_stack then
      sym_set_stack (EL n ss.sym_stack :: ss.sym_stack) ss
    else SymError "dup: stack underflow"
End

Definition sym_swap_def:
  sym_swap n ss =
    let stk = ss.sym_stack in
    if n < LENGTH stk ∧ 0 < n then
      sym_set_stack (LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk)) ss
    else SymError "swap: invalid"
End

Definition sym_step_op_def:
  sym_step_op p env name ss =
    if name = "POP" then
      (case ss.sym_stack of
         _ :: stk => sym_set_stack stk ss
       | [] => SymError "pop: stack underflow")
    else if name = "JUMP" then sym_jump p ss
    else if name = "JUMPI" then sym_jumpi p ss
    else if name = "ADD" then sym_add p env ss
    else if name = "MSTORE" then sym_mstore ss
    else if name = "MLOAD" then sym_mload ss
    else if name = "CODECOPY" then sym_codecopy p env ss
    else if name = "CODESIZE" then SymBad "CODESIZE"
    else
      case ALOOKUP dup_table name of
        SOME n => sym_dup n ss
      | NONE =>
          case ALOOKUP swap_table name of
            SOME n => sym_swap n ss
          | NONE => sym_step_concrete name ss
End

Definition sym_step_def:
  sym_step p env inst ss =
    case inst of
      AsmOp name => sym_step_op p env name ss
    | AsmPushLabel l => sym_set_stack (Lab l 0 :: ss.sym_stack) ss
    | AsmPushOfst l d => sym_push_lab l d ss.sym_stack ss
    | _ => sym_lift 0 ss.sym_mem_labels ss
             (asm_step FEMPTY FEMPTY inst (ss.sym_base with as_stack := []))
End

(* As asm_steps, which the codegen simulation uses: running off the end of
   the program is an error, and the stack is unbounded (the EVM's stack
   limit is handled outside the asm semantics). *)
Definition sym_run_def:
  sym_run p env (fuel:num) ss =
    if fuel = 0 then SymError "out of fuel"
    else if ss.sym_base.as_pc ≥ LENGTH p then SymError "pc out of bounds"
    else
      case sym_step p env (EL ss.sym_base.as_pc p) ss of
        SymOK ss' => sym_run p env (fuel - 1) ss'
      | r => r
Termination
  WF_REL_TAC `measure (λ(_, _, fuel, _). fuel)`
End

(* ===== The contract ===== *)

(* Code labels are unique and apart from data headers, every label a push
   refers to is defined, and the program is its code followed by its data
   section: no data before the first data header, only data after it. It
   encodes (asm_encoding_wf), so label offsets fit their PUSH2. The
   data section holds no AsmDataLabel: its bytes are a code address, which
   the finalizer moves, so one data environment couldn't serve both
   programs. *)
Definition asm_static_wf_def:
  asm_static_wf p ⇔
    asm_labels_unique p ∧
    (∀l. MEM (AsmLabel l) p ⇒ ¬MEM (AsmDataHeader l) p) ∧
    (∀l. MEM l (asm_label_refs p) ⇒
         MEM (AsmLabel l) p ∨ MEM (AsmDataHeader l) p) ∧
    (∀l. ¬MEM (AsmDataLabel l) p) ∧
    asm_data_at_end p ∧
    asm_encoding_wf p ∧
    (∀i. i < LENGTH p ∧ is_data_inst (EL i p) ⇒
         ∃j l. j ≤ i ∧ EL j p = AsmDataHeader l)
End

Definition label_disciplined_def:
  label_disciplined env p s ⇔
    asm_static_wf p ∧
    ∀fuel msg. sym_run p env fuel (sym_init s) ≠ SymBad msg
End

Definition sym_terminal_def:
  sym_terminal (SymHalt _) = T ∧
  sym_terminal (SymRevert _) = T ∧
  sym_terminal (SymFault _) = T ∧
  sym_terminal _ = F
End

(* Terminal results agree on everything but the PC, stack, memory and code:
   accounts, transient storage, returndata, logs, requests, and the oracle
   lists left over. *)
Definition sym_obs_def:
  sym_obs ss =
    ss.sym_base with <| as_pc := 0; as_memory := []; as_code := [] |>
End

Definition sym_result_rel_def:
  sym_result_rel (SymHalt a) (SymHalt b) = (sym_obs a = sym_obs b) ∧
  sym_result_rel (SymRevert a) (SymRevert b) = (sym_obs a = sym_obs b) ∧
  sym_result_rel (SymFault a) (SymFault b) = (sym_obs a = sym_obs b) ∧
  sym_result_rel _ _ = F
End

(* p' refines p: it keeps p's data section, and from every start state and
   data environment where p's symbolic run ends without error, p''s ends the
   same way. The environment stands for the bytes from each data header on;
   since p' has the same data section, one environment serves both programs.
   The optimizer's rules are each proved against this. *)
Definition asm_refines_def:
  asm_refines p p' ⇔
    asm_static_wf p ⇒
    asm_static_wf p' ∧
    FILTER is_data_inst p' = FILTER is_data_inst p ∧
    ∀env s fuel.
      sym_terminal (sym_run p env fuel (sym_init s)) ⇒
      ∃fuel'. sym_result_rel (sym_run p env fuel (sym_init s))
                             (sym_run p' env fuel' (sym_init s))
End

Definition finalizer_correct_def:
  finalizer_correct (f : assembly_finalizer) ⇔
    ∀rp p p'. f rp p = SOME p' ⇒ asm_refines p p'
End

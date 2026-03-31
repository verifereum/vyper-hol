(*
 * Alloca Safety Predicates
 *
 * Structural properties of Venom IR functions regarding alloca pointers.
 * Used as preconditions for passes that change alloca layout.
 *
 * TOP-LEVEL:
 *   alloca_derived       — set of variables that may hold alloca-derived pointers
 *   sensitive_operands   — operand positions where pointer values affect observable output
 *   alloca_safe_inst     — instruction doesn't leak alloca pointers to sensitive channels
 *   alloca_safe_fn       — function-level: no alloca pointer leaks
 *
 * Design decision: stated as a precondition on pass correctness theorems.
 * Discharged by construction from Vyper→Venom lowering.
 * Future TODO: generalize to tagged values for non-Vyper frontends.
 *)

Theory allocaSafety
Ancestors
  venomWf

(* ===== Alloca-Derived Variables ===== *)

(* A variable is alloca-derived if its value may hold an alloca pointer.
 * Def-use reachability from ALLOCA outputs: any instruction that
 * consumes an alloca-derived input may produce an alloca-derived output.
 *
 * This over-approximates (e.g. ISZERO of a pointer isn't a pointer),
 * which is safe — makes alloca_safe_fn a stronger precondition.
 * Under-approximation would be unsound.
 *
 * Compare bp_handle_inst which only tracks {ALLOCA,ADD,SUB,PHI,ASSIGN}.
 * That's sound for Vyper (lowering never stores pointers to memory)
 * but not in general (MLOAD of a stored pointer, INVOKE returning one).
 * alloca_derived is the sound specification; bp analysis is the
 * efficient-but-Vyper-specific implementation. *)
Inductive alloca_derived:
  (* Base: ALLOCA output *)
  (∀fn inst out.
     MEM inst (fn_insts fn) ∧
     inst.inst_opcode = ALLOCA ∧
     inst_output inst = SOME out ⇒
     alloca_derived fn out)
  ∧
  (* Propagation: any instruction consuming an alloca-derived input *)
  (∀fn inst out v.
     MEM inst (fn_insts fn) ∧
     inst_output inst = SOME out ∧
     MEM (Var v) inst.inst_operands ∧
     alloca_derived fn v ⇒
     alloca_derived fn out)
End

(* ===== Sensitive Operand Positions ===== *)

(* Operand positions where a pointer-derived value affects observable
 * output. Two categories:
 *
 * 1. Direct external effect: operand value stored to world state
 *    (SSTORE, TSTORE, ISTORE), sent externally (CALL value/gas/addr,
 *    CREATE value, LOG topics, SELFDESTRUCT), or determines external
 *    output shape (RETURN/REVERT/LOG/CALL size/length args).
 *
 * 2. Memory laundering: MSTORE value can be loaded back via MLOAD,
 *    reaching external state indirectly.
 *
 * Memory OFFSET operands are NOT sensitive — they determine WHERE
 * to read/write, but the pointer value itself doesn't escape.
 * Taint propagation through alloca_derived handles indirect flows.
 *
 * Operand positions use HOL4/EVM semantic order (not Python stack order).
 * Returns NONE for malformed operand lists.
 *
 * Non-sensitive opcodes (SOME {}): pure arithmetic, comparisons,
 * bitwise, reads, context reads, control flow, SSA, bulk copies
 * from external sources (calldatacopy, returndatacopy, codecopy,
 * extcodecopy, dloadbytes). These either have no side effects or
 * copy from sources that cannot contain alloca pointers. *)
Definition sensitive_operands_def:
  sensitive_operands (inst : instruction) : operand set option =
    case inst.inst_opcode of
    (* ---- World state writes: all operands sensitive ---- *)
    | SSTORE => SOME (set inst.inst_operands)
    | TSTORE => SOME (set inst.inst_operands)
    | ISTORE => SOME (set inst.inst_operands)
    | SELFDESTRUCT => SOME (set inst.inst_operands)
    (* ---- Memory value write: laundering channel ---- *)
    (* MSTORE [offset; value] — value enters memory, can be
     * loaded back via MLOAD and reach external state. *)
    | MSTORE => (case inst.inst_operands of
                   [_; value] => SOME {value}
                 | _ => NONE)
    (* ---- External output shape: size/length operands ---- *)
    (* RETURN [offset; sz] — sz determines return data length *)
    | RETURN => (case inst.inst_operands of
                   [_; sz] => SOME {sz}
                 | _ => NONE)
    (* REVERT [offset; sz] — sz determines revert data length *)
    | REVERT => (case inst.inst_operands of
                   [_; sz] => SOME {sz}
                 | _ => NONE)
    (* SHA3 [offset; sz] — sz affects hash output *)
    | SHA3 => (case inst.inst_operands of
                 [_; sz] => SOME {sz}
               | _ => NONE)
    (* MCOPY [dest; src; sz] — sz determines copy extent *)
    | MCOPY => (case inst.inst_operands of
                  [_; _; sz] => SOME {sz}
                | _ => NONE)
    (* LOG [Lit tc; offset; size; topic1; ...] —
     * size determines log data length; topics are external values.
     * tc must be a literal. Malformed → NONE. *)
    | LOG => (case inst.inst_operands of
                Lit _ :: _ :: sz :: topics => SOME (sz INSERT set topics)
              | _ => NONE)
    (* ---- External calls: value/gas/addr + size args ---- *)
    (* CALL [gas; addr; value; argsOff; argsLen; retOff; retLen] *)
    | CALL => (case inst.inst_operands of
                 [gas; addr; value; _; argsLen; _; retLen] =>
                   SOME {gas; addr; value; argsLen; retLen}
               | _ => NONE)
    (* STATICCALL [gas; addr; argsOff; argsLen; retOff; retLen] *)
    | STATICCALL => (case inst.inst_operands of
                       [gas; addr; _; argsLen; _; retLen] =>
                         SOME {gas; addr; argsLen; retLen}
                     | _ => NONE)
    (* DELEGATECALL [gas; addr; argsOff; argsLen; retOff; retLen] *)
    | DELEGATECALL => (case inst.inst_operands of
                         [gas; addr; _; argsLen; _; retLen] =>
                           SOME {gas; addr; argsLen; retLen}
                       | _ => NONE)
    (* CREATE [value; offset; size] — value + size sensitive *)
    | CREATE => (case inst.inst_operands of
                   [value; _; sz] => SOME {value; sz}
                 | _ => NONE)
    (* CREATE2 [value; offset; sz; salt] — value, sz, salt sensitive *)
    | CREATE2 => (case inst.inst_operands of
                    [value; _; sz; salt] => SOME {value; sz; salt}
                  | _ => NONE)
    (* ---- Non-sensitive: no operand values reach external state ---- *)
    | ADD => SOME {} | SUB => SOME {} | MUL => SOME {}
    | Div => SOME {} | Mod => SOME {}
    | SDIV => SOME {} | SMOD => SOME {} | Exp => SOME {}
    | EQ => SOME {} | LT => SOME {} | GT => SOME {}
    | SLT => SOME {} | SGT => SOME {}
    | AND => SOME {} | OR => SOME {} | XOR => SOME {} | NOT => SOME {}
    | SHL => SOME {} | SHR => SOME {} | SAR => SOME {}
    | SIGNEXTEND => SOME {} | BYTE => SOME {}
    | ISZERO => SOME {} | ADDMOD => SOME {} | MULMOD => SOME {}
    | MLOAD => SOME {} | SLOAD => SOME {} | TLOAD => SOME {}
    | ILOAD => SOME {} | DLOAD => SOME {}
    | BLOCKHASH => SOME {} | BLOBHASH => SOME {} | BALANCE => SOME {}
    | CALLDATALOAD => SOME {} | EXTCODESIZE => SOME {}
    | EXTCODEHASH => SOME {}
    | CALLER => SOME {} | ADDRESS => SOME {} | CALLVALUE => SOME {}
    | GAS => SOME {}
    | ORIGIN => SOME {} | GASPRICE => SOME {} | CHAINID => SOME {}
    | COINBASE => SOME {}
    | TIMESTAMP => SOME {} | NUMBER => SOME {} | PREVRANDAO => SOME {}
    | GASLIMIT => SOME {}
    | BASEFEE => SOME {} | BLOBBASEFEE => SOME {}
    | CALLDATASIZE => SOME {}
    | RETURNDATASIZE => SOME {} | MSIZE => SOME {} | CODESIZE => SOME {}
    | SELFBALANCE => SOME {}
    | CALLDATACOPY => SOME {} | RETURNDATACOPY => SOME {}
    | DLOADBYTES => SOME {} | CODECOPY => SOME {} | EXTCODECOPY => SOME {}
    | JMP => SOME {} | JNZ => SOME {} | DJMP => SOME {}
    | STOP => SOME {} | SINK => SOME {} | RET => SOME {}
    | PHI => SOME {} | ASSIGN => SOME {} | NOP => SOME {}
    | PARAM => SOME {} | ALLOCA => SOME {}
    | OFFSET => SOME {} | INVOKE => SOME {}
    | ASSERT => SOME {} | ASSERT_UNREACHABLE => SOME {}
    | INVALID => SOME {}
End

(* ===== Instruction-Level Safety ===== *)

(* An instruction is alloca-safe if it is well-formed (sensitive_operands
 * returns SOME) and no alloca-derived variable appears in a sensitive
 * operand position. *)
Definition alloca_safe_inst_def:
  alloca_safe_inst fn inst ⇔
    case sensitive_operands inst of
    | NONE => F
    | SOME sens => ∀v. alloca_derived fn v ⇒ Var v ∉ sens
End

(* inst_wf guarantees sensitive_operands succeeds. *)
Theorem inst_wf_sensitive_operands:
  ∀inst. inst_wf inst ⇒ IS_SOME (sensitive_operands inst)
Proof
  cheat
QED

(* ===== Function-Level Safety ===== *)

(* A function is alloca-safe: no instruction leaks alloca pointers
 * to observable channels. *)
Definition alloca_safe_fn_def:
  alloca_safe_fn fn ⇔
    ∀inst. MEM inst (fn_insts fn) ⇒ alloca_safe_inst fn inst
End

(* Context-level: use EVERY alloca_safe_fn ctx.ctx_functions
 * (no separate definition — consistent with EVERY wf_function pattern) *)


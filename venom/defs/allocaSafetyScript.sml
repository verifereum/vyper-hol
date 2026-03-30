(*
 * Alloca Safety Predicates
 *
 * Structural properties of Venom IR functions regarding alloca pointers.
 * Used as preconditions for passes that change alloca layout.
 *
 * TOP-LEVEL:
 *   alloca_derived       — set of variables that may hold alloca-derived pointers
 *   observable_operands  — operand positions whose values reach external state
 *   alloca_safe_inst     — instruction doesn't leak alloca pointers to observable channels
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

(* A variable is alloca-derived if its value may contain an alloca pointer.
 * This is the transitive closure of pointer propagation through the IR.
 *
 * ALLOCA output is alloca-derived (base case).
 * ADD/SUB on a pointer produces a pointer (pointer arithmetic).
 * ASSIGN/PHI transparently forward values (including pointers).
 *
 * Over-approximation: safe to include non-pointer variables.
 * Under-approximation would be unsound. *)
Inductive alloca_derived:
  (* Base: ALLOCA output *)
  (∀fn inst out.
     MEM inst (fn_insts fn) ∧
     inst.inst_opcode = ALLOCA ∧
     inst_output inst = SOME out ⇒
     alloca_derived fn out)
  ∧
  (* ADD: pointer arithmetic *)
  (∀fn inst out v.
     MEM inst (fn_insts fn) ∧
     inst.inst_opcode = ADD ∧
     inst_output inst = SOME out ∧
     MEM (Var v) inst.inst_operands ∧
     alloca_derived fn v ⇒
     alloca_derived fn out)
  ∧
  (* SUB: pointer arithmetic *)
  (∀fn inst out v.
     MEM inst (fn_insts fn) ∧
     inst.inst_opcode = SUB ∧
     inst_output inst = SOME out ∧
     MEM (Var v) inst.inst_operands ∧
     alloca_derived fn v ⇒
     alloca_derived fn out)
  ∧
  (* ASSIGN: transparent forwarding *)
  (∀fn inst out v.
     MEM inst (fn_insts fn) ∧
     inst.inst_opcode = ASSIGN ∧
     inst_output inst = SOME out ∧
     MEM (Var v) inst.inst_operands ∧
     alloca_derived fn v ⇒
     alloca_derived fn out)
  ∧
  (* PHI: any source may carry a pointer *)
  (∀fn inst out v.
     MEM inst (fn_insts fn) ∧
     inst.inst_opcode = PHI ∧
     inst_output inst = SOME out ∧
     MEM (Var v) inst.inst_operands ∧
     alloca_derived fn v ⇒
     alloca_derived fn out)
End

(* ===== Observable Value Positions ===== *)

(* Operands at these positions have their VALUES stored to external state
 * (storage, transient storage, logs, cross-contract calls). If an
 * alloca-derived pointer reaches one of these positions, the observable
 * output depends on the concrete alloca layout.
 *
 * Memory offset operands (MLOAD, MSTORE, RETURN, etc.) are NOT observable
 * — they determine WHERE to read/write memory, but the pointer value
 * itself doesn't escape. The memory CONTENTS may escape, not the address.
 *
 * Operand positions use HOL4/EVM semantic order (not Python stack order).
 *
 * Non-observable opcodes (empty set):
 *   - Pure arithmetic: ADD SUB MUL Div Mod SDIV SMOD Exp
 *   - Comparison: EQ LT GT SLT SGT
 *   - Bitwise: AND OR XOR NOT SHL SHR SAR SIGNEXTEND BYTE
 *   - Unary: ISZERO
 *   - 3-arg: ADDMOD MULMOD
 *   - Reads: MLOAD SLOAD TLOAD ILOAD DLOAD BLOCKHASH BLOBHASH
 *            BALANCE CALLDATALOAD EXTCODESIZE EXTCODEHASH
 *   - Context reads: CALLER ADDRESS CALLVALUE GAS ORIGIN GASPRICE
 *            CHAINID COINBASE TIMESTAMP NUMBER PREVRANDAO GASLIMIT
 *            BASEFEE BLOBBASEFEE CALLDATASIZE RETURNDATASIZE MSIZE
 *            CODESIZE SELFBALANCE
 *   - Memory writes: MSTORE (offset operand, not value-to-world)
 *   - Bulk copies: MCOPY CALLDATACOPY RETURNDATACOPY DLOADBYTES
 *            CODECOPY EXTCODECOPY (memory addresses, not values)
 *   - Hash: SHA3 (memory offset + size)
 *   - Control flow: JMP JNZ DJMP RETURN REVERT STOP SINK RET
 *   - SSA: PHI ASSIGN NOP PARAM ALLOCA
 *   - Other: OFFSET INVOKE ASSERT ASSERT_UNREACHABLE INVALID
 *
 * MSTORE is NOT observable: MSTORE [offset; value] writes to
 * internal memory, not world state. The value is only observable
 * if later read by RETURN/LOG/CALL — tracked transitively. *)
Definition observable_operands_def:
  observable_operands (inst : instruction) =
    case inst.inst_opcode of
    (* SSTORE [key; value] — both key and value stored to world state *)
    | SSTORE => set inst.inst_operands
    (* TSTORE [key; value] — both stored to transient storage *)
    | TSTORE => set inst.inst_operands
    (* ISTORE [key; value] — both stored to immutable storage *)
    | ISTORE => set inst.inst_operands
    (* LOG [tc; offset; size; topic1; topic2; ...] —
     * topics are observable values; offset/size are memory addresses *)
    | LOG => (case inst.inst_operands of
                Lit tc :: _ :: _ :: topics => set topics
              | _ => {})
    (* CALL [gas; addr; value; argsOff; argsLen; retOff; retLen]
     * value (operand 2) is ETH transferred — observable.
     * gas, addr also observable (affect external behavior).
     * argsOff/argsLen/retOff/retLen are memory addresses. *)
    | CALL => (case inst.inst_operands of
                 gas :: addr :: value :: _ => {gas; addr; value}
               | _ => set inst.inst_operands)
    (* STATICCALL [gas; addr; argsOff; argsLen; retOff; retLen] *)
    | STATICCALL => (case inst.inst_operands of
                       gas :: addr :: _ => {gas; addr}
                     | _ => set inst.inst_operands)
    (* DELEGATECALL [gas; addr; argsOff; argsLen; retOff; retLen] *)
    | DELEGATECALL => (case inst.inst_operands of
                         gas :: addr :: _ => {gas; addr}
                       | _ => set inst.inst_operands)
    (* CREATE [value; offset; size] — value is observable *)
    | CREATE => (case inst.inst_operands of
                   value :: _ => {value}
                 | _ => {})
    (* CREATE2 [value; offset; size; salt] — value and salt observable *)
    | CREATE2 => (case inst.inst_operands of
                    value :: _ :: _ :: salt :: _ => {value; salt}
                  | _ => set inst.inst_operands)
    (* SELFDESTRUCT [beneficiary] — address is observable *)
    | SELFDESTRUCT => set inst.inst_operands
    (* ---- Non-observable: all remaining opcodes ----
     * Pure/comparison/bitwise/reads/context/memory/bulk-copy/hash/
     * control-flow/SSA/special — none store operand values to world state.
     * See comment above for complete enumeration. *)
    | ADD => {} | SUB => {} | MUL => {} | Div => {} | Mod => {}
    | SDIV => {} | SMOD => {} | Exp => {}
    | EQ => {} | LT => {} | GT => {} | SLT => {} | SGT => {}
    | AND => {} | OR => {} | XOR => {} | NOT => {}
    | SHL => {} | SHR => {} | SAR => {} | SIGNEXTEND => {} | BYTE => {}
    | ISZERO => {} | ADDMOD => {} | MULMOD => {}
    | MLOAD => {} | SLOAD => {} | TLOAD => {} | ILOAD => {} | DLOAD => {}
    | BLOCKHASH => {} | BLOBHASH => {} | BALANCE => {}
    | CALLDATALOAD => {} | EXTCODESIZE => {} | EXTCODEHASH => {}
    | CALLER => {} | ADDRESS => {} | CALLVALUE => {} | GAS => {}
    | ORIGIN => {} | GASPRICE => {} | CHAINID => {} | COINBASE => {}
    | TIMESTAMP => {} | NUMBER => {} | PREVRANDAO => {} | GASLIMIT => {}
    | BASEFEE => {} | BLOBBASEFEE => {} | CALLDATASIZE => {}
    | RETURNDATASIZE => {} | MSIZE => {} | CODESIZE => {} | SELFBALANCE => {}
    | MSTORE => {} | MCOPY => {} | CALLDATACOPY => {} | RETURNDATACOPY => {}
    | DLOADBYTES => {} | CODECOPY => {} | EXTCODECOPY => {}
    | SHA3 => {}
    | JMP => {} | JNZ => {} | DJMP => {} | RETURN => {} | REVERT => {}
    | STOP => {} | SINK => {} | RET => {}
    | PHI => {} | ASSIGN => {} | NOP => {} | PARAM => {} | ALLOCA => {}
    | OFFSET => {} | INVOKE => {} | ASSERT => {} | ASSERT_UNREACHABLE => {}
    | INVALID => {}
End

(* ===== Instruction-Level Safety ===== *)

(* An instruction is alloca-safe if no alloca-derived variable appears
 * in an observable value position. *)
Definition alloca_safe_inst_def:
  alloca_safe_inst fn inst ⇔
    ∀v. alloca_derived fn v ⇒
        Var v ∉ observable_operands inst
End

(* ===== Function-Level Safety ===== *)

(* A function is alloca-safe: no instruction leaks alloca pointers
 * to observable channels. *)
Definition alloca_safe_fn_def:
  alloca_safe_fn fn ⇔
    ∀inst. MEM inst (fn_insts fn) ⇒ alloca_safe_inst fn inst
End

(* Context-level: use EVERY alloca_safe_fn ctx.ctx_functions
 * (no separate definition — consistent with EVERY wf_function pattern) *)


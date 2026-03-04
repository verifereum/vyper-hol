(*
 * Venom Effects System
 *
 * Effects track what state an instruction reads or writes.
 * This is crucial for optimization passes (CSE, DCE, reordering).
 *
 * Ported from vyper/venom/effects.py.
 *
 * TOP-LEVEL:
 *   effect, read_effects, write_effects, effects_independent,
 *   has_conflicting_effects, is_nonidempotent, addr_space, effect_of_addr_space
 *)

Theory venomEffects
Ancestors
  venomInst

(* ===== Effect Categories ===== *)

Datatype:
  effect =
    | Eff_STORAGE
    | Eff_TRANSIENT
    | Eff_MEMORY
    | Eff_MSIZE
    | Eff_IMMUTABLES
    | Eff_RETURNDATA
    | Eff_LOG
    | Eff_BALANCE
    | Eff_EXTCODE
End

Type effects = ``:effect set``

Definition empty_effects_def:
  empty_effects : effects = {}
End

Definition all_effects_def:
  all_effects : effects =
    {Eff_STORAGE; Eff_TRANSIENT; Eff_MEMORY; Eff_MSIZE;
     Eff_IMMUTABLES; Eff_RETURNDATA; Eff_LOG; Eff_BALANCE; Eff_EXTCODE}
End

(* ===== Read Effects ===== *)

(* Which state components an opcode may read.
 * Matches Python _reads table in effects.py. *)
Definition read_effects_def:
  read_effects SLOAD = {Eff_STORAGE} /\
  read_effects TLOAD = {Eff_TRANSIENT} /\
  read_effects ILOAD = {Eff_IMMUTABLES; Eff_MEMORY} /\
  read_effects MLOAD = {Eff_MEMORY} /\
  read_effects MCOPY = {Eff_MEMORY} /\
  read_effects CALL = all_effects /\
  read_effects DELEGATECALL = all_effects /\
  read_effects STATICCALL = all_effects /\
  read_effects CREATE = all_effects /\
  read_effects CREATE2 = all_effects /\
  read_effects INVOKE = all_effects /\
  read_effects RETURNDATASIZE = {Eff_RETURNDATA} /\
  read_effects RETURNDATACOPY = {Eff_RETURNDATA} /\
  read_effects BALANCE = {Eff_BALANCE} /\
  read_effects SELFBALANCE = {Eff_BALANCE} /\
  read_effects EXTCODECOPY = {Eff_EXTCODE} /\
  read_effects EXTCODESIZE = {Eff_EXTCODE} /\
  read_effects EXTCODEHASH = {Eff_EXTCODE} /\
  read_effects SELFDESTRUCT = {Eff_BALANCE} /\
  read_effects LOG = {Eff_MEMORY} /\
  read_effects REVERT = {Eff_MEMORY} /\
  read_effects SHA3 = {Eff_MEMORY} /\
  read_effects MSIZE = {Eff_MSIZE} /\
  read_effects RETURN = {Eff_MEMORY} /\
  read_effects _ = empty_effects
End

(* ===== Write Effects ===== *)

(* Which state components an opcode may write.
 * Matches Python _writes table in effects.py AFTER post-processing:
 *   - Eff_MSIZE added for any opcode that reads or writes MEMORY/IMMUTABLES
 *   - ISTORE writes MEMORY (immutables live in memory region)
 *
 * Post-processing rule from effects.py:
 *   for k, v in reads.items():
 *     if MEMORY in v or IMMUTABLES in v:
 *       writes[k] |= MSIZE
 *   for k, v in writes.items():
 *     if MEMORY in v or IMMUTABLES in v:
 *       writes[k] |= MSIZE
 *)
Definition write_effects_def:
  (* Storage/transient: no memory involvement *)
  write_effects SSTORE = {Eff_STORAGE} /\
  write_effects TSTORE = {Eff_TRANSIENT} /\
  (* Memory writes *)
  write_effects MSTORE = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects ISTORE = {Eff_IMMUTABLES; Eff_MEMORY; Eff_MSIZE} /\
  (* External calls *)
  write_effects CALL = all_effects DIFF {Eff_IMMUTABLES} /\
  write_effects DELEGATECALL = all_effects DIFF {Eff_IMMUTABLES} /\
  write_effects STATICCALL = {Eff_MEMORY; Eff_RETURNDATA; Eff_MSIZE} /\
  write_effects CREATE = all_effects DIFF {Eff_MEMORY; Eff_IMMUTABLES} /\
  write_effects CREATE2 = all_effects DIFF {Eff_MEMORY; Eff_IMMUTABLES} /\
  write_effects INVOKE = all_effects /\
  (* Logging *)
  write_effects LOG = {Eff_LOG; Eff_MSIZE} /\
  (* Memory-writing bulk ops *)
  write_effects DLOADBYTES = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects DLOAD = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects RETURNDATACOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects CALLDATACOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects CODECOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects EXTCODECOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects MCOPY = {Eff_MEMORY; Eff_MSIZE} /\
  (* Memory-reading opcodes write MSIZE (reads can expand memory) *)
  write_effects ILOAD = {Eff_MSIZE} /\
  write_effects MLOAD = {Eff_MSIZE} /\
  write_effects REVERT = {Eff_MSIZE} /\
  write_effects SHA3 = {Eff_MSIZE} /\
  write_effects RETURN = {Eff_MSIZE} /\
  write_effects _ = empty_effects
End

(* ===== Derived Predicates ===== *)

(* Two opcodes can be safely reordered *)
Definition effects_independent_def:
  effects_independent op1 op2 <=>
    DISJOINT (write_effects op1) (read_effects op2 UNION write_effects op2) /\
    DISJOINT (write_effects op2) (read_effects op1 UNION write_effects op1)
End

(* Opcode has conflicting read/write effects on same component *)
Definition has_conflicting_effects_def:
  has_conflicting_effects op <=>
    read_effects op INTER write_effects op <> {}
End

(* Side-effecting opcodes that are never available for CSE *)
Definition is_nonidempotent_def:
  is_nonidempotent CALL = T /\
  is_nonidempotent DELEGATECALL = T /\
  is_nonidempotent STATICCALL = T /\
  is_nonidempotent CREATE = T /\
  is_nonidempotent CREATE2 = T /\
  is_nonidempotent INVOKE = T /\
  is_nonidempotent LOG = T /\
  is_nonidempotent _ = F
End

(* Commutative opcodes: operand order does not affect result.
 * Matches Python COMMUTATIVE_INSTRUCTIONS =
 *   frozenset(["add", "mul", "smul", "or", "xor", "and", "eq"])
 * Note: Python has "smul" but our IR uses MUL for both (SDIV/SMOD are
 * separate but smul is just MUL with sign-extension handled elsewhere). *)
Definition is_commutative_def:
  is_commutative ADD = T /\
  is_commutative MUL = T /\
  is_commutative OR = T /\
  is_commutative XOR = T /\
  is_commutative AND = T /\
  is_commutative EQ = T /\
  is_commutative _ = F
End

(* ===== Address Spaces ===== *)

(* Matches vyper/evm/address_space.py *)
Datatype:
  addr_space =
    AddrSp_Memory | AddrSp_Storage | AddrSp_Transient |
    AddrSp_Calldata | AddrSp_Immutables | AddrSp_Data |
    AddrSp_Code | AddrSp_Returndata
End

(* Partial: only addr spaces with mutable state have effects.
 * Matches Python to_addr_space (which maps effect→addr_space for these 4). *)
Definition effect_of_addr_space_def:
  effect_of_addr_space AddrSp_Memory = SOME Eff_MEMORY /\
  effect_of_addr_space AddrSp_Storage = SOME Eff_STORAGE /\
  effect_of_addr_space AddrSp_Transient = SOME Eff_TRANSIENT /\
  effect_of_addr_space AddrSp_Immutables = SOME Eff_IMMUTABLES /\
  effect_of_addr_space _ = NONE
End


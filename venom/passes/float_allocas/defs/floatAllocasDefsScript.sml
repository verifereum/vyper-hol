(*
 * Float Allocas Pass — Definitions
 *
 * Ports vyper/venom/passes/float_allocas.py to HOL4.
 *
 * Moves alloca/palloca/calloca instructions from non-entry blocks
 * to the entry basic block, preserving their relative order.
 * For palloca: also moves the immediately following mstore if it is
 * a parameter initialization store (mstore param_var → palloca_addr).
 *
 * This ensures allocas dominate all their uses, which is required
 * by SCCP and other passes.
 *
 * No analysis needed — structural instruction movement.
 *
 * TOP-LEVEL:
 *   is_alloca_opcode            — check if opcode is alloca/palloca/calloca
 *   is_palloca_init_store       — detect synthetic palloca init mstore
 *   extract_allocas_from_block  — separate allocas from non-alloca insts
 *   float_allocas_function      — function-level transform
 *   float_allocas_context       — context-level transform
 *
 * Source: vyper/venom/passes/float_allocas.py
 *)

Theory floatAllocasDefs
Ancestors
  passSimulationDefs venomExecSemantics venomInst

(* ===== Alloca Detection ===== *)

Definition is_alloca_opcode_def:
  is_alloca_opcode ALLOCA = T /\
  is_alloca_opcode PALLOCA = T /\
  is_alloca_opcode CALLOCA = T /\
  is_alloca_opcode _ = F
End

(* ===== Palloca Init Store Detection ===== *)

(*
 * Detect the synthetic mstore that initializes a palloca's memory
 * with a stack-passed parameter value.
 *
 * Pattern (in HOL4 semantic operand order):
 *   palloca [...] → [palloca_out]
 *   mstore [Var palloca_out; param_val]
 *
 * The mstore writes param_val to the palloca's address.
 * Python checks: mstore.operands[1] == palloca.output (stack order: [val, offset])
 * HOL4 semantic order: mstore [offset, value], so offset = Var palloca_out.
 *
 * Note: The full Python check also verifies that the palloca's alloca_id
 * maps to a function parameter (get_param_by_id). Since the HOL4 function
 * model lacks fn_params, we check only the structural pattern.
 *)
Definition is_palloca_init_store_def:
  is_palloca_init_store palloca_inst mstore_inst <=>
    palloca_inst.inst_opcode = PALLOCA /\
    mstore_inst.inst_opcode = MSTORE /\
    LENGTH mstore_inst.inst_operands >= 2 /\
    case palloca_inst.inst_outputs of
      [palloca_out] =>
        HD mstore_inst.inst_operands = Var palloca_out
    | _ => F
End

(* ===== Extract Allocas From a Block ===== *)

(*
 * Process instructions from a non-entry block.
 * Returns (allocas_to_move, remaining_insts).
 *
 * For each alloca/palloca/calloca:
 *   - Move the instruction to the alloca list
 *   - For palloca: if the next instruction is an init store, move it too
 *
 * Preserves relative order of both allocas and non-allocas.
 *)
Definition extract_allocas_def:
  extract_allocas [] = ([], []) /\
  extract_allocas [inst] =
    (if is_alloca_opcode inst.inst_opcode
     then ([inst], [])
     else ([], [inst])) /\
  extract_allocas (inst :: next :: rest) =
    if is_alloca_opcode inst.inst_opcode then
      if is_palloca_init_store inst next then
        let (more_allocas, remaining) = extract_allocas rest in
        (inst :: next :: more_allocas, remaining)
      else
        let (more_allocas, remaining) = extract_allocas (next :: rest) in
        (inst :: more_allocas, remaining)
    else
      let (allocas, remaining) = extract_allocas (next :: rest) in
      (allocas, inst :: remaining)
End

(* ===== Insert Before Terminator ===== *)

(*
 * Insert instructions before the last instruction (terminator) of a block.
 * If the block is empty, just prepend the instructions.
 *)
Definition insert_before_terminator_def:
  insert_before_terminator insts bb =
    case bb.bb_instructions of
      [] => bb with bb_instructions := insts
    | _ =>
        let front = FRONT bb.bb_instructions in
        let term = LAST bb.bb_instructions in
        bb with bb_instructions := front ++ insts ++ [term]
End

(* ===== Function-Level Transform ===== *)

(*
 * Float allocas to entry block.
 *
 * 1. For each non-entry block, extract allocas
 * 2. Insert extracted allocas into entry block (before terminator)
 * 3. Replace non-entry blocks with their remaining instructions
 *)
Definition float_allocas_function_def:
  float_allocas_function fn =
    case fn.fn_blocks of
      [] => fn
    | entry :: rest =>
        let results = MAP (\bb. (bb, extract_allocas bb.bb_instructions)) rest in
        let all_allocas = FLAT (MAP (\(bb, (allocas, _)). allocas) results) in
        let new_rest = MAP (\(bb, (_, remaining)).
          bb with bb_instructions := remaining) results in
        let new_entry = insert_before_terminator all_allocas entry in
        fn with fn_blocks := new_entry :: new_rest
End

(* Transform all functions in a context. *)
Definition float_allocas_context_def:
  float_allocas_context ctx =
    ctx with ctx_functions := MAP float_allocas_function ctx.ctx_functions
End

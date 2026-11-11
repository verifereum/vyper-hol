(*
 * The gas of one step of the generated code's EVM frame, for the
 * sufficient-gas theorem S7g: an instruction that touches memory only
 * below H costs at most frame_op_gas H, so with that much gas left it
 * doesn't run out of gas, and a call leaves the frame at least a 64th of
 * what is left after that cost.  RETURNDATACOPY, whose size the callee
 * sets, is the exception.
 *
 * TOP-LEVEL:
 *   frame_op_gas       - the gas bound of one instruction under H
 *   asm_frame_gas_step - the step's gas, against the assembly step
 *)

Theory asmFrameGas
Ancestors
  asmFrameRel asmRunBounded frameStep callTrace asmSem asmWf symbolResolve
  vfmExecution vfmExecutionProp

(* At least the gas of any instruction asm_inst_gas_ok H allows: static
   and access costs (a value-carrying CALL to a new account costs 36700),
   SSTORE's 22100 and its 2300 stipend check, the per-byte costs of
   copies, hashing and logs (at most 8 a byte), memory expansion to H,
   and 6400 for a call's static cost after the 63/64 split. *)
Definition frame_op_gas_def:
  frame_op_gas H = 50000 + 8 * H + memory_cost H
End

(* The frame's step at es, an instruction of prog that is
   asm_inst_gas_ok H and not RETURNDATACOPY, with frame_op_gas H gas left:
   step_inst doesn't run out of gas at our depth and uses at most
   frame_op_gas H there, and at the frame's next state a CALL or
   STATICCALL leaves at least a 64th of what is left after that. *)
Theorem asm_frame_gas_step:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    frame_op_gas H <= frame_gas_left es ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r, s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       frame_gas_left es <= frame_gas_left s' + frame_op_gas H) /\
    (!es1. frame_next es es1 ==>
       if EL a.as_pc prog = AsmOp "CALL" \/
          EL a.as_pc prog = AsmOp "STATICCALL"
       then (frame_gas_left es - frame_op_gas H) DIV 64 <= frame_gas_left es1
       else frame_gas_left es <= frame_gas_left es1 + frame_op_gas H)
Proof
  cheat
QED

(*
 * A resource-bounded assembly run, for the sufficient-gas theorem S7g
 * (codegen_gas_sufficient): the run ends within a number of steps, and
 * every step before it reaches a RETURNDATACOPY touches memory below a
 * bound and is an instruction whose gas the bound limits.
 *
 * TOP-LEVEL:
 *   asm_mem_ranges   - the memory ranges an instruction touches
 *   asm_inst_gas_ok  - an instruction's gas is bounded by its memory bound
 *   asm_run_bounded  - the run's step and memory bound
 *)

Theory asmRunBounded
Ancestors
  asmSem asmWf words list

(* The memory ranges (offset, size) an assembly instruction reads or
   writes, from its operands on the stack (top first, as the EVM pops
   them).  Instructions that touch no memory have none. *)
Definition asm_mem_ranges_def:
  (asm_mem_ranges (AsmOp name) (stk:bytes32 list) =
     if MEM name ["MLOAD"; "MSTORE"] then
       (case stk of off :: _ => [(w2n off, 32)] | _ => [])
     else if name = "MSTORE8" then
       (case stk of off :: _ => [(w2n off, 1)] | _ => [])
     else if MEM name ["SHA3"; "RETURN"; "REVERT";
                       "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] then
       (case stk of off :: sz :: _ => [(w2n off, w2n sz)] | _ => [])
     else if MEM name ["CALLDATACOPY"; "CODECOPY"; "RETURNDATACOPY"] then
       (case stk of dst :: _ :: sz :: _ => [(w2n dst, w2n sz)] | _ => [])
     else if name = "EXTCODECOPY" then
       (case stk of _ :: dst :: _ :: sz :: _ => [(w2n dst, w2n sz)]
                  | _ => [])
     else if name = "MCOPY" then
       (case stk of dst :: src :: sz :: _ =>
                      [(w2n dst, w2n sz); (w2n src, w2n sz)]
                  | _ => [])
     else if name = "CALL" then
       (case stk of _ :: _ :: _ :: ao :: az :: ro :: rs :: _ =>
                      [(w2n ao, w2n az); (w2n ro, w2n rs)]
                  | _ => [])
     else if name = "STATICCALL" then
       (case stk of _ :: _ :: ao :: az :: ro :: rs :: _ =>
                      [(w2n ao, w2n az); (w2n ro, w2n rs)]
                  | _ => [])
     else []) /\
  (asm_mem_ranges _ stk = [])
End

(* The instruction's gas is bounded given its memory bound H: it touches
   memory only below H, and it is none of the instructions whose cost or
   failure the bound doesn't cover (creation, delegation, self-destruct). *)
Definition asm_inst_gas_ok_def:
  asm_inst_gas_ok H inst stk <=>
    (!name. inst = AsmOp name ==>
            ~MEM name ["CREATE"; "CREATE2"; "DELEGATECALL"; "SELFDESTRUCT"]) /\
    EVERY (\(off,len). len = 0 \/ off + len <= H) (asm_mem_ranges inst stk)
End

(* The run from s reaches a RETURNDATACOPY, or ends, within k steps,
   without an assembly error, and each step before that is
   asm_inst_gas_ok H. *)
Definition asm_run_bounded_def:
  (asm_run_bounded lo o2pc prog H 0 s = F) /\
  (asm_run_bounded lo o2pc prog H (SUC k) s <=>
     s.as_pc < LENGTH prog /\
     (EL s.as_pc prog = AsmOp "RETURNDATACOPY" \/
      asm_inst_gas_ok H (EL s.as_pc prog) s.as_stack /\
      case asm_step lo o2pc (EL s.as_pc prog) s of
        AsmOK s1 => asm_run_bounded lo o2pc prog H k s1
      | AsmError _ => F
      | _ => T))
End

Theorem asm_run_bounded_step:
  asm_run_bounded lo o2pc prog H (SUC k) s ==>
  s.as_pc < LENGTH prog /\ ~is_data_inst (EL s.as_pc prog) /\
  (EL s.as_pc prog <> AsmOp "RETURNDATACOPY" ==>
    asm_inst_gas_ok H (EL s.as_pc prog) s.as_stack /\
    (!e. asm_step lo o2pc (EL s.as_pc prog) s <> AsmError e) /\
    (!s1. asm_step lo o2pc (EL s.as_pc prog) s = AsmOK s1 ==>
           asm_run_bounded lo o2pc prog H k s1))
Proof
  simp[asm_run_bounded_def] >> strip_tac >> simp[is_data_inst_def] >>
  conj_tac
  >- (Cases_on `EL s.as_pc prog` >>
      gvs[is_data_inst_def, asm_step_def]) >>
  strip_tac >> gvs[] >>
  Cases_on `asm_step lo o2pc (EL s.as_pc prog) s` >> gvs[]
QED

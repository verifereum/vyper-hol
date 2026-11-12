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
  asmSem asmWf vfmConstants words list

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
     else if MEM name ["STATICCALL"; "DELEGATECALL"] then
       (case stk of _ :: _ :: ao :: az :: ro :: rs :: _ =>
                      [(w2n ao, w2n az); (w2n ro, w2n rs)]
                  | _ => [])
     else if MEM name ["CREATE"; "CREATE2"] then
       (case stk of _ :: off :: sz :: _ => [(w2n off, w2n sz)] | _ => [])
     else []) /\
  (asm_mem_ranges _ stk = [])
End

(* The instruction's gas is bounded given its memory bound H: it touches
   memory only below H, and a CREATE or CREATE2 has an initcode within the
   EIP-3860 limit (the EVM fails a longer one with OutOfGas at any gas). *)
Definition asm_inst_gas_ok_def:
  asm_inst_gas_ok H inst stk <=>
    ((inst = AsmOp "CREATE" \/ inst = AsmOp "CREATE2") ==>
     case stk of _ :: _ :: sz :: _ => w2n sz <= 2 * max_code_size | _ => F) /\
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

Theorem word_memory_range_bounds[local]:
  !(x:bytes32) (y:bytes32).
    w2n x + w2n y <= 2 * dimword (:256) /\
    w2n x + 32 <= 2 * dimword (:256) /\
    w2n x + 1 <= 2 * dimword (:256)
Proof
  rpt gen_tac >>
  mp_tac (Q.ISPEC `x:bytes32` w2n_lt) >>
  mp_tac (Q.ISPEC `y:bytes32` w2n_lt) >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  simp[dimword_def] >> decide_tac
QED

Theorem asm_mem_ranges_bounded:
  EVERY (\(off,len). len = 0 \/ off + len <= 2 * dimword (:256))
    (asm_mem_ranges inst stk)
Proof
  Cases_on `inst` >> simp[asm_mem_ranges_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  (* Split the first stack cell separately to keep each case tactic small.
     Normalize the bound in the rewrite to match simp's numeric form. *)
  CASE_TAC >> simp[SRULE [] (CONV_RULE (DEPTH_CONV wordsLib.SIZES_CONV)
    word_memory_range_bounds), arithmeticTheory.ADD_SYM] >>
  rpt (CASE_TAC >> simp[SRULE [] (CONV_RULE (DEPTH_CONV wordsLib.SIZES_CONV)
    word_memory_range_bounds), arithmeticTheory.ADD_SYM])
QED

Theorem asm_run_bounded_mono:
  !k l s.
    asm_run_bounded lo o2pc prog H k s /\ k <= l ==>
    asm_run_bounded lo o2pc prog H l s
Proof
  Induct_on `k` >- simp[asm_run_bounded_def] >>
  Cases_on `l` >- simp[] >>
  rpt gen_tac >> simp[Once asm_run_bounded_def] >>
  strip_tac >> simp[Once asm_run_bounded_def] >>
  Cases_on `EL s.as_pc prog = AsmOp "RETURNDATACOPY"` >> simp[] >>
  Cases_on `asm_step lo o2pc (EL s.as_pc prog) s` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* The CALL families expose the same two ranges, after their value slot. *)
Theorem asm_inst_gas_ok_call_ranges:
  asm_inst_gas_ok H (AsmOp name) stk /\
  (name = "CALL" \/ name = "STATICCALL") /\
  6 + (if name = "CALL" then 1 else 0) <= LENGTH stk ==>
  (w2n (EL (3 + (if name = "CALL" then 1 else 0)) stk) = 0 \/
   w2n (EL (2 + (if name = "CALL" then 1 else 0)) stk) +
   w2n (EL (3 + (if name = "CALL" then 1 else 0)) stk) <= H) /\
  (w2n (EL (5 + (if name = "CALL" then 1 else 0)) stk) = 0 \/
   w2n (EL (4 + (if name = "CALL" then 1 else 0)) stk) +
   w2n (EL (5 + (if name = "CALL" then 1 else 0)) stk) <= H)
Proof
  strip_tac >>
  namedCases_on `stk` ["", "x0 xs0"] >> gvs[] >>
  namedCases_on `xs0` ["", "x1 xs1"] >> gvs[] >>
  namedCases_on `xs1` ["", "x2 xs2"] >> gvs[] >>
  namedCases_on `xs2` ["", "x3 xs3"] >> gvs[] >>
  namedCases_on `xs3` ["", "x4 xs4"] >> gvs[] >>
  namedCases_on `xs4` ["", "x5 xs5"] >> gvs[] >>
  Cases_on `name = "CALL"` >>
  gvs[asm_inst_gas_ok_def, asm_mem_ranges_def] >>
  namedCases_on `xs5` ["", "x6 xs6"] >>
  gvs[asm_inst_gas_ok_def, asm_mem_ranges_def]
QED

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

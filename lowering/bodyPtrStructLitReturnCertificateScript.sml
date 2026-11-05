(* Finite return-prefix certificates. Prefix states keep concrete evaluation
   separate from symbolic taint threading; no pointer-safety claim is made. *)
Theory bodyPtrStructLitReturnCertificate
Ancestors bodyPtrStructLitCalleeFixture bodyPtrStructLitGhostNormalize
  exprLoweringProps venomState venomInst ptrDiscipline ghostPcTransportPtr
  fragExecPtr allocationPtr list
Libs wordsLib intLib

(* Naming return-prefix states avoids repeating the compiler and memory terms
   in each independently checked machine and ghost equation. *)
Definition structlit_return_state_def:
  structlit_return_state n =
    case run_inst_seq
      (TAKE n (SND (structlit_callee_return_compiled F)).cs_current_insts)
      structlit_callee_initial of
      OK s => s
    | _ => structlit_callee_initial
End

Theorem structlit_return_instructions:
  (SND (structlit_callee_return_compiled F)).cs_current_insts =
    [mk_inst 0 ALLOCA [Lit 160w] ["%0"];
     mk_inst 1 ALLOCA [Lit 32w] ["%1"];
     mk_inst 2 MSTORE [Var "%1"; Lit 0w] [];
     mk_inst 3 ADD [Var "%0"; Lit 0w] ["%2"];
     mk_inst 4 MLOAD [Var "%1"] ["%3"];
     mk_inst 5 ADD [Var "%3"; Lit 31w] ["%4"];
     mk_inst 6 AND [Var "%4"; Lit (-32w)] ["%5"];
     mk_inst 7 ADD [Var "%5"; Lit 32w] ["%6"];
     mk_inst 8 MCOPY [Var "%2"; Var "%1"; Var "%6"] [];
     mk_inst 9 ALLOCA [Lit 64w] ["%7"];
     mk_inst 10 MSTORE [Var "%7"; Lit 0w] [];
     mk_inst 11 ADD [Var "%0"; Lit 96w] ["%8"];
     mk_inst 12 MCOPY [Var "%8"; Var "%7"; Lit 64w] [];
     mk_inst 13 MLOAD [Lit 32w] ["%9"];
     mk_inst 14 MLOAD [Lit 0w] ["%10"];
     mk_inst 15 MCOPY [Var "%10"; Var "%0"; Lit 160w] [];
     mk_inst 16 RET [Var "%9"] []]
Proof
  EVAL_TAC
QED


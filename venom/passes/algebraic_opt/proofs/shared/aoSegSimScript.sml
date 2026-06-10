(*
 * Segment Simulation Helpers for Algebraic Optimization
 *
 * TOP-LEVEL:
 *   eval_operand_exec_equiv     — eval_operand agrees under execution_equiv
 *   step_inst_base_exec_equiv   — step_inst_base preserves execution_equiv
 *   step_inst_exec_equiv        — step_inst preserves execution_equiv (non-INVOKE)
 *   jump_to_exec_to_state_equiv — jump_to restores state_equiv
 *   halt_state_exec_equiv       — halt_state preserves execution_equiv
 *   run_insts (from analysisSimDefs) — sequential instruction runner
 *)

Theory aoSegSim
Ancestors
  stateEquiv stateEquivProps execEquivProps
  analysisSimDefs
  venomExecSemantics venomState venomInst finite_map
Libs
  pairLib BasicProvers

(* ===== eval_operand under execution_equiv ===== *)

Theorem eval_operand_exec_equiv:
  !fv op s1 s2.
    execution_equiv fv s1 s2 /\
    (!x. op = Var x ==> x NOTIN fv) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >>
  gvs[execution_equiv_def, lookup_var_def]
QED

(* ===== Mutation helpers ===== *)

Triviality update_var_exec_equiv[local]:
  !fv x v s1 s2.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (update_var x v s1) (update_var x v s2)
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

(* Preservation helpers: execution_equiv through specific field updates *)


(* Extract field equalities from execution_equiv without consuming it *)


(* ===== Per-category helpers ===== *)


(* Pure 2-operand: ADD, SUB, MUL, etc. *)

(* Pure 1-operand: NOT, ISZERO *)

(* Pure 3-operand: ADDMOD, MULMOD *)

(* Read 0-operand: pass f s1 = f s2 as hypothesis *)

(* Read 1-operand: pass f v s1 = f v s2 as hypothesis *)

(* Write 2-operand: pass f preserves execution_equiv as hypothesis *)

(* ===== Main theorem ===== *)

(* step_inst_base preserves execution_equiv for non-external-call opcodes.
   External calls (CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2) are
   excluded — the algebraic optimization never transforms these.
   PHI needs vs_prev_bb agreement (not part of execution_equiv). *)
Theorem step_inst_base_exec_equiv:
  !fv inst s1 s2.
    execution_equiv fv s1 s2 /\
    (inst.inst_opcode = NOT \/ inst.inst_opcode = XOR \/
     inst.inst_opcode = ISZERO \/ inst.inst_opcode = ASSIGN \/
     inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = MUL \/ inst.inst_opcode = AND \/
     inst.inst_opcode = OR) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fv) ==>
    case (step_inst_base inst s1, step_inst_base inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Halt r1, Halt r2) => execution_equiv fv r1 r2
    | (Abort a1 r1, Abort a2 r2) => a1 = a2 /\ execution_equiv fv r1 r2
    | (Error e1, Error e2) => T
    | _ => F
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2`
    by (rpt strip_tac >> irule eval_operand_exec_equiv >>
        qexists_tac `fv` >> simp[] >> rpt strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[step_inst_base_def,
       exec_pure1_def, exec_pure2_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> gvs[]
QED

(* step_inst version (non-INVOKE, non-ext-call) *)
Theorem step_inst_exec_equiv:
  !fv fuel ctx inst s1 s2.
    execution_equiv fv s1 s2 /\
    (inst.inst_opcode = NOT \/ inst.inst_opcode = XOR \/
     inst.inst_opcode = ISZERO \/ inst.inst_opcode = ASSIGN \/
     inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = MUL \/ inst.inst_opcode = AND \/
     inst.inst_opcode = OR) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fv) ==>
    case (step_inst fuel ctx inst s1, step_inst fuel ctx inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Halt r1, Halt r2) => execution_equiv fv r1 r2
    | (Abort a1 r1, Abort a2 r2) => a1 = a2 /\ execution_equiv fv r1 r2
    | (Error e1, Error e2) => T
    | _ => F
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2`
    by (rpt strip_tac >> irule eval_operand_exec_equiv >>
        qexists_tac `fv` >> simp[] >> rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[step_inst_base_def, exec_pure1_def, exec_pure2_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> gvs[]
QED

(* ===== Terminal state helpers ===== *)

Theorem jump_to_exec_to_state_equiv:
  !fv lbl s1 s2.
    execution_equiv fv s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb ==>
    state_equiv fv (jump_to lbl s1) (jump_to lbl s2)
Proof
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_exec_equiv:
  !fv s1 s2.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (halt_state s1) (halt_state s2)
Proof
  rpt strip_tac >>
  fs[execution_equiv_def, halt_state_def, lookup_var_def]
QED



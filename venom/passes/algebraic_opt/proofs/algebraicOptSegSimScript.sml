(*
 * Segment Simulation Helpers for Algebraic Optimization
 *
 * TOP-LEVEL:
 *   eval_operand_exec_equiv     — eval_operand agrees under execution_equiv
 *   step_inst_base_exec_equiv   — step_inst_base preserves execution_equiv
 *   step_inst_exec_equiv        — step_inst preserves execution_equiv (non-INVOKE)
 *   jump_to_exec_to_state_equiv — jump_to restores state_equiv
 *   halt_state_exec_equiv       — halt_state preserves execution_equiv
 *   run_insts_def               — sequential instruction runner
 *   run_insts_exec_equiv        — run_insts preserves execution_equiv
 *)

Theory algebraicOptSegSim
Ancestors
  stateEquiv stateEquivProps execEquivProps
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
Triviality exec_equiv_upd_memory[local]:
  !fv s1 s2 m.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_memory := m) (s2 with vs_memory := m)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_upd_logs[local]:
  !fv s1 s2 l.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_logs := l) (s2 with vs_logs := l)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_upd_immutables[local]:
  !fv s1 s2 im.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_immutables := im) (s2 with vs_immutables := im)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_upd_alloca[local]:
  !fv s1 s2 al an.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv
      (s1 with <| vs_allocas := al; vs_alloca_next := an |>)
      (s2 with <| vs_allocas := al; vs_alloca_next := an |>)
Proof rw[execution_equiv_def, lookup_var_def]
QED

(* Extract field equalities from execution_equiv without consuming it *)
Triviality exec_equiv_upd_accounts[local]:
  !fv s1 s2 a.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_accounts := a) (s2 with vs_accounts := a)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_upd_transient[local]:
  !fv s1 s2 t.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_transient := t) (s2 with vs_transient := t)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_jump_to[local]:
  !fv lbl s1 s2.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (jump_to lbl s1) (jump_to lbl s2)
Proof rw[execution_equiv_def, jump_to_def, lookup_var_def]
QED

Triviality exec_equiv_upd_halted[local]:
  !fv s1 s2 h.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_halted := h) (s2 with vs_halted := h)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_upd_returndata[local]:
  !fv s1 s2 rd.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_returndata := rd)
                       (s2 with vs_returndata := rd)
Proof rw[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_sym_local[local]:
  !fv s1 s2. execution_equiv fv s1 s2 ==> execution_equiv fv s2 s1
Proof gvs[execution_equiv_def, lookup_var_def]
QED

Triviality exec_equiv_fields[local]:
  !fv s1 s2. execution_equiv fv s1 s2 ==>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next
Proof gvs[execution_equiv_def]
QED

(* ===== Per-category helpers ===== *)

Triviality ops_agree[local]:
  !fv inst s1 s2.
    execution_equiv fv s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fv) ==>
    !op. MEM op inst.inst_operands ==>
         eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >> irule eval_operand_exec_equiv >>
  qexists_tac `fv` >> simp[] >> rpt strip_tac >> gvs[]
QED

(* Pure 2-operand: ADD, SUB, MUL, etc. *)
Theorem exec_pure2_exec_equiv[local]:
  !fv f inst s1 s2.
    execution_equiv fv s1 s2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    case (exec_pure2 f inst s1, exec_pure2 f inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Error _, Error _) => T
    | _ => F
Proof
  rpt strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s2 = eval_operand op s1` by metis_tac[] >>
  simp[exec_pure2_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> simp[]
QED

(* Pure 1-operand: NOT, ISZERO *)
Triviality exec_pure1_exec_equiv[local]:
  !fv f inst s1 s2.
    execution_equiv fv s1 s2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    case (exec_pure1 f inst s1, exec_pure1 f inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Error _, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[exec_pure1_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> simp[]
QED

(* Pure 3-operand: ADDMOD, MULMOD *)
Triviality exec_pure3_exec_equiv[local]:
  !fv f inst s1 s2.
    execution_equiv fv s1 s2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    case (exec_pure3 f inst s1, exec_pure3 f inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Error _, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[exec_pure3_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> simp[]
QED

(* Read 0-operand: pass f s1 = f s2 as hypothesis *)
Triviality exec_read0_exec_equiv[local]:
  !fv f inst s1 s2.
    execution_equiv fv s1 s2 /\
    f s1 = f s2 ==>
    case (exec_read0 f inst s1, exec_read0 f inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Error _, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[exec_read0_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> simp[]
QED

(* Read 1-operand: pass f v s1 = f v s2 as hypothesis *)
Triviality exec_read1_exec_equiv[local]:
  !fv f inst s1 s2.
    execution_equiv fv s1 s2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!v. f v s1 = f v s2) ==>
    case (exec_read1 f inst s1, exec_read1 f inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Error _, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[exec_read1_def] >>
  every_case_tac >> gvs[] >>
  irule update_var_exec_equiv >> simp[]
QED

(* Write 2-operand: pass f preserves execution_equiv as hypothesis *)
Triviality exec_write2_exec_equiv[local]:
  !fv f inst s1 s2.
    execution_equiv fv s1 s2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!v1 v2. execution_equiv fv (f v1 v2 s1) (f v1 v2 s2)) ==>
    case (exec_write2 f inst s1, exec_write2 f inst s2) of
      (OK r1, OK r2) => execution_equiv fv r1 r2
    | (Error _, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[exec_write2_def] >>
  every_case_tac >> gvs[]
QED

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

(* ===== Sequential instruction runner ===== *)

(* Run a list of non-terminator instructions sequentially.
   Unlike exec_block, does not require a terminator at the end. *)
Definition run_insts_def:
  run_insts fuel ctx [] s = OK s /\
  run_insts fuel ctx (inst :: rest) s =
    case step_inst fuel ctx inst s of
      OK s' => run_insts fuel ctx rest s'
    | err => err
End


(* Helper: execution_equiv is preserved by setting inst_idx *)
Theorem exec_equiv_set_idx:
  !fv s1 s2 idx.
    execution_equiv fv s1 s2 ==>
    execution_equiv fv (s1 with vs_inst_idx := idx)
                       (s2 with vs_inst_idx := idx)
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

val _ = export_theory();

(* Positive instruction inventory for administrative pending fragments. *)
Theory staticAbortAdminRows
Ancestors
  prefixExec planExec asmSem asmIR stackOpSim list rich_list arithmetic
Libs
  BasicProvers

Theorem pending_admin_instruction_rows:
  !ops lo h fmp ins.
    prefix_wf lo h ops /\ MEM ins (execute_plan fmp ops) ==>
    case ins of
      AsmLabel _ => T
    | AsmPush _ => T
    | AsmPushLabel l => IS_SOME (FLOOKUP lo l)
    | AsmPushOfst l _ => IS_SOME (FLOOKUP lo l)
    | AsmOp name =>
        (?n. ALOOKUP dup_table name = SOME n /\ n < 16) \/
        (?n. ALOOKUP swap_table name = SOME n /\ 0 < n /\ n <= 16) \/
        name = "POP" \/ name = "MSTORE" \/ name = "MLOAD"
    | _ => F
Proof
  Induct >> simp[prefix_wf_def, execute_plan_def, MEM_APPEND] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> strip_tac
  >- (rename1 `MEM ins (exec_stack_op fmp op0)` >>
      Cases_on `op0` >> gvs[stack_op_wf_def, exec_stack_op_def]
      >~ [`exec_stack_op _ (SOPush _)`] >- (
        rename1 `MEM ins (exec_stack_op fmp (SOPush operand))` >>
        Cases_on `operand` >> gvs[stack_op_wf_def, exec_stack_op_def])
      >~ [`ALOOKUP swap_table (swap_name _)`] >- (
        rename1 `0 < k` >>
        disj2_tac >> disj1_tac >> qexists `k` >> simp[swap_table_lookup])
      >~ [`ALOOKUP dup_table (dup_name _)`] >- (
        (rename1 `0 < k` >>
        `k - 1 <= 15 /\ k = (k - 1) + 1` by decide_tac >>
        drule dup_table_lookup >> simp[GSYM ADD1] >> strip_tac >>
        disj1_tac >> qexists `k - 1` >> simp[] >> (metis_tac[GSYM ADD1, dup_table_lookup])))) >>
  rewrite_tac[GSYM execute_plan_def] >>
  first_x_assum irule >>
  conj_tac
  >- (qexists `fmp` >> simp[execute_plan_def]) >>
  qexists `n'` >> simp[]
QED

(* The explicit emission lists are in PC order.  In particular the two
   JUMPI producers sit immediately before the branch, and only the local
   ASSERT_UNREACHABLE fallthrough is INVALID. *)
Theory staticAbortEmitRows
Ancestors
  staticAbortEmit staticAbortStraight stackPlanGen planExec asmSymSem
  asmSem asmIR venomInst words finite_map alist list arithmetic

Theorem pending_static_emit_rows:
  generate_emit_ops inst topics ps = (ops,ps') ==>
  let code = execute_plan fmp ops in
  (static_abort_emit_io inst a b ==>
    (?name. code = [AsmOp name] /\
       static_abort_straight name b /\ a = asm_op_arity name) \/
    (inst.inst_opcode = INITIAL_FMP /\ a = 0 /\ b = 1 /\
       ?bs. code = [AsmPush bs]) \/
    (inst.inst_opcode = BUMP /\ a = 2 /\ b = 2 /\
       code = [AsmOp "DUP2"; AsmOp "ADD"] /\
       ALOOKUP dup_table "DUP2" = SOME 1 /\
       asm_op_arity "ADD" = 2 /\ static_abort_straight "ADD" 1) \/
    (inst.inst_opcode = ISTORE /\ a = 2 /\ b = 0 /\
       code = [AsmOp "SWAP1"; AsmOp "MSTORE"] /\
       ALOOKUP swap_table "SWAP1" = SOME 1 /\
       asm_op_arity "MSTORE" = 2 /\ static_abort_straight "MSTORE" 0) \/
    (inst.inst_opcode = ASSERT /\ a = 1 /\ b = 0 /\
       code = [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] /\
       asm_op_arity "ISZERO" = 1 /\ static_abort_straight "ISZERO" 1 /\
       asm_op_arity "JUMPI" = 2 /\ asm_op_arity "REVERT" = 2 /\
       ALOOKUP dup_table "DUP1" = SOME 0 /\
       (!lo o2pc prog pc.
         static_abort_emit_labels lo o2pc prog fmp pc inst ops ==>
         ?off dest. FLOOKUP lo "revert" = SOME off /\
           FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME dest /\
           asm_block_at prog dest
             [AsmLabel "revert"; AsmPush (encode_num_bytes_fuel 32 0);
              AsmOp "DUP1"; AsmOp "REVERT"])) \/
    (inst.inst_opcode = ASSERT_UNREACHABLE /\ a = 1 /\ b = 0 /\
       asm_op_arity "JUMPI" = 2 /\
       ?lbl. code = [AsmPushLabel lbl; AsmOp "JUMPI";
                     AsmOp "INVALID"; AsmLabel lbl] /\
         (!lo o2pc prog pc.
           static_abort_emit_labels lo o2pc prog fmp pc inst ops ==>
           ?off. FLOOKUP lo lbl = SOME off /\
                 FLOOKUP o2pc (w2n (n2w off : bytes32)) = SOME (pc + 3))) \/
    (code = [] /\ a = 0 /\ b = 0)) /\
  (MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\
   (inst.inst_opcode = LOG ==> topics <= 4) ==>
   ?name. code = [AsmOp name] /\
     (inst.inst_opcode = SSTORE /\ name = "SSTORE" \/
      inst.inst_opcode = TSTORE /\ name = "TSTORE" \/
      inst.inst_opcode = LOG /\ name = "LOG" ++ num_to_dec_string topics /\
      MEM name ["LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"]) /\
     asm_op_arity name = if inst.inst_opcode = LOG then 2 + topics else 2)
Proof
  simp[] >> strip_tac >> conj_tac
  >- (simp[static_abort_emit_io_def] >> strip_tac
      >- (drule generate_emit_ops_some >>
          disch_then (qspecl_then [`topics`, `ps`] assume_tac) >>
          gvs[execute_plan_def, exec_stack_op_def])
      >- (gvs[generate_emit_ops_def, execute_plan_def, exec_stack_op_def])
      >- (gvs[generate_emit_ops_def, bump_emit_ops_def, dup_name_def,
              execute_plan_def, exec_stack_op_def] >> EVAL_TAC)
      >- (gvs[generate_emit_ops_def, venom_to_evm_name_def,
              execute_plan_def, exec_stack_op_def] >> EVAL_TAC)
      >- (gvs[generate_emit_ops_def, venom_to_evm_name_def,
              execute_plan_def, exec_stack_op_def, static_abort_emit_labels_def,
              revert_postamble_def] >>
          CONV_TAC (DEPTH_CONV (REWR_CONV asm_op_arity_def THENC EVAL)) >>
          simp[dup_table_def, static_abort_straight_def])
      >- (gvs[generate_emit_ops_def, venom_to_evm_name_def] >>
          pairarg_tac >> gvs[execute_plan_def, exec_stack_op_def,
                             static_abort_emit_labels_def] >>
          CONV_TAC (DEPTH_CONV (REWR_CONV asm_op_arity_def THENC EVAL)) >>
          simp[]) >>
      `generate_emit_ops inst topics ps = ([],ps)` by
        (irule static_abort_emit_empty >> simp[]) >>
      gvs[execute_plan_def]) >>
  strip_tac >> gvs[generate_emit_ops_def, venom_to_evm_name_def,
                   execute_plan_def, exec_stack_op_def]
  >- EVAL_TAC
  >- EVAL_TAC >>
  `topics = 0 \/ topics = 1 \/ topics = 2 \/ topics = 3 \/ topics = 4` by decide_tac >>
  gvs[] >> EVAL_TAC
QED

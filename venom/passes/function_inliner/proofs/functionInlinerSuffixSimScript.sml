(*
 * Block Suffix Simulation
 *
 * Key result: step_inst for non-PHI, non-terminator, non-INVOKE
 * commutes with metadata field changes (vs_current_bb, vs_inst_idx,
 * vs_prev_bb). This enables proving that running a block suffix
 * from different metadata starting points produces execution-equivalent
 * results.
 *)

Theory functionInlinerSuffixSim
Ancestors venomExecSemantics venomInst venomExecProps stateEquiv
          stateEquivProps execEquivProps functionInlinerBlockSplit

open BasicProvers
open listTheory rich_listTheory venomStateTheory
     venomExecSemanticsTheory venomInstTheory venomExecPropsTheory
     stateEquivTheory stateEquivPropsTheory execEquivPropsTheory
     functionInlinerBlockSplitTheory

(* ================================================================
   Metadata adjustment and result mapping
   ================================================================ *)

Definition md_adj_def:
  md_adj bb1 idx1 prev1 (s:venom_state) =
    s with <|vs_current_bb := bb1; vs_inst_idx := idx1; vs_prev_bb := prev1|>
End

Definition map_exec_result_def:
  (map_exec_result f (OK s) = OK (f s)) /\
  (map_exec_result f (Halt s) = Halt (f s)) /\
  (map_exec_result f (Abort a s) = Abort a (f s)) /\
  (map_exec_result f (IntRet v s) = IntRet v (f s)) /\
  (map_exec_result f (Error e) = Error e)
End

(* ================================================================
   md_adj field accessors — resolves field accesses without
   fully unfolding md_adj_def (prevents extract_venom_result
   rewrite breakage)
   ================================================================ *)

Theorem md_adj_fields[local]:
  (md_adj bb1 idx1 prev1 s).vs_current_bb = bb1 /\
  (md_adj bb1 idx1 prev1 s).vs_inst_idx = idx1 /\
  (md_adj bb1 idx1 prev1 s).vs_prev_bb = prev1 /\
  (md_adj bb1 idx1 prev1 s).vs_vars = s.vs_vars /\
  (md_adj bb1 idx1 prev1 s).vs_params = s.vs_params /\
  (md_adj bb1 idx1 prev1 s).vs_memory = s.vs_memory /\
  (md_adj bb1 idx1 prev1 s).vs_accounts = s.vs_accounts /\
  (md_adj bb1 idx1 prev1 s).vs_logs = s.vs_logs /\
  (md_adj bb1 idx1 prev1 s).vs_returndata = s.vs_returndata /\
  (md_adj bb1 idx1 prev1 s).vs_transient = s.vs_transient /\
  (md_adj bb1 idx1 prev1 s).vs_labels = s.vs_labels /\
  (md_adj bb1 idx1 prev1 s).vs_call_ctx = s.vs_call_ctx /\
  (md_adj bb1 idx1 prev1 s).vs_tx_ctx = s.vs_tx_ctx /\
  (md_adj bb1 idx1 prev1 s).vs_block_ctx = s.vs_block_ctx /\
  (md_adj bb1 idx1 prev1 s).vs_prev_hashes = s.vs_prev_hashes /\
  (md_adj bb1 idx1 prev1 s).vs_halted = s.vs_halted /\
  (md_adj bb1 idx1 prev1 s).vs_data_section = s.vs_data_section /\
  (md_adj bb1 idx1 prev1 s).vs_immutables = s.vs_immutables /\
  (md_adj bb1 idx1 prev1 s).vs_code = s.vs_code /\
  (md_adj bb1 idx1 prev1 s).vs_allocas = s.vs_allocas
Proof
  simp[md_adj_def]
QED

(* ================================================================
   eval_operand/eval_operands ignore metadata fields
   ================================================================ *)

Theorem eval_operand_bb_irrel[local]:
  !op (s:venom_state) bb1 idx1 prev1.
    eval_operand op (md_adj bb1 idx1 prev1 s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, md_adj_def]
QED

Theorem eval_operands_bb_irrel[local]:
  !ops (s:venom_state) bb1 idx1 prev1.
    eval_operands ops (md_adj bb1 idx1 prev1 s) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, eval_operand_bb_irrel]
QED

(* ================================================================
   State-modifying helpers commute with md_adj
   ================================================================ *)

Theorem update_var_bb_commute[local]:
  !v w (s:venom_state) bb1 idx1 prev1.
    update_var v w (md_adj bb1 idx1 prev1 s) =
    md_adj bb1 idx1 prev1 (update_var v w s)
Proof
  simp[update_var_def, md_adj_def]
QED

(* FOLDL update_var commutes with md_adj *)
Theorem foldl_update_var_bb_commute[local]:
  !pairs (s:venom_state) bb1 idx1 prev1.
    FOLDL (\s' (out,val). update_var out val s') (md_adj bb1 idx1 prev1 s)
      pairs =
    md_adj bb1 idx1 prev1
      (FOLDL (\s' (out,val). update_var out val s') s pairs)
Proof
  Induct >> simp[] >> Cases >> simp[update_var_bb_commute]
QED

(* setup_callee doesn't depend on md_adj fields — it overwrites them *)
Theorem setup_callee_bb_irrel[local]:
  !fn args (s:venom_state) bb1 idx1 prev1.
    setup_callee fn args (md_adj bb1 idx1 prev1 s) = setup_callee fn args s
Proof
  rw[setup_callee_def, md_adj_def]
QED

(* merge_callee_state commutes with md_adj on the caller side *)
Theorem merge_callee_state_bb_commute[local]:
  !callee_s (s:venom_state) bb1 idx1 prev1.
    merge_callee_state (md_adj bb1 idx1 prev1 s) callee_s =
    md_adj bb1 idx1 prev1 (merge_callee_state s callee_s)
Proof
  simp[merge_callee_state_def, md_adj_def]
QED

(* bind_outputs commutes with md_adj *)
Theorem bind_outputs_bb_commute[local]:
  !outs vals (s:venom_state) bb1 idx1 prev1.
    bind_outputs outs vals (md_adj bb1 idx1 prev1 s) =
    OPTION_MAP (md_adj bb1 idx1 prev1) (bind_outputs outs vals s)
Proof
  rw[bind_outputs_def] >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[] >>
  simp[foldl_update_var_bb_commute]
QED

Theorem write_memory_exp_bb_commute[local]:
  !off bytes (s:venom_state) bb1 idx1 prev1.
    write_memory_with_expansion off bytes (md_adj bb1 idx1 prev1 s) =
    md_adj bb1 idx1 prev1 (write_memory_with_expansion off bytes s)
Proof
  simp[write_memory_with_expansion_def, md_adj_def, LET_THM]
QED

Theorem halt_state_bb_commute[local]:
  !(s:venom_state) bb1 idx1 prev1.
    halt_state (md_adj bb1 idx1 prev1 s) =
    md_adj bb1 idx1 prev1 (halt_state s)
Proof
  simp[halt_state_def, md_adj_def]
QED

Theorem set_returndata_bb_commute[local]:
  !rd (s:venom_state) bb1 idx1 prev1.
    set_returndata rd (md_adj bb1 idx1 prev1 s) =
    md_adj bb1 idx1 prev1 (set_returndata rd s)
Proof
  simp[set_returndata_def, md_adj_def]
QED

Theorem revert_state_bb_commute[local]:
  !(s:venom_state) bb1 idx1 prev1.
    revert_state (md_adj bb1 idx1 prev1 s) =
    md_adj bb1 idx1 prev1 (revert_state s)
Proof
  simp[revert_state_def, md_adj_def]
QED

(* ================================================================
   State-reading helpers are irrel to metadata
   ================================================================ *)

Theorem read_memory_bb_irrel[local]:
  !off sz (s:venom_state) bb1 idx1 prev1.
    read_memory off sz (md_adj bb1 idx1 prev1 s) = read_memory off sz s
Proof
  simp[read_memory_def, md_adj_def]
QED

Theorem venom_to_tx_params_bb_irrel[local]:
  !(s:venom_state) bb1 idx1 prev1.
    venom_to_tx_params (md_adj bb1 idx1 prev1 s) = venom_to_tx_params s
Proof
  simp[venom_to_tx_params_def, md_adj_def]
QED

Theorem make_venom_call_state_bb_irrel[local]:
  !(s:venom_state) bb1 idx1 prev1 tgt gas val cd code is_st.
    make_venom_call_state (md_adj bb1 idx1 prev1 s)
      tgt gas val cd code is_st =
    make_venom_call_state s tgt gas val cd code is_st
Proof
  simp[make_venom_call_state_def, venom_to_tx_params_bb_irrel,
       md_adj_def, LET_THM]
QED

Theorem make_venom_delegatecall_state_bb_irrel[local]:
  !(s:venom_state) bb1 idx1 prev1 tgt gas cd code is_st.
    make_venom_delegatecall_state (md_adj bb1 idx1 prev1 s)
      tgt gas cd code is_st =
    make_venom_delegatecall_state s tgt gas cd code is_st
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_bb_irrel,
       md_adj_def, LET_THM]
QED

Theorem make_venom_create_state_bb_irrel[local]:
  !(s:venom_state) bb1 idx1 prev1 addr gas val ic.
    make_venom_create_state (md_adj bb1 idx1 prev1 s)
      addr gas val ic =
    make_venom_create_state s addr gas val ic
Proof
  simp[make_venom_create_state_def, venom_to_tx_params_bb_irrel,
       md_adj_def, LET_THM]
QED

(* ================================================================
   extract_venom_result commutation

   Key lemma for external calls. The output state gets md_adj
   because extract_venom_result writes s with <|exec fields|>
   and md_adj only touches metadata fields.
   ================================================================ *)

Triviality extract_venom_result_bb_commute_optmap[local]:
  !s bb1 idx1 prev1 output_val retOff retSize run_result.
    extract_venom_result (md_adj bb1 idx1 prev1 s) output_val retOff retSize
      run_result =
    OPTION_MAP (\(output, s'). (output, md_adj bb1 idx1 prev1 s'))
      (extract_venom_result s output_val retOff retSize run_result)
Proof
  rpt gen_tac >>
  simp[extract_venom_result_def, md_adj_def, LET_THM] >>
  EVERY_CASE_TAC >>
  simp[write_memory_with_expansion_def, md_adj_def, LET_THM]
QED

Theorem extract_venom_result_bb_commute[local]:
  !s bb1 idx1 prev1 output_val retOff retSize run_result.
    extract_venom_result (md_adj bb1 idx1 prev1 s) output_val retOff retSize
      run_result =
    case extract_venom_result s output_val retOff retSize run_result of
      NONE => NONE
    | SOME (output, s') => SOME (output, md_adj bb1 idx1 prev1 s')
Proof
  rpt gen_tac >>
  Cases_on `extract_venom_result s output_val retOff retSize run_result` >>
  simp[extract_venom_result_bb_commute_optmap] >>
  Cases_on `x` >> simp[]
QED

(* Per-external-call opcode commutation lemmas *)
fun ext_call_tac (asl, g) =
  (simp[step_inst_base_def,
        exec_ext_call_def, exec_delegatecall_def, exec_create_def,
        eval_operand_bb_irrel, eval_operands_bb_irrel,
        extract_venom_result_bb_commute,
        md_adj_fields, read_memory_bb_irrel,
        make_venom_call_state_bb_irrel,
        make_venom_delegatecall_state_bb_irrel,
        make_venom_create_state_bb_irrel,
        map_exec_result_def, LET_THM] >>
   EVERY_CASE_TAC >>
   simp[map_exec_result_def, md_adj_def, update_var_def]) (asl, g);

Theorem step_inst_base_bb_commute_call[local]:
  !inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode = CALL ==>
    step_inst_base inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> ext_call_tac
QED

Theorem step_inst_base_bb_commute_staticcall[local]:
  !inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode = STATICCALL ==>
    step_inst_base inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> ext_call_tac
QED

Theorem step_inst_base_bb_commute_delegatecall[local]:
  !inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode = DELEGATECALL ==>
    step_inst_base inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> ext_call_tac
QED

Theorem step_inst_base_bb_commute_create[local]:
  !inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode = CREATE ==>
    step_inst_base inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> ext_call_tac
QED

Theorem step_inst_base_bb_commute_create2[local]:
  !inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode = CREATE2 ==>
    step_inst_base inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> ext_call_tac
QED

Theorem step_inst_base_bb_commute:
  !inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    step_inst_base inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  (* Handle external call opcodes via pre-proved lemmas *)
  TRY (irule step_inst_base_bb_commute_call >> simp[] >> NO_TAC) >>
  TRY (irule step_inst_base_bb_commute_staticcall >> simp[] >> NO_TAC) >>
  TRY (irule step_inst_base_bb_commute_delegatecall >> simp[] >> NO_TAC) >>
  TRY (irule step_inst_base_bb_commute_create >> simp[] >> NO_TAC) >>
  TRY (irule step_inst_base_bb_commute_create2 >> simp[] >> NO_TAC) >>
  (* All remaining opcodes *)
  simp[step_inst_base_def,
       exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def, exec_alloca_def,
       eval_operand_bb_irrel, eval_operands_bb_irrel,
       mload_def, sload_def, tload_def,
       write_memory_def, mstore_def, mstore8_def, sstore_def, tstore_def, mcopy_def,
       contract_storage_def, contract_transient_def,
       next_alloca_offset_def, map_exec_result_def, LET_THM,
       md_adj_fields] >>
  EVERY_CASE_TAC >>
  simp[map_exec_result_def, update_var_def, md_adj_def,
       write_memory_with_expansion_def, halt_state_def,
       set_returndata_def, revert_state_def, LET_THM,
       next_alloca_offset_def]
QED

(* Lift to step_inst: non-PHI, non-terminator, non-INVOKE *)
Theorem step_inst_bb_commute:
  !fuel ctx inst (s:venom_state) bb1 idx1 prev1.
    inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (md_adj bb1 idx1 prev1 s) =
    map_exec_result (md_adj bb1 idx1 prev1) (step_inst fuel ctx inst s)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_def] >>
  fs[is_terminator_def] >>
  simp[step_inst_base_bb_commute, md_adj_def]
QED

(* ================================================================
   eval_operand / eval_operands respect execution_equiv
   ================================================================ *)

Triviality eval_operand_exec_equiv:
  !vars op s1 s2.
    execution_equiv vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, execution_equiv_def, lookup_var_def]
QED

Triviality eval_operands_exec_equiv:
  !vars ops s1 s2.
    execution_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >>
  (SUBGOAL_THEN ``eval_operand h s1 = eval_operand h s2`` (fn th => rewrite_tac [th]) >- (
    irule eval_operand_exec_equiv >> simp[] >> metis_tac[]
  )) >>
  (SUBGOAL_THEN ``eval_operands ops s1 = eval_operands ops s2`` (fn th => rewrite_tac [th]) >- (
    first_x_assum irule >> simp[] >> metis_tac[]
  ))
QED

(* ================================================================
   Composition: result_equiv + lift_result → lift_result

   result_equiv vars r1 r2 says same-constructor with
     OK: state_equiv vars, Halt/Abort/IntRet: execution_equiv vars
   lift_result (exec_equiv {}) r2 r3 says same-constructor with
     OK/Halt/Abort/IntRet: execution_equiv {}

   Composing: state_equiv → execution_equiv → subset to vars → trans
   ================================================================ *)

Triviality result_equiv_lift_result_trans:
  !vars r1 r2 r3.
    result_equiv vars r1 r2 /\
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      r2 r3 ==>
    lift_result (execution_equiv vars) (\s1 s2. execution_equiv vars s1 s2)
      r1 r3
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  fs[result_equiv_def, lift_result_def, state_equiv_def] >> rpt strip_tac >>
  irule execution_equiv_trans >>
  first_assum (irule_at (Pos hd)) >>
  irule execution_equiv_subset >>
  qexists_tac `{}` >> simp[]
QED

(* ================================================================
   Per-opcode terminator execution_equiv lemmas

   For each terminator opcode, step_inst_base on md_adj'd state
   produces execution_equiv {} results vs the original state.
   ================================================================ *)

val term_base_tac =
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def, LET_THM,
       eval_operand_bb_irrel, eval_operands_bb_irrel] >>
  EVERY_CASE_TAC >>
  simp[lift_result_def, execution_equiv_def, lookup_var_def,
       jump_to_def, md_adj_def, halt_state_def, set_returndata_def,
       revert_state_def];

Triviality md_adj_exec_equiv_JMP:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = JMP ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_JNZ:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = JNZ ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_DJMP:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = DJMP ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_RET:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = RET ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_RETURN:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = RETURN ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_REVERT:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = REVERT ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_STOP:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = STOP ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_SINK:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = SINK ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_SELFDESTRUCT:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = SELFDESTRUCT ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

Triviality md_adj_exec_equiv_INVALID:
  !inst bb1 idx1 prev1 s.
    inst.inst_opcode = INVALID ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof term_base_tac
QED

(* Combine per-opcode lemmas *)
Triviality step_inst_base_term_md_adj_exec_equiv:
  !inst bb1 idx1 prev1 s.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    lift_result (execution_equiv {}) (\s1 s2. execution_equiv {} s1 s2)
      (step_inst_base inst (md_adj bb1 idx1 prev1 s))
      (step_inst_base inst s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  metis_tac[md_adj_exec_equiv_JMP, md_adj_exec_equiv_JNZ,
            md_adj_exec_equiv_DJMP, md_adj_exec_equiv_RET,
            md_adj_exec_equiv_RETURN, md_adj_exec_equiv_REVERT,
            md_adj_exec_equiv_STOP, md_adj_exec_equiv_SINK,
            md_adj_exec_equiv_SELFDESTRUCT, md_adj_exec_equiv_INVALID]
QED

(* ================================================================
   Unified step_inst execution_equiv for terminators

   Uses: result_equiv (from step_inst_result_equiv on md_adj'd states)
         + md_adj exec_equiv (per-opcode above)
         + composition lemma
   ================================================================ *)

Triviality step_inst_exec_equiv_term_helper:
  !fuel ctx vars inst s1 s2.
    execution_equiv vars s1 s2 /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (execution_equiv vars) (\s1 s2. execution_equiv vars s1 s2)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s2_adj = md_adj s1.vs_current_bb s1.vs_inst_idx s1.vs_prev_bb s2` >>
  (* state_equiv vars s1 s2_adj *)
  (SUBGOAL_THEN ``state_equiv vars s1 s2_adj`` ASSUME_TAC >- (
    gvs[state_equiv_def, Abbr `s2_adj`, md_adj_def,
        execution_equiv_def, lookup_var_def]
  )) >>
  (* result_equiv via step_inst_result_equiv *)
  (SUBGOAL_THEN ``result_equiv vars (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2_adj)`` ASSUME_TAC >- (
    irule (REWRITE_RULE [GSYM AND_IMP_INTRO] step_inst_result_equiv) >>
    fs[]
  )) >>
  (* step_inst = step_inst_base for terminators (non-INVOKE) *)
  (SUBGOAL_THEN ``step_inst fuel ctx inst s2_adj = step_inst_base inst s2_adj`` ASSUME_TAC >- (
    simp[step_inst_def] >> fs[is_terminator_def]
  )) >>
  (SUBGOAL_THEN ``step_inst fuel ctx inst s2 = step_inst_base inst s2`` ASSUME_TAC >- (
    simp[step_inst_def] >> fs[is_terminator_def]
  )) >>
  fs[] >>
  irule result_equiv_lift_result_trans >>
  qexists_tac `step_inst_base inst s2_adj` >> simp[] >>
  simp[Abbr `s2_adj`] >>
  irule step_inst_base_term_md_adj_exec_equiv >> simp[]
QED

(* ================================================================
   INVOKE preserves execution_equiv directly.

   Under execution_equiv vars, s1 and s2 agree on all fields except
   vs_current_bb, vs_inst_idx, vs_prev_bb. INVOKE reads operands (agree
   for vars not in vars), setup_callee overwrites md_adj fields so both
   produce the same callee state, run_function gives identical results,
   and merge_callee_state + bind_outputs preserve execution_equiv vars.
   ================================================================ *)

Triviality setup_callee_exec_equiv:
  !vars fn args (s1:venom_state) s2.
    execution_equiv vars s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rpt strip_tac >> simp[setup_callee_def] >>
  IF_CASES_TAC >> simp[] >>
  fs[execution_equiv_def] >>
  simp[venom_state_component_equality]
QED

Triviality merge_callee_state_exec_equiv:
  !vars (s1:venom_state) s2 callee_s.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (merge_callee_state s1 callee_s)
                         (merge_callee_state s2 callee_s)
Proof
  rpt strip_tac >>
  fs[execution_equiv_def, merge_callee_state_def, lookup_var_def]
QED

Triviality update_var_exec_equiv:
  !vars v val (s1:venom_state) s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (update_var v val s1) (update_var v val s2)
Proof
  rpt strip_tac >>
  fs[execution_equiv_def, update_var_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE]
QED

Triviality foldl_update_var_exec_equiv:
  !pairs vars (s1:venom_state) s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> simp[] >> Cases >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  irule update_var_exec_equiv >> first_assum ACCEPT_TAC
QED

Triviality bind_outputs_exec_equiv:
  !vars outs vals (s1:venom_state) s2.
    execution_equiv vars s1 s2 ==>
    bind_outputs outs vals s1 = NONE /\ bind_outputs outs vals s2 = NONE \/
    ?s1' s2'. bind_outputs outs vals s1 = SOME s1' /\
              bind_outputs outs vals s2 = SOME s2' /\
              execution_equiv vars s1' s2'
Proof
  rpt strip_tac >> simp[bind_outputs_def] >>
  strip_tac >>
  irule foldl_update_var_exec_equiv >> simp[]
QED

Triviality step_inst_invoke_exec_equiv:
  !fuel ctx vars inst s1 s2.
    execution_equiv vars s1 s2 /\
    inst.inst_opcode = INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (execution_equiv vars) (\s1 s2. execution_equiv vars s1 s2)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_def] >>
  (* After simp with inst.inst_opcode = INVOKE:
     goal is about case decode_invoke inst of ... for both s1, s2 *)
  Cases_on `decode_invoke inst` >> simp[lift_result_def] >>
  rename1 `decode_invoke inst = SOME di` >>
  Cases_on `di` >> simp[] >>
  rename1 `decode_invoke inst = SOME (callee_name, arg_ops)` >>
  (* arg_ops are a tail of inst.inst_operands, so Var membership transfers *)
  (SUBGOAL_THEN ``!x. MEM (Var x) arg_ops ==> x NOTIN vars`` ASSUME_TAC >- (
    rpt strip_tac >>
    qpat_x_assum `!x. MEM (Var x) inst.inst_operands ==> _`
      (fn th => mp_tac (SPEC ``x:string`` th)) >>
    impl_tac >- (
      qpat_x_assum `decode_invoke _ = SOME _` mp_tac >>
      simp[decode_invoke_def] >>
      BasicProvers.EVERY_CASE_TAC >> simp[] >>
      strip_tac >> gvs[MEM]
    ) >> simp[]
  )) >>
  (* eval_operands agree on arg_ops *)
  (SUBGOAL_THEN ``eval_operands arg_ops s1 = eval_operands arg_ops s2``
    (fn th => rewrite_tac [th]) >- (
    irule eval_operands_exec_equiv >> qexists_tac `vars` >> simp[]
  )) >>
  (* Now both sides share eval_operands arg_ops s2.
     Case-split on shared intermediates *)
  Cases_on `lookup_function callee_name ctx.ctx_functions` >>
  simp[lift_result_def] >>
  Cases_on `eval_operands arg_ops s2` >> simp[lift_result_def] >>
  (* setup_callee produces identical states *)
  (SUBGOAL_THEN ``setup_callee x x' s1 = setup_callee x x' s2``
    (fn th => rewrite_tac [th]) >- (
    irule setup_callee_exec_equiv >> metis_tac[]
  )) >>
  Cases_on `setup_callee x x' s2` >> simp[lift_result_def] >>
  (* run_function is identical — same callee state *)
  Cases_on `run_function fuel ctx x x''` >>
  simp[lift_result_def, execution_equiv_refl] >>
  (* IntRet: merge_callee_state preserves exec_equiv *)
  (SUBGOAL_THEN ``execution_equiv vars (merge_callee_state s1 v)
                                        (merge_callee_state s2 v)``
    ASSUME_TAC >- (
    irule merge_callee_state_exec_equiv >> metis_tac[]
  )) >>
  (* bind_outputs preserves exec_equiv *)
  qpat_x_assum `execution_equiv _ (merge_callee_state _ _) _` mp_tac >>
  disch_then (fn th => mp_tac (MATCH_MP bind_outputs_exec_equiv th)) >>
  disch_then (qspecl_then [`inst.inst_outputs`, `l`] mp_tac) >>
  strip_tac >> fs[lift_result_def]
QED

(* ================================================================
   Main result: execution_equiv preservation across step_inst
   for non-PHI instructions (including INVOKE).
   ================================================================ *)

Theorem step_inst_exec_equiv:
  !fuel ctx vars inst s1 s2.
    execution_equiv vars s1 s2 /\
    inst.inst_opcode <> PHI /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (execution_equiv vars) (\s1 s2. execution_equiv vars s1 s2)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  (* INVOKE: direct proof without md_adj *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule step_inst_invoke_exec_equiv >> simp[])
  >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (irule step_inst_exec_equiv_term_helper >> simp[])
  >>
  (* === NON-TERMINATOR, NON-INVOKE CASE: md_adj trick === *)
  qabbrev_tac `s2_adj = md_adj s1.vs_current_bb s1.vs_inst_idx s1.vs_prev_bb s2` >>
  (SUBGOAL_THEN ``state_equiv vars s1 s2_adj`` ASSUME_TAC >- (
    gvs[state_equiv_def, Abbr `s2_adj`, md_adj_def,
        execution_equiv_def, lookup_var_def]
  )) >>
  (SUBGOAL_THEN ``result_equiv vars (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2_adj)`` ASSUME_TAC >- (
    irule (REWRITE_RULE [GSYM AND_IMP_INTRO] step_inst_result_equiv) >>
    fs[]
  )) >>
  (SUBGOAL_THEN ``step_inst fuel ctx inst s2_adj =
     map_exec_result (md_adj s1.vs_current_bb s1.vs_inst_idx s1.vs_prev_bb)
       (step_inst fuel ctx inst s2)`` ASSUME_TAC >- (
    simp[Abbr `s2_adj`] >> irule step_inst_bb_commute >> simp[]
  )) >>
  fs[] >>
  Cases_on `step_inst fuel ctx inst s2` >>
  Cases_on `step_inst fuel ctx inst s1` >>
  fs[map_exec_result_def, result_equiv_def, lift_result_def,
     state_equiv_def, execution_equiv_def, md_adj_def, lookup_var_def]
QED

(* Terminator step_inst_base OK: same current_bb from execution_equiv states.
   Key insight: OK terminators use jump_to with target from operand evaluation.
   Same instruction + same operand evaluation = same target. *)
(* eval_operand agrees under execution_equiv for non-excluded vars *)
Triviality eval_operand_exec_equiv_match[local]:
  !vars op s1 s2.
    execution_equiv vars s1 s2 /\
    (!x. MEM (Var x) [op] ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >>
  fs[execution_equiv_def, lookup_var_def]
QED

(* Per-opcode tactic for current_bb equality: for non-OK terminators,
   step_inst_base never returns OK; for JMP/JNZ/DJMP, both results use
   jump_to with the same target label. *)
val term_ok_cb_tac =
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ s1 = OK _` mp_tac >>
  qpat_x_assum `step_inst_base _ s2 = OK _` mp_tac >>
  simp[step_inst_base_def, LET_THM] >>
  EVERY_CASE_TAC >> simp[jump_to_def,
    venom_state_accfupds, combinTheory.K_THM] >>
  rpt strip_tac >> gvs[];

Triviality term_ok_cb_JMP[local]:
  !inst s1 s2 s1' s2' vars.
    step_inst_base inst s1 = OK s1' /\ step_inst_base inst s2 = OK s2' /\
    inst.inst_opcode = JMP ==> s1'.vs_current_bb = s2'.vs_current_bb
Proof term_ok_cb_tac
QED

(* For JNZ/DJMP: establish eval_operand agreement, then expand *)
val term_ok_cb_eval_tac =
  rpt gen_tac >> strip_tac >> gvs[] >>
  (* Establish eval agreement for all operands *)
  (SUBGOAL_THEN ``!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2`` ASSUME_TAC >- (
    rpt strip_tac >> Cases_on `op` >>
    simp[eval_operand_def] >>
    fs[execution_equiv_def, lookup_var_def] >>
    first_x_assum irule >> res_tac
  )) >>
  qpat_x_assum `step_inst_base _ s1 = OK _` mp_tac >>
  qpat_x_assum `step_inst_base _ s2 = OK _` mp_tac >>
  simp[step_inst_base_def, LET_THM] >>
  EVERY_CASE_TAC >> simp[jump_to_def,
    venom_state_accfupds, combinTheory.K_THM] >>
  rpt strip_tac >> gvs[] >>
  TRY (res_tac >> gvs[] >> NO_TAC);

Triviality term_ok_cb_JNZ[local]:
  !inst s1 s2 s1' s2' vars.
    step_inst_base inst s1 = OK s1' /\ step_inst_base inst s2 = OK s2' /\
    inst.inst_opcode = JNZ /\ execution_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    s1'.vs_current_bb = s2'.vs_current_bb
Proof term_ok_cb_eval_tac
QED

Triviality term_ok_cb_DJMP[local]:
  !inst s1 s2 s1' s2' vars.
    step_inst_base inst s1 = OK s1' /\ step_inst_base inst s2 = OK s2' /\
    inst.inst_opcode = DJMP /\ execution_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    s1'.vs_current_bb = s2'.vs_current_bb
Proof term_ok_cb_eval_tac
QED

(* Non-jump terminators never return OK from step_inst_base *)
Triviality term_ok_is_jump[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ is_terminator inst.inst_opcode ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, LET_THM] >>
  EVERY_CASE_TAC >> simp[]
QED

Triviality step_inst_base_term_ok_same_current_bb[local]:
  !inst s1 s2 s1' s2' vars.
    step_inst_base inst s1 = OK s1' /\
    step_inst_base inst s2 = OK s2' /\
    is_terminator inst.inst_opcode /\
    execution_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    s1'.vs_current_bb = s2'.vs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all term_ok_is_jump >> strip_tac
  >- (mp_tac term_ok_cb_JMP >>
      DISCH_THEN (qspecl_then [`inst`,`s1`,`s2`,`s1'`,`s2'`] mp_tac) >>
      ASM_REWRITE_TAC[])
  >- (mp_tac term_ok_cb_JNZ >>
      DISCH_THEN (qspecl_then [`inst`,`s1`,`s2`,`s1'`,`s2'`,`vars`] mp_tac) >>
      ASM_REWRITE_TAC[])
  >- (mp_tac term_ok_cb_DJMP >>
      DISCH_THEN (qspecl_then [`inst`,`s1`,`s2`,`s1'`,`s2'`,`vars`] mp_tac) >>
      ASM_REWRITE_TAC[])
QED

(* Non-terminator step_inst_base preserves current_bb.
   Same proof technique as step_inst_base_preserves_inst_idx. *)
Triviality step_inst_base_preserves_current_bb[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
QED

(* FOLDL update_var preserves current_bb *)
Triviality foldl_update_var_preserves_current_bb[local]:
  !pairs s.
    (FOLDL (\s' (out,val). update_var out val s') s pairs).vs_current_bb
    = s.vs_current_bb
Proof
  Induct >> simp[FOLDL] >> Cases >> simp[FOLDL] >>
  simp[update_var_def, venom_state_accfupds, combinTheory.K_THM]
QED

(* step_inst preserves current_bb for non-terminators
   (handles both INVOKE and non-INVOKE cases) *)
Triviality step_inst_preserves_current_bb[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = INVOKE` >>
  simp[step_inst_def]
  >- (
    (* INVOKE: merge_callee_state + bind_outputs preserve current_bb *)
    strip_tac >>
    gvs[AllCaseEqs(), bind_outputs_def, merge_callee_state_def] >>
    simp[foldl_update_var_preserves_current_bb,
         venom_state_accfupds, combinTheory.K_THM]
  )
  >- metis_tac[step_inst_base_preserves_current_bb]
QED

(* Terminator OK: prev_bb = SOME input current_bb (from jump_to) *)
Triviality step_inst_base_term_ok_prev_bb[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all term_ok_is_jump >> strip_tac >>
  gvs[] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, LET_THM] >>
  EVERY_CASE_TAC >> simp[jump_to_def,
    venom_state_accfupds, combinTheory.K_THM] >>
  rpt strip_tac >> gvs[]
QED

(* Non-terminator step_inst_base preserves prev_bb *)
Triviality step_inst_base_preserves_prev_bb[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
QED

(* FOLDL update_var preserves prev_bb *)
Triviality foldl_update_var_preserves_prev_bb[local]:
  !pairs s.
    (FOLDL (\s' (out,val). update_var out val s') s pairs).vs_prev_bb
    = s.vs_prev_bb
Proof
  Induct >> simp[FOLDL] >> Cases >> simp[FOLDL] >>
  simp[update_var_def, venom_state_accfupds, combinTheory.K_THM]
QED

(* step_inst preserves prev_bb for non-terminators *)
Triviality step_inst_preserves_prev_bb[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = INVOKE` >>
  simp[step_inst_def]
  >- (
    strip_tac >>
    gvs[AllCaseEqs(), bind_outputs_def, merge_callee_state_def] >>
    simp[foldl_update_var_preserves_prev_bb,
         venom_state_accfupds, combinTheory.K_THM]
  )
  >- metis_tac[step_inst_base_preserves_prev_bb]
QED

(* Helper for induction — carries the measure n explicitly.
   Strengthened: OK case gives execution_equiv, current_bb eq, and prev_bb info. *)
Triviality run_block_suffix_exec_equiv_ind:
  !n fuel ctx bb1 bb2 vars s1 s2 k.
    n = LENGTH bb2.bb_instructions - s2.vs_inst_idx /\
    bb2.bb_instructions = DROP k bb1.bb_instructions /\
    execution_equiv vars s1 s2 /\
    s1.vs_inst_idx = k + s2.vs_inst_idx /\
    k <= LENGTH bb1.bb_instructions /\
    bb_well_formed bb1 /\
    bb_well_formed bb2 /\
    EVERY (\i. i.inst_opcode <> PHI) bb2.bb_instructions /\
    EVERY (\i. !x. MEM (Var x) i.inst_operands ==> x NOTIN vars)
      bb2.bb_instructions ==>
    lift_result (\s1 s2. execution_equiv vars s1 s2 /\
                         s1.vs_current_bb = s2.vs_current_bb)
      (\s1 s2. execution_equiv vars s1 s2)
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  Induct_on `n` >> rpt strip_tac
  >- (
    (* Base: n = 0, so s2.vs_inst_idx >= LENGTH bb2 *)
    (SUBGOAL_THEN ``~(s2.vs_inst_idx < LENGTH bb2.bb_instructions)``
      ASSUME_TAC >- decide_tac) >>
    (SUBGOAL_THEN ``~(s1.vs_inst_idx < LENGTH bb1.bb_instructions)``
      ASSUME_TAC >- (gvs[LENGTH_DROP] >> decide_tac)) >>
    ONCE_REWRITE_TAC [run_block_def] >>
    simp[get_instruction_def, lift_result_def]
  ) >>
  (* Step case: SUC n, so s2.vs_inst_idx < LENGTH bb2 *)
  (SUBGOAL_THEN ``s2.vs_inst_idx < LENGTH bb2.bb_instructions``
    ASSUME_TAC >- decide_tac) >>
  (SUBGOAL_THEN ``s1.vs_inst_idx < LENGTH bb1.bb_instructions``
    ASSUME_TAC >- (gvs[LENGTH_DROP] >> decide_tac)) >>
  (* Same instruction via EL_DROP *)
  (SUBGOAL_THEN ``EL s1.vs_inst_idx bb1.bb_instructions =
                   EL s2.vs_inst_idx bb2.bb_instructions``
    ASSUME_TAC >- (
    gvs[EL_DROP, LENGTH_DROP]
  )) >>
  qabbrev_tac `inst = EL s2.vs_inst_idx bb2.bb_instructions` >>
  (* inst properties from EVERY *)
  (SUBGOAL_THEN ``inst.inst_opcode <> PHI /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)`` ASSUME_TAC >- (
    qunabbrev_tac `inst` >> rpt conj_tac
    >- (qpat_x_assum `EVERY (\i. i.inst_opcode <> PHI) _` mp_tac >>
        simp[EVERY_EL] >> disch_then (qspec_then `s2.vs_inst_idx` mp_tac) >> simp[])
    >- (qpat_x_assum `EVERY (\i. !x. MEM (Var x) _ ==> _) _` mp_tac >>
        simp[EVERY_EL] >> disch_then (qspec_then `s2.vs_inst_idx` mp_tac) >> simp[])
  )) >>
  (* step_inst_exec_equiv *)
  (SUBGOAL_THEN ``lift_result (execution_equiv vars)
      (\s1 s2. execution_equiv vars s1 s2)
      (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)``
    ASSUME_TAC >- (
    irule step_inst_exec_equiv >> simp[]
  )) >>
  (* Unfold run_block *)
  ONCE_REWRITE_TAC [run_block_def] >>
  ASM_REWRITE_TAC[get_instruction_def] >>
  simp[] >>
  (* Fold RHS to use inst (bb2 was substituted to DROP k bb1) *)
  qpat_assum `bb2.bb_instructions = DROP k bb1.bb_instructions` (fn eq =>
    qpat_assum `Abbrev (inst = _)` (fn ab =>
      REWRITE_TAC[GSYM (REWRITE_RULE [markerTheory.Abbrev_def, eq] ab)])) >>
  (* Case split on step_inst results *)
  Cases_on `step_inst fuel ctx inst s2` >>
  Cases_on `step_inst fuel ctx inst s1` >>
  qpat_x_assum `Abbrev (inst = _)` (fn ab =>
    gvs[lift_result_def] >> assume_tac ab)
  >>
    IF_CASES_TAC >> simp[]
  >- (
    (* Terminator: halted agreement from execution_equiv *)
    (SUBGOAL_THEN ``(v':venom_state).vs_halted <=> v.vs_halted``
      (fn th => REWRITE_TAC [th]) >- (
      qpat_x_assum `execution_equiv _ v' v` mp_tac >>
      simp[execution_equiv_def]
    )) >>
    IF_CASES_TAC >> REWRITE_TAC[lift_result_def] >> BETA_TAC
    >- (* halted — Halt case, just execution_equiv *)
      first_assum ACCEPT_TAC
    >>
    (* NOT halted — OK case: need execution_equiv AND current_bb equality *)
    conj_tac >- first_assum ACCEPT_TAC >>
    (* current_bb: terminator is NOT INVOKE (is_terminator INVOKE = F) *)
    `bb1.bb_instructions❲k + s2.vs_inst_idx❳.inst_opcode <> INVOKE` by
      (strip_tac >> gvs[EVAL ``is_terminator INVOKE``]) >>
    metis_tac[step_inst_base_term_ok_same_current_bb, step_inst_non_invoke]
  )
  >- (
    (* Non-terminator: IH needs execution_equiv (have it), no current_bb needed *)
    qpat_x_assum `!fuel ctx bb1 bb2 vars s1 s2 k. _` irule >>
    simp[] >>
    conj_tac >- (qexists_tac `k` >> decide_tac) >>
    qpat_x_assum `execution_equiv _ v' v` mp_tac >>
    simp[execution_equiv_def, lookup_var_def]
  )
QED

(* The exported theorem, derived from the induction helper *)
Triviality run_block_suffix_exec_equiv_gen:
  !fuel ctx bb1 bb2 vars s1 s2 k.
    bb2.bb_instructions = DROP k bb1.bb_instructions /\
    execution_equiv vars s1 s2 /\
    s1.vs_inst_idx = k + s2.vs_inst_idx /\
    k <= LENGTH bb1.bb_instructions /\
    bb_well_formed bb1 /\
    bb_well_formed bb2 /\
    EVERY (\i. i.inst_opcode <> PHI) bb2.bb_instructions /\
    EVERY (\i. !x. MEM (Var x) i.inst_operands ==> x NOTIN vars)
      bb2.bb_instructions ==>
    lift_result (\s1 s2. execution_equiv vars s1 s2 /\
                         s1.vs_current_bb = s2.vs_current_bb)
      (\s1 s2. execution_equiv vars s1 s2)
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >> irule run_block_suffix_exec_equiv_ind >> simp[]
QED

Theorem run_block_suffix_exec_equiv:
  !fuel ctx bb1 bb2 vars s1 s2 k.
    bb2.bb_instructions = DROP k bb1.bb_instructions /\
    execution_equiv vars s1 s2 /\
    s1.vs_inst_idx = k /\ s2.vs_inst_idx = 0 /\
    k <= LENGTH bb1.bb_instructions /\
    bb_well_formed bb1 /\
    bb_well_formed bb2 /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb2.bb_instructions /\
    EVERY (\inst. !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)
      bb2.bb_instructions ==>
    lift_result (\s1 s2. execution_equiv vars s1 s2 /\
                         s1.vs_current_bb = s2.vs_current_bb)
      (\s1 s2. execution_equiv vars s1 s2)
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >> irule run_block_suffix_exec_equiv_gen >> simp[]
QED

val _ = export_theory();

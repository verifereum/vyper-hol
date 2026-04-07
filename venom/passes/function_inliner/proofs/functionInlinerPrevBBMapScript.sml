(*
 * Function Inliner — prev_bb independence for step_inst_base
 *
 * ML-level per-opcode proofs that step_inst_base commutes with
 * prev_bb updates (for non-PHI/INVOKE instructions).
 * Also defines exec_result_map_state.
 *)

Theory functionInlinerPrevBBMap
Ancestors
  functionInlinerCallSimHelpers
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps cfgTransform cfgTransformProps venomExecProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerCallSimHelpersTheory
     functionInlinerDefsTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory cfgTransformTheory cfgTransformPropsTheory
     venomExecPropsTheory venomInstPropsTheory

Definition exec_result_map_state_def:
  (exec_result_map_state f (OK s) = OK (f s)) /\
  (exec_result_map_state f (Error e) = Error e) /\
  (exec_result_map_state f (Halt s) = Halt (f s)) /\
  (exec_result_map_state f (Abort a s) = Abort a (f s)) /\
  (exec_result_map_state f (IntRet ws s) = IntRet ws (f s))
End

(* prev_bb commutation: all semantic helpers are transparent to prev_bb.
   We collect rewrite rules and prove the two key theorems directly. *)
val prev_bb_rws = let
  val eval_operand_prev_bb = prove(
    ``!op s p. eval_operand op (s with vs_prev_bb := p) = eval_operand op s``,
    Cases >> simp[eval_operand_def, lookup_var_def])
  val eval_operands_prev_bb = prove(
    ``!ops s p. eval_operands ops (s with vs_prev_bb := p) = eval_operands ops s``,
    Induct >> simp[eval_operands_def, eval_operand_prev_bb])
  val update_var_prev_bb = prove(
    ``!x v s p. update_var x v (s with vs_prev_bb := p) =
                (update_var x v s) with vs_prev_bb := p``,
    simp[update_var_def])
  val jump_to_prev_bb = prove(
    ``!lbl s p. jump_to lbl (s with vs_prev_bb := p) = jump_to lbl s``,
    simp[jump_to_def])
  val halt_state_prev_bb = prove(
    ``!s p. halt_state (s with vs_prev_bb := p) = (halt_state s) with vs_prev_bb := p``,
    simp[halt_state_def])
  val revert_state_prev_bb = prove(
    ``!s p. revert_state (s with vs_prev_bb := p) = (revert_state s) with vs_prev_bb := p``,
    simp[revert_state_def])
  val set_returndata_prev_bb = prove(
    ``!d s p. set_returndata d (s with vs_prev_bb := p) =
              (set_returndata d s) with vs_prev_bb := p``,
    simp[set_returndata_def])
  val write_memory_with_expansion_prev_bb = prove(
    ``!off data s p. write_memory_with_expansion off data (s with vs_prev_bb := p) =
                     (write_memory_with_expansion off data s) with vs_prev_bb := p``,
    simp[write_memory_with_expansion_def])
  val read_memory_prev_bb = prove(
    ``!off sz s p. read_memory off sz (s with vs_prev_bb := p) = read_memory off sz s``,
    simp[read_memory_def])
  val mstore_prev_bb = prove(
    ``!off v s p. mstore off v (s with vs_prev_bb := p) =
                  (mstore off v s) with vs_prev_bb := p``,
    simp[mstore_def, write_memory_with_expansion_def])
  val mstore8_prev_bb = prove(
    ``!off v s p. mstore8 off v (s with vs_prev_bb := p) =
                  (mstore8 off v s) with vs_prev_bb := p``,
    simp[mstore8_def, LET_THM])
  val sstore_prev_bb = prove(
    ``!k v s p. sstore k v (s with vs_prev_bb := p) =
                (sstore k v s) with vs_prev_bb := p``,
    simp[sstore_def])
  val tstore_prev_bb = prove(
    ``!k v s p. tstore k v (s with vs_prev_bb := p) =
                (tstore k v s) with vs_prev_bb := p``,
    simp[tstore_def])
  val mcopy_prev_bb = prove(
    ``!d src sz s p. mcopy d src sz (s with vs_prev_bb := p) =
                     (mcopy d src sz s) with vs_prev_bb := p``,
    simp[mcopy_def, write_memory_with_expansion_def, read_memory_def])
  val mload_prev_bb = prove(
    ``!off s p. mload off (s with vs_prev_bb := p) = mload off s``,
    simp[mload_def, read_memory_def])
  val sload_prev_bb = prove(
    ``!k s p. sload k (s with vs_prev_bb := p) = sload k s``,
    simp[sload_def, contract_storage_def])
  val tload_prev_bb = prove(
    ``!k s p. tload k (s with vs_prev_bb := p) = tload k s``,
    simp[tload_def, contract_transient_def])
  val next_alloca_offset_prev_bb = prove(
    ``!s p. next_alloca_offset (s with vs_prev_bb := p) = next_alloca_offset s``,
    simp[next_alloca_offset_def])
  val venom_to_tx_params_prev_bb = prove(
    ``!s p. venom_to_tx_params (s with vs_prev_bb := p) = venom_to_tx_params s``,
    simp[venom_to_tx_params_def])
  val make_venom_call_state_prev_bb = prove(
    ``!s p t g v cd c is.
      make_venom_call_state (s with vs_prev_bb := p) t g v cd c is =
      make_venom_call_state s t g v cd c is``,
    simp[make_venom_call_state_def, venom_to_tx_params_def])
  val make_venom_delegatecall_state_prev_bb = prove(
    ``!s p t g cd c is.
      make_venom_delegatecall_state (s with vs_prev_bb := p) t g cd c is =
      make_venom_delegatecall_state s t g cd c is``,
    simp[make_venom_delegatecall_state_def, venom_to_tx_params_def])
  val make_venom_create_state_prev_bb = prove(
    ``!s p new_addr gas value init_code.
      make_venom_create_state (s with vs_prev_bb := p) new_addr gas value init_code =
      make_venom_create_state s new_addr gas value init_code``,
    simp[make_venom_create_state_def, venom_to_tx_params_def,
         make_rollback_def, LET_THM])
  val extract_venom_result_prev_bb = prove(
    ``!s flag off sz r p.
      extract_venom_result (s with vs_prev_bb := p) flag off sz r =
      OPTION_MAP (\(out,s'). (out, s' with vs_prev_bb := p))
        (extract_venom_result s flag off sz r)``,
    simp[extract_venom_result_def, write_memory_with_expansion_def] >>
    rpt gen_tac >>
    BasicProvers.EVERY_CASE_TAC >> gvs[] >>
    simp[venom_state_component_equality])
  in [eval_operand_prev_bb, eval_operands_prev_bb,
    update_var_prev_bb, jump_to_prev_bb, halt_state_prev_bb,
    revert_state_prev_bb, set_returndata_prev_bb,
    write_memory_with_expansion_prev_bb, read_memory_prev_bb,
    make_venom_call_state_prev_bb, make_venom_delegatecall_state_prev_bb,
    make_venom_create_state_prev_bb, extract_venom_result_prev_bb,
    next_alloca_offset_prev_bb, venom_to_tx_params_prev_bb,
    exec_result_map_state_def, mstore_prev_bb, mstore8_prev_bb, sstore_prev_bb,
    tstore_prev_bb, mcopy_prev_bb, mload_prev_bb, sload_prev_bb,
    tload_prev_bb] end;

val cat_defs = [exec_pure1_def, exec_pure2_def, exec_pure3_def,
  exec_read0_def, exec_read1_def, exec_write2_def,
  exec_ext_call_def, exec_delegatecall_def, exec_create_def,
  exec_alloca_def];

(* Prove both prev_bb theorems directly with Cases_on opcode.
   This is much faster than per-opcode ML loop (86 opcodes). *)
(* Per-opcode ML proof loop for step_inst_base prev_bb theorems.
   Each opcode takes ~2s; with 86 non-excluded opcodes this takes ~170s.
   Proved via ML-level prove() which is faster than Theorem/QED overhead. *)
local
  val excluded = [``PHI``, ``INVOKE``, ``JMP``, ``JNZ``, ``DJMP``];
  val map_opcodes = List.filter
    (fn t => not (List.exists (same_const t) excluded))
    (TypeBase.constructors_of ``:opcode``);
  fun prove_map op_tm = prove(
    ``!inst (s:venom_state) p. inst.inst_opcode = ^op_tm ==>
      step_inst_base inst (s with vs_prev_bb := p) =
      exec_result_map_state (\st. st with vs_prev_bb := p)
        (step_inst_base inst s)``,
    rw ([step_inst_base_def] @ cat_defs @ prev_bb_rws) >>
    BasicProvers.EVERY_CASE_TAC >>
    gvs (prev_bb_rws @ [venom_state_component_equality, update_var_def]));
  val per_op_thms = map prove_map map_opcodes;
  fun prove_jmp op_tm = prove(
    ``!inst (s:venom_state) p. inst.inst_opcode = ^op_tm ==>
      step_inst_base inst (s with vs_prev_bb := p) = step_inst_base inst s``,
    rw ([step_inst_base_def] @ cat_defs @ prev_bb_rws) >>
    BasicProvers.EVERY_CASE_TAC >> gvs[jump_to_def]);
  val jmp_thms = map prove_jmp [``JMP``, ``JNZ``, ``DJMP``];
in
  val step_inst_base_prev_bb_map = save_thm("step_inst_base_prev_bb_map",
    prove(
      ``!inst (s:venom_state) p.
        inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
        inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
        inst.inst_opcode <> DJMP ==>
        step_inst_base inst (s with vs_prev_bb := p) =
        exec_result_map_state (\st. st with vs_prev_bb := p)
          (step_inst_base inst s)``,
      rpt strip_tac >> Cases_on `inst.inst_opcode` >> gvs per_op_thms));
  val step_inst_base_prev_bb_jmp = save_thm("step_inst_base_prev_bb_jmp",
    prove(
      ``!inst (s:venom_state) p.
        (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
         inst.inst_opcode = DJMP) ==>
        step_inst_base inst (s with vs_prev_bb := p) =
          step_inst_base inst s``,
      rpt strip_tac >> gvs jmp_thms));
end;

val _ = export_theory();

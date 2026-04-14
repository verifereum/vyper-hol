(*
 * SSA Renamed Instruction Simulation
 *
 * Proves step_inst_base_renamed_sim: stepping a renamed instruction
 * (same opcode, renamed operands/outputs via sigma) on ssa_sim-related
 * states produces ssa_sim-related results.
 *
 * Uses ssaRenamedSimLib for per-opcode step_inst_base reduction.
 *)

Theory ssaRenamedSim
Ancestors
  ssaSimDefs venomExecSemantics venomInst venomState
  list rich_list finite_map pred_set
Libs
  ssaRenamedSimLib

(* ==========================================================================
   exec_* Category Helpers for renamed instructions
   
   Pattern: unfold exec helper, use eval_operand_renamed for operand
   agreement, use ssa_sim_update_var for output agreement.
   ========================================================================== *)

(* Common tactic for exec helpers that produce one output variable *)
(* After unfolding: case split, eval_operand agreement, ssa_sim_update_var *)

Triviality exec_pure1_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_pure1 f inst1 s1 = OK s1' ==>
    ?s2'. exec_pure1 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_pure1_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_pure2_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_pure2 f inst1 s1 = OK s1' ==>
    ?s2'. exec_pure2 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_pure2_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_pure3_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_pure3 f inst1 s1 = OK s1' ==>
    ?s2'. exec_pure3 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_pure3_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_read0_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    f s1 = f s2 /\
    exec_read0 f inst1 s1 = OK s1' ==>
    ?s2'. exec_read0 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_read0_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

Triviality exec_read1_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    (!v. f v s1 = f v s2) /\
    exec_read1 f inst1 s1 = OK s1' ==>
    ?s2'. exec_read1 f inst2 s2 = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_read1_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[] >>
  irule ssa_sim_update_var >> gvs[]
QED

(* exec_write2: no output variable, modifies state *)
Triviality exec_write2_renamed:
  !f inst1 inst2 sigma s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst2.inst_operands = MAP (renamed_operand sigma) inst1.inst_operands /\
    (!v1 v2. ssa_sim sigma (f v1 v2 s1) (f v1 v2 s2)) /\
    exec_write2 f inst1 s1 = OK s1' ==>
    ?s2'. exec_write2 f inst2 s2 = OK s2' /\
          ssa_sim sigma s1' s2'
Proof
  rw[exec_write2_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac eval_operand_renamed >> gvs[]
QED

(* Helper: ssa_sim implies all non-var state fields agree *)
Triviality ssa_sim_fields:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
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
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb
Proof
  rw[ssa_sim_def]
QED

(* ==========================================================================
   External call helpers
   
   Under ssa_sim, all non-var state fields are equal, so:
   - make_venom_*_state produces identical EVM states
   - extract_venom_result produces ssa_sim-related output states
   ========================================================================== *)

(* Under ssa_sim, make_venom_call_state is identical *)
Triviality make_venom_call_state_ssa_sim:
  !sigma s1 s2 target gas value calldata code is_static.
    ssa_sim sigma s1 s2 ==>
    make_venom_call_state s1 target gas value calldata code is_static =
    make_venom_call_state s2 target gas value calldata code is_static
Proof
  rw[ssa_sim_def, make_venom_call_state_def, LET_THM, venom_to_tx_params_def]
QED

Triviality make_venom_delegatecall_state_ssa_sim:
  !sigma s1 s2 target gas calldata code is_static.
    ssa_sim sigma s1 s2 ==>
    make_venom_delegatecall_state s1 target gas calldata code is_static =
    make_venom_delegatecall_state s2 target gas calldata code is_static
Proof
  rw[ssa_sim_def, make_venom_delegatecall_state_def, LET_THM,
     venom_to_tx_params_def]
QED

Triviality make_venom_create_state_ssa_sim:
  !sigma s1 s2 new_address gas value init_code.
    ssa_sim sigma s1 s2 ==>
    make_venom_create_state s1 new_address gas value init_code =
    make_venom_create_state s2 new_address gas value init_code
Proof
  rw[ssa_sim_def, make_venom_create_state_def, LET_THM,
     venom_to_tx_params_def]
QED

(* extract_venom_result preserves ssa_sim: if the run_result is the same
   and input states are ssa_sim-related, output states are too. *)
Triviality extract_venom_result_ssa_sim:
  !sigma s1 s2 output_val retOff retSize run_result output s1'.
    ssa_sim sigma s1 s2 /\
    extract_venom_result s1 output_val retOff retSize run_result =
      SOME (output, s1') ==>
    ?s2'. extract_venom_result s2 output_val retOff retSize run_result =
            SOME (output, s2') /\
          ssa_sim sigma s1' s2'
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac ssa_sim_fields >>
  simp[ssa_sim_def, lookup_var_def,
       write_memory_with_expansion_def, LET_THM] >>
  gvs[ssa_sim_def, lookup_var_def]
QED

(* exec_ext_call simulation *)
Triviality exec_ext_call_renamed:
  !sigma inst1 inst2 s1 s2 s1' gas addr_w value ao as_ ro rs is_static.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_ext_call inst1 s1 gas addr_w value ao as_ ro rs is_static = OK s1' ==>
    ?s2'. exec_ext_call inst2 s2 gas addr_w value ao as_ ro rs is_static = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_ext_call_def, LET_THM] >>
  imp_res_tac ssa_sim_fields >> gvs[read_memory_def] >>
  `make_venom_call_state s1 (w2w addr_w) (w2n gas) (w2n value)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code is_static =
   make_venom_call_state s2 (w2w addr_w) (w2n gas) (w2n value)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code is_static` by
    metis_tac[make_venom_call_state_ssa_sim] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule_all extract_venom_result_ssa_sim >> strip_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[] >>
  gvs[extract_venom_result_def, AllCaseEqs(), LET_THM, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* exec_delegatecall simulation *)
Triviality exec_delegatecall_renamed:
  !sigma inst1 inst2 s1 s2 s1' gas addr_w ao as_ ro rs.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_delegatecall inst1 s1 gas addr_w ao as_ ro rs = OK s1' ==>
    ?s2'. exec_delegatecall inst2 s2 gas addr_w ao as_ ro rs = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_delegatecall_def, LET_THM] >>
  imp_res_tac ssa_sim_fields >> gvs[read_memory_def] >>
  `make_venom_delegatecall_state s1 (w2w addr_w) (w2n gas)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code
     s2.vs_call_ctx.cc_static =
   make_venom_delegatecall_state s2 (w2w addr_w) (w2n gas)
     (TAKE (w2n as_) (DROP (w2n ao) s2.vs_memory ++ REPLICATE (w2n as_) 0w))
     (lookup_account (w2w addr_w) s2.vs_accounts).code
     s2.vs_call_ctx.cc_static` by
    metis_tac[make_venom_delegatecall_state_ssa_sim] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule_all extract_venom_result_ssa_sim >> strip_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[] >>
  gvs[extract_venom_result_def, AllCaseEqs(), LET_THM, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* exec_create simulation *)
Triviality exec_create_renamed:
  !sigma inst1 inst2 s1 s2 s1' value offset sz salt_opt.
    ssa_sim sigma s1 s2 /\
    LENGTH inst2.inst_outputs = LENGTH inst1.inst_outputs /\
    (inst1.inst_outputs <> [] ==>
     !x. ~MEM x inst1.inst_outputs /\ lookup_var x s1 <> NONE ==>
         sigma x <> HD inst2.inst_outputs) /\
    exec_create inst1 s1 value offset sz salt_opt = OK s1' ==>
    ?s2'. exec_create inst2 s2 value offset sz salt_opt = OK s2' /\
          ssa_sim ((HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma)
                  s1' s2'
Proof
  rw[exec_create_def, LET_THM] >>
  imp_res_tac ssa_sim_fields >> gvs[read_memory_def] >>
  `make_venom_create_state s1
     (case salt_opt of
        NONE => address_for_create s2.vs_call_ctx.cc_address
          (lookup_account s2.vs_call_ctx.cc_address s2.vs_accounts).nonce
      | SOME salt => address_for_create2 s2.vs_call_ctx.cc_address salt
          (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w)))
     (s2.vs_call_ctx.cc_gas - s2.vs_call_ctx.cc_gas DIV 64)
     (w2n value) (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w)) =
   make_venom_create_state s2
     (case salt_opt of
        NONE => address_for_create s2.vs_call_ctx.cc_address
          (lookup_account s2.vs_call_ctx.cc_address s2.vs_accounts).nonce
      | SOME salt => address_for_create2 s2.vs_call_ctx.cc_address salt
          (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w)))
     (s2.vs_call_ctx.cc_gas - s2.vs_call_ctx.cc_gas DIV 64)
     (w2n value) (TAKE (w2n sz) (DROP (w2n offset) s2.vs_memory ++ REPLICATE (w2n sz) 0w))` by (
    Cases_on `salt_opt` >> simp[] >>
    metis_tac[make_venom_create_state_ssa_sim]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule_all extract_venom_result_ssa_sim >> strip_tac >> gvs[] >>
  irule ssa_sim_update_var >> gvs[] >>
  gvs[extract_venom_result_def, AllCaseEqs(), LET_THM, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Under ssa_sim, vs_alloca_next is equal *)
Triviality vs_alloca_next_ssa_sim:
  !sigma s1 s2. ssa_sim sigma s1 s2 ==>
    s1.vs_alloca_next = s2.vs_alloca_next
Proof
  rw[ssa_sim_def]
QED

(* ssa_sim preserved by identical vs_allocas + vs_alloca_next update *)
Triviality ssa_sim_allocas_update:
  !sigma s1 s2 X Y.
    ssa_sim sigma s1 s2 ==>
    ssa_sim sigma (s1 with <| vs_allocas := X; vs_alloca_next := Y |>)
                  (s2 with <| vs_allocas := X; vs_alloca_next := Y |>)
Proof
  rw[ssa_sim_def, lookup_var_def]
QED

(* ==========================================================================
   Main theorem: step_inst_base_renamed_sim
   Uses STEP_BASE_REDUCE_TAC from ssaRenamedSimLib to avoid expanding
   the monolithic step_inst_base_def across many goals.
   ========================================================================== *)

Theorem step_inst_base_renamed_sim:
  !sigma inst1 inst2 s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    output_fresh sigma inst1 inst2 s1 /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> ASSIGN /\
    step_inst_base inst1 s1 = OK s1' ==>
    ?s2'. step_inst_base inst2 s2 = OK s2' /\
          ssa_sim (if opcode_has_output inst1.inst_opcode
                   then (HD inst1.inst_outputs =+ HD inst2.inst_outputs) sigma
                   else sigma)
                  s1' s2'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def, output_fresh_def] >>
  Cases_on `inst1.inst_opcode` >> gvs[is_terminator_def] >>
  gvs step_base_reduces >>
  (* Phase 1: pure opcodes — closed by drule_all + simp[opcode_has_output_def] *)
  TRY (drule_all exec_pure2_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_pure1_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_pure3_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  (* Phase 2: remaining goals — get field equalities, unfold defs *)
  imp_res_tac ssa_sim_fields >>
  imp_res_tac vs_alloca_next_ssa_sim >>
  gvs[exec_read0_def, exec_read1_def, exec_write2_def,
      exec_alloca_def, LET_THM, AllCaseEqs(), renamed_operand_def] >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[]) >>
  TRY (imp_res_tac eval_operands_renamed >> gvs[]) >>
  (* Phase 3: ext calls — drule_all + simp[opcode_has_output_def] *)
  TRY (drule_all exec_ext_call_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_delegatecall_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  TRY (drule_all exec_create_renamed >>
       simp[opcode_has_output_def] >> NO_TAC) >>
  (* Phase 4: resolve conclusion-side case expressions *)
  gvs[EL_MAP, GSYM MAP_DROP] >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* Phase 5a: destructure inst2.inst_outputs where LENGTH is concrete *)
  TRY (
    `?h. inst2.inst_outputs = [h]` by
      (Cases_on `inst2.inst_outputs` >> gvs[] >>
       Cases_on `t` >> gvs[]) >>
    gvs[]) >>
  (* Phase 5b: destructure inst1.inst_outputs similarly *)
  TRY (
    `?h1. inst1.inst_outputs = [h1]` by
      (Cases_on `inst1.inst_outputs` >> gvs[] >>
       Cases_on `t` >> gvs[]) >>
    gvs[]) >>
  (* Resolve opcode_has_output for remaining opcodes *)
  gvs[opcode_has_output_def] >>
  (* Phase 6a: ALLOCA — needs combined allocas + var update *)
  TRY (irule ssa_sim_update_var >> gvs[lookup_var_def] >>
       irule ssa_sim_allocas_update >> gvs[] >> NO_TAC) >>
  (* Phase 6b: output-producing opcodes *)
  TRY (gvs[mload_def, sload_def, tload_def, contract_storage_def,
           contract_transient_def] >>
       irule ssa_sim_update_var >> gvs[lookup_var_def] >> NO_TAC) >>
  (* Phase 7: LOG needs Cases_on rest to simplify HD (MAP f rest) *)
  TRY (Cases_on `rest` >> gvs[]) >>
  (* Phase 8: state-modifying / trivial — sigma unchanged (opcode_has_output = F) *)
  gvs[mcopy_def, write_memory_with_expansion_def,
      mload_def, mstore_def, mstore8_def, sload_def, sstore_def, tload_def, tstore_def,
      contract_storage_def, contract_transient_def,
      ssa_sim_def, update_var_def, lookup_var_def]
QED

(* ==========================================================================
   Terminator simulation: step_terminator_ssa_sim
   
   Like step_inst_base_renamed_sim but for terminators. Returns
   ssa_result_equiv since terminators produce mixed result types
   (OK for jumps, Halt for stop/return, Abort for revert, IntRet for ret).
   
   Assumes original doesn't error (all operands defined). Error case is
   handled separately at the run_block level.
   ========================================================================== *)

(* extract_labels is invariant under MAP (renamed_operand sigma) *)
Triviality extract_labels_renamed:
  !ops sigma.
    extract_labels (MAP (renamed_operand sigma) ops) = extract_labels ops
Proof
  Induct >> rw[extract_labels_def, renamed_operand_def, MAP] >>
  Cases_on `h` >> rw[renamed_operand_def, extract_labels_def]
QED

(* Common setup for terminator simulation: strip, expand inst_renamed,
   get ssa_sim field equalities, reduce step_inst_base per opcode. *)
val term_setup_tac =
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def] >>
  imp_res_tac ssa_sim_fields;

(* After setup + step_base_reduces for a specific opcode:
   1. Split inst1.inst_operands (determines BOTH sides since MAP preserves structure)
   2. gvs to simplify renamed_operand + eliminate Error branches
   3. Split eval_operand results, bridge with eval_operand_renamed
   4. Close remaining goals *)
(* resolve_cases_tac: like every_case_tac but lighter.
   Splits conclusion-side case expressions only (via TOP_CASE_TAC),
   then uses gvs to simplify and eliminate Error/contradiction branches.
   The ssa_result_equiv_def + renamed_operand_def in gvs ensure that after
   both sides resolve to constructors, the result matches. *)
val term_resolve_tac =
  gvs[renamed_operand_def, extract_labels_renamed] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[ssa_result_equiv_def, renamed_operand_def, extract_labels_renamed,
           execution_equiv_UNIV, halt_state_def, set_returndata_def,
           revert_state_def]) >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[]) >>
  TRY (imp_res_tac eval_operands_renamed >> gvs[execution_equiv_UNIV]) >>
  TRY (qexists_tac `sigma` >> irule jump_to_ssa_sim >> simp[]) >>
  gvs[ssa_result_equiv_def, execution_equiv_UNIV, halt_state_def,
      set_returndata_def, revert_state_def];

(* Split into per-terminator trivialities to avoid every_case_tac on 7+ goals *)
Triviality step_term_jmp:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = JMP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_jnz:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = JNZ /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_djmp:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = DJMP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_ret:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = RET /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_return:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = RETURN /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_revert:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = REVERT /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_selfdestruct:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = SELFDESTRUCT /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_stop:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = STOP /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_sink:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = SINK /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

Triviality step_term_invalid:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\ inst_renamed sigma inst1 inst2 /\
    inst1.inst_opcode = INVALID /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  term_setup_tac >> gvs step_base_reduces >> term_resolve_tac
QED

val step_term_lemmas = [step_term_jmp, step_term_jnz, step_term_djmp,
  step_term_ret, step_term_return, step_term_revert, step_term_selfdestruct,
  step_term_stop, step_term_sink, step_term_invalid];

Theorem step_terminator_ssa_sim:
  !sigma inst1 inst2 s1 s2.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    (!e. step_inst_base inst1 s1 <> Error e) ==>
    ssa_result_equiv (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst1.inst_opcode` >> gvs[is_terminator_def] >>
  metis_tac step_term_lemmas
QED

(* For terminators returning OK, the input sigma is preserved.
   Only JMP/JNZ/DJMP return OK (via jump_to); all others return
   Halt/Abort/IntRet/Error. jump_to_ssa_sim preserves sigma. *)
Theorem step_terminator_ok_preserves_sim:
  !sigma inst1 inst2 s1 s2 v v'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    step_inst_base inst1 s1 = OK v /\
    step_inst_base inst2 s2 = OK v' ==>
    ssa_sim sigma v v'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def] >>
  imp_res_tac ssa_sim_fields >>
  Cases_on `inst1.inst_opcode` >> gvs[is_terminator_def] >>
  gvs step_base_reduces >>
  gvs[renamed_operand_def, extract_labels_renamed, AllCaseEqs()] >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[AllCaseEqs()]) >>
  TRY (irule jump_to_ssa_sim >> simp[])
QED

(* For non-terminator, non-INVOKE: if step_inst_base aborts on side 1,
   the renamed instruction also aborts with same reason + execution_equiv.
   Only ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY can abort among
   non-terminators — all depend on operand values (same by ssa_sim). *)
Theorem step_base_abort_sim:
  !sigma inst1 inst2 s1 s2 a s1'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    step_inst_base inst1 s1 = Abort a s1' ==>
    ?s2'. step_inst_base inst2 s2 = Abort a s2' /\
          execution_equiv UNIV s1' s2'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[inst_renamed_def] >>
  imp_res_tac ssa_sim_fields >>
  Cases_on `inst1.inst_opcode` >> gvs[is_terminator_def] >>
  gvs step_base_reduces >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_alloca_def, exec_ext_call_def, exec_delegatecall_def,
      exec_create_def, extract_venom_result_def,
      AllCaseEqs(), LET_THM, renamed_operand_def] >>
  TRY (imp_res_tac eval_operand_renamed >> gvs[]) >>
  TRY (imp_res_tac eval_operands_renamed >> gvs[]) >>
  irule ssa_sim_implies_exec_equiv_UNIV >>
  gvs[ssa_sim_def, halt_state_def, revert_state_def, set_returndata_def,
      lookup_var_def] >>
  metis_tac[]
QED

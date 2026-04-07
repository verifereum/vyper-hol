(*
 * Function Inliner — Callee Clone Simulation
 *
 * Proves that vs_params is irrelevant for non-PARAM opcodes,
 * enabling clone simulation without vs_params match.
 *)

Theory functionInlinerCalleeSim
Ancestors
  functionInlinerInline functionInlinerStepClone
  functionInlinerCloneSim functionInlinerSim
  functionInlinerDefs
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  cfgTransform

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory

open functionInlinerDefsTheory functionInlinerInlineTheory
     functionInlinerCloneSimTheory functionInlinerSimTheory
     functionInlinerStepCloneTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     cfgTransformTheory

(* ================================================================
   Section 1: vs_params commutation lemmas
   ================================================================ *)

Theorem eval_operand_params_irrel[simp]:
  !op (s:venom_state) p.
    eval_operand op (s with vs_params := p) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_params_irrel[simp]:
  !ops (s:venom_state) p.
    eval_operands ops (s with vs_params := p) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def]
QED

Theorem update_var_params_comm[simp]:
  !x v (s:venom_state) p.
    update_var x v (s with vs_params := p) =
    (update_var x v s) with vs_params := p
Proof
  simp[update_var_def, venomStateTheory.venom_state_component_equality]
QED

Theorem jump_to_params_comm[simp]:
  !lbl (s:venom_state) p.
    jump_to lbl (s with vs_params := p) =
    (jump_to lbl s) with vs_params := p
Proof
  simp[jump_to_def, venomStateTheory.venom_state_component_equality]
QED

Theorem halt_state_params_comm[simp]:
  !(s:venom_state) p.
    halt_state (s with vs_params := p) =
    (halt_state s) with vs_params := p
Proof
  simp[halt_state_def, venomStateTheory.venom_state_component_equality]
QED

Theorem revert_state_params_comm[simp]:
  !(s:venom_state) p.
    revert_state (s with vs_params := p) =
    (revert_state s) with vs_params := p
Proof
  simp[revert_state_def, venomStateTheory.venom_state_component_equality]
QED

Theorem set_returndata_params_comm[simp]:
  !rd (s:venom_state) p.
    set_returndata rd (s with vs_params := p) =
    (set_returndata rd s) with vs_params := p
Proof
  simp[set_returndata_def, venomStateTheory.venom_state_component_equality]
QED

Theorem write_memory_with_expansion_params_comm[simp]:
  !off bytes (s:venom_state) p.
    write_memory_with_expansion off bytes (s with vs_params := p) =
    (write_memory_with_expansion off bytes s) with vs_params := p
Proof
  simp[write_memory_with_expansion_def,
       venomStateTheory.venom_state_component_equality]
QED

(* State-reading functions are unaffected by vs_params *)
Theorem mload_params_irrel[simp]:
  !off (s:venom_state) p. mload off (s with vs_params := p) = mload off s
Proof
  simp[mload_def]
QED

Theorem sload_params_irrel[simp]:
  !key (s:venom_state) p. sload key (s with vs_params := p) = sload key s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem tload_params_irrel[simp]:
  !key (s:venom_state) p. tload key (s with vs_params := p) = tload key s
Proof
  simp[tload_def, contract_transient_def]
QED

Theorem read_memory_params_irrel[simp]:
  !off sz (s:venom_state) p.
    read_memory off sz (s with vs_params := p) = read_memory off sz s
Proof
  simp[read_memory_def]
QED

Theorem contract_storage_params_irrel[simp]:
  !(s:venom_state) p.
    contract_storage (s with vs_params := p) = contract_storage s
Proof
  simp[contract_storage_def]
QED

Theorem contract_transient_params_irrel[simp]:
  !(s:venom_state) p.
    contract_transient (s with vs_params := p) = contract_transient s
Proof
  simp[contract_transient_def]
QED

(* External call state construction: doesn't read vs_params at all *)
Theorem make_venom_call_state_params_irrel[simp]:
  !(s:venom_state) p tgt gas val cd code stat.
    make_venom_call_state (s with vs_params := p) tgt gas val cd code stat =
    make_venom_call_state s tgt gas val cd code stat
Proof
  simp[make_venom_call_state_def, venom_to_tx_params_def]
QED

Theorem make_venom_delegatecall_state_params_irrel[simp]:
  !(s:venom_state) p tgt gas cd code stat.
    make_venom_delegatecall_state (s with vs_params := p) tgt gas cd code stat =
    make_venom_delegatecall_state s tgt gas cd code stat
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def]
QED

Theorem make_venom_create_state_params_irrel[simp]:
  !(s:venom_state) p addr gas value init_code.
    make_venom_create_state (s with vs_params := p) addr gas value init_code =
    make_venom_create_state s addr gas value init_code
Proof
  simp[make_venom_create_state_def, venom_to_tx_params_def]
QED

(* extract_venom_result: commutes with vs_params *)
Theorem extract_venom_result_params_comm[simp]:
  !(s:venom_state) p oval roff rsz rr.
    extract_venom_result (s with vs_params := p) oval roff rsz rr =
    OPTION_MAP (\(v,s'). (v, s' with vs_params := p))
      (extract_venom_result s oval roff rsz rr)
Proof
  rpt gen_tac >>
  simp[extract_venom_result_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[venomStateTheory.venom_state_component_equality]
QED

(* ================================================================
   Section 2: step_inst_base params irrelevance (the main lemma)

   For non-PARAM opcodes, step_inst_base doesn't read vs_params.
   Proved by case split on opcode with FULL unfolding of all
   venomState helpers so the simplifier sees raw record accesses.
   ================================================================ *)

(* State functions that return venom_state: commute with vs_params *)
Theorem mstore_params_comm[simp]:
  !off v (s:venom_state) p.
    mstore off v (s with vs_params := p) =
    (mstore off v s) with vs_params := p
Proof
  simp[mstore_def, write_memory_with_expansion_def,
       venomStateTheory.venom_state_component_equality]
QED

Theorem mstore8_params_comm[simp]:
  !off v (s:venom_state) p.
    mstore8 off v (s with vs_params := p) =
    (mstore8 off v s) with vs_params := p
Proof
  simp[mstore8_def, LET_THM,
       venomStateTheory.venom_state_component_equality]
QED

Theorem sstore_params_comm[simp]:
  !key v (s:venom_state) p.
    sstore key v (s with vs_params := p) =
    (sstore key v s) with vs_params := p
Proof
  simp[sstore_def, contract_storage_def,
       venomStateTheory.venom_state_component_equality]
QED

Theorem tstore_params_comm[simp]:
  !key v (s:venom_state) p.
    tstore key v (s with vs_params := p) =
    (tstore key v s) with vs_params := p
Proof
  simp[tstore_def, contract_transient_def,
       venomStateTheory.venom_state_component_equality]
QED

Theorem mcopy_params_comm[simp]:
  !dst src sz (s:venom_state) p.
    mcopy dst src sz (s with vs_params := p) =
    (mcopy dst src sz s) with vs_params := p
Proof
  simp[mcopy_def, write_memory_with_expansion_def, read_memory_def,
       venomStateTheory.venom_state_component_equality]
QED

(* Non-state-returning functions: irrel *)
Theorem lookup_account_params_irrel[simp]:
  !addr (s:venom_state) p.
    lookup_account addr (s with vs_params := p).vs_accounts =
    lookup_account addr s.vs_accounts
Proof
  simp[]
QED

Theorem account_empty_params_irrel[simp]:
  !addr (s:venom_state) p.
    account_empty (lookup_account addr (s with vs_params := p).vs_accounts) =
    account_empty (lookup_account addr s.vs_accounts)
Proof
  simp[]
QED

val rec_eq = venomStateTheory.venom_state_component_equality;

(* ================================================================
   Section 2: External-call-level params commutation
   All three exec_ext_call / exec_delegatecall / exec_create share
   the same tail pattern: extract_venom_result → case inst_outputs.
   We prove each commutes with vs_params, avoiding the need to unfold
   extract_venom_result_def inside step_inst_base_params_irrel.
   ================================================================ *)

(* Helper tactic for the shared tail of exec_ext_call/delegatecall/create *)
val ext_call_params_tac =
  rpt gen_tac >>
  simp[] >>  (* unfold the exec_* def via included def thm *)
  Cases_on `extract_venom_result s oval roff rsz (run evm_s)` >>
  simp[] >>
  rename1 `SOME result` >> PairCases_on `result` >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[rec_eq];

(* Shared tactic for exec_*_params_comm proofs:
   After simp unfolds the exec def and commutes params through
   make_venom_*_state and read_memory, we have:
     LHS: ... OPTION_MAP (\(v,s'). (v, s' with vs_params := p))
                         (extract_venom_result s ...) ...
     RHS: ... extract_venom_result s ... ...
   Case-split on the shared extract_venom_result, then handle
   inst_outputs with EVERY_CASE_TAC. *)
val exec_params_comm_tac =
  rpt gen_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac
    `OPTION_MAP _ (extract_venom_result s oval roff rsz rr)` >>
  Cases_on `extract_venom_result s oval roff rsz rr` >>
  simp[Abbr`oval`, Abbr`roff`, Abbr`rsz`, Abbr`rr`] >>
  rename1 `SOME result` >> PairCases_on `result` >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[rec_eq];

Theorem exec_ext_call_params_comm[local]:
  !inst (s:venom_state) p gas addr_w value argsOff argsSize retOff retSize
   is_static.
    exec_ext_call inst (s with vs_params := p) gas addr_w value argsOff
      argsSize retOff retSize is_static =
    case exec_ext_call inst s gas addr_w value argsOff argsSize retOff
      retSize is_static of
      OK s1 => OK (s1 with vs_params := p)
    | Halt s2 => Halt (s2 with vs_params := p)
    | Abort a s3 => Abort a (s3 with vs_params := p)
    | IntRet v s4 => IntRet v (s4 with vs_params := p)
    | Error e => Error e
Proof
  simp[exec_ext_call_def] >> exec_params_comm_tac
QED

Theorem exec_delegatecall_params_comm[local]:
  !inst (s:venom_state) p gas addr_w argsOff argsSize retOff retSize.
    exec_delegatecall inst (s with vs_params := p) gas addr_w argsOff
      argsSize retOff retSize =
    case exec_delegatecall inst s gas addr_w argsOff argsSize retOff
      retSize of
      OK s1 => OK (s1 with vs_params := p)
    | Halt s2 => Halt (s2 with vs_params := p)
    | Abort a s3 => Abort a (s3 with vs_params := p)
    | IntRet v s4 => IntRet v (s4 with vs_params := p)
    | Error e => Error e
Proof
  simp[exec_delegatecall_def] >> exec_params_comm_tac
QED

Theorem exec_create_params_comm[local]:
  !inst (s:venom_state) p value offset sz salt_opt.
    exec_create inst (s with vs_params := p) value offset sz salt_opt =
    case exec_create inst s value offset sz salt_opt of
      OK s1 => OK (s1 with vs_params := p)
    | Halt s2 => Halt (s2 with vs_params := p)
    | Abort a s3 => Abort a (s3 with vs_params := p)
    | IntRet v s4 => IntRet v (s4 with vs_params := p)
    | Error e => Error e
Proof
  simp[exec_create_def] >> exec_params_comm_tac
QED

Theorem step_inst_base_params_irrel:
  !inst (s:venom_state) p.
    inst.inst_opcode <> PARAM /\ inst.inst_opcode <> ALLOCA ==>
    step_inst_base inst (s with vs_params := p) =
    case step_inst_base inst s of
      OK s1 => OK (s1 with vs_params := p)
    | Halt s2 => Halt (s2 with vs_params := p)
    | Abort a s3 => Abort a (s3 with vs_params := p)
    | IntRet v s4 => IntRet v (s4 with vs_params := p)
    | Error e => Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[step_inst_base_def,
      exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_ext_call_params_comm, exec_delegatecall_params_comm,
      exec_create_params_comm] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[rec_eq, halt_state_def, revert_state_def]
QED

(* Lift to step_inst for non-INVOKE, non-PARAM *)
Theorem step_inst_params_irrel:
  !fuel ctx inst (s:venom_state) p.
    inst.inst_opcode <> PARAM /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA ==>
    step_inst fuel ctx inst (s with vs_params := p) =
    case step_inst fuel ctx inst s of
      OK s1 => OK (s1 with vs_params := p)
    | Halt s2 => Halt (s2 with vs_params := p)
    | Abort a s3 => Abort a (s3 with vs_params := p)
    | IntRet v s4 => IntRet v (s4 with vs_params := p)
    | Error e => Error e
Proof
  rpt strip_tac >>
  simp[step_inst_def, step_inst_base_params_irrel]
QED

(* ================================================================
   Section 3: clone_rel_np — clone relation without vs_params match
   
   Callee has vs_params = invoke_args (from setup_callee).
   Clone operates in caller context with vs_params = caller_params.
   Since PARAM is replaced by ASSIGN in clone blocks, vs_params
   is never read, so the difference doesn't matter.
   ================================================================ *)

Definition shared_globals_np_def:
  shared_globals_np (s1:venom_state) (s2:venom_state) <=>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_code = s2.vs_code /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_prev_hashes = s2.vs_prev_hashes
End

(* clone_rel_np: FDOM-restricted variant of clone_rel without vs_params match.
   Only requires variable correspondence for vars in FDOM of callee.
   This is crucial for loop re-entry where s_clone may have stale prefix vars
   from a previous iteration — with FEMPTY callee, FDOM = {} makes this vacuous. *)
Definition clone_rel_np_def:
  clone_rel_np prefix labels (s_callee:venom_state) (s_clone:venom_state) <=>
    (!v. v IN FDOM s_callee.vs_vars ==>
         FLOOKUP s_clone.vs_vars (STRCAT prefix v) =
         FLOOKUP s_callee.vs_vars v) /\
    (s_clone.vs_current_bb = STRCAT prefix s_callee.vs_current_bb) /\
    (s_clone.vs_prev_bb = OPTION_MAP (STRCAT prefix) s_callee.vs_prev_bb) /\
    (s_clone.vs_inst_idx = s_callee.vs_inst_idx) /\
    (s_clone.vs_halted <=> s_callee.vs_halted) /\
    FDOM s_callee.vs_labels = {} /\
    FDOM s_clone.vs_labels = {} /\
    shared_globals_np s_callee s_clone
End

Theorem shared_globals_implies_np:
  !s1 s2. shared_globals s1 s2 ==> shared_globals_np s1 s2
Proof
  simp[shared_globals_def, shared_globals_np_def]
QED

(* clone_rel (unrestricted ∀v) trivially implies FDOM-restricted clone_rel_np *)
Theorem clone_rel_implies_np:
  !p l s1 s2. clone_rel p l s1 s2 ==> clone_rel_np p l s1 s2
Proof
  simp[clone_rel_def, clone_rel_np_def] >> metis_tac[shared_globals_implies_np]
QED

Theorem shared_globals_params_adj_np:
  !s_adj s_clone s_orig pv.
    shared_globals s_adj s_clone /\
    s_adj = s_orig with vs_params := pv ==>
    shared_globals_np s_orig s_clone
Proof
  simp[shared_globals_def, shared_globals_np_def, rec_eq]
QED

(* Conditional eval_operand: if callee eval succeeds, clone eval gives same result.
   Key insight: SOME val for Var v implies v IN FDOM, so FDOM-restricted matches. *)
Theorem eval_operand_clone_np_some:
  !prefix labels op s_callee s_clone val.
    clone_rel_np prefix labels s_callee s_clone /\
    eval_operand op s_callee = SOME val ==>
    eval_operand (clone_operand prefix labels op) s_clone = SOME val
Proof
  Cases_on `op` >>
  simp[eval_operand_def, clone_operand_def, lookup_var_def,
       clone_rel_np_def] >>
  rpt strip_tac
  >- (
    (* Var case: FLOOKUP ... = SOME val => s IN FDOM => FLOOKUP match *)
    `s IN FDOM s_callee.vs_vars` by
      (fs[FLOOKUP_DEF]) >>
    res_tac >> fs[]
  )
  >>
  (* Label case: FDOM vs_labels = {} => FLOOKUP = NONE => contradiction *)
  qpat_x_assum `FLOOKUP _ _ = SOME _` mp_tac >>
  simp[FLOOKUP_DEF, pred_setTheory.NOT_IN_EMPTY]
QED

(* Conditional eval_operands: if callee evals all succeed, clone evals give same. *)
Theorem eval_operands_clone_np_some:
  !prefix labels ops s_callee s_clone vals.
    clone_rel_np prefix labels s_callee s_clone /\
    eval_operands ops s_callee = SOME vals ==>
    eval_operands (MAP (clone_operand prefix labels) ops) s_clone = SOME vals
Proof
  Induct_on `ops` >>
  simp[eval_operands_def, MAP] >>
  rpt strip_tac >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `eval_operands ops s_callee` >> gvs[] >>
  res_tac >> simp[]
QED

(* step_inst_base_clone_np: DIRECT proof via conditional eval.
   Per-opcode-category: each exec_* helper dispatches to conditional eval
   + shared_globals_np + update_var preservation. No bridge through clone_rel. *)

(* Helper: STRCAT prefix is injective *)
Theorem STRCAT_RIGHT_CANCEL:
  !p (a:string) b. STRCAT p a = STRCAT p b ==> a = b
Proof
  Induct >> simp[]
QED

(* update_var preserves FDOM-restricted clone_rel_np.
   After update_var v val on callee and p++v val on clone,
   FDOM grows by {v} on callee side. For the new var, both have SOME val.
   For existing vars in FDOM, FLOOKUP unchanged. *)
Theorem update_var_clone_rel_np:
  !prefix labels s_c s_cl v val.
    clone_rel_np prefix labels s_c s_cl ==>
    clone_rel_np prefix labels
      (update_var v val s_c)
      (update_var (STRCAT prefix v) val s_cl)
Proof
  simp[clone_rel_np_def, update_var_def, shared_globals_np_def, rec_eq,
       FLOOKUP_UPDATE, FDOM_FUPDATE] >>
  rpt strip_tac >> Cases_on `v' = v` >> simp[] >>
  res_tac >> simp[] >>
  imp_res_tac STRCAT_RIGHT_CANCEL >> gvs[]
QED

(* update_var preserves shared_globals_np *)
Theorem update_var_shared_globals_np:
  !v1 val1 v2 val2 s1 s2.
    shared_globals_np s1 s2 ==>
    shared_globals_np (update_var v1 val1 s1) (update_var v2 val2 s2)
Proof
  simp[shared_globals_np_def, update_var_def]
QED

(* Halt/revert state preservation *)
Theorem halt_state_shared_globals_np:
  !s1 s2. shared_globals_np s1 s2 ==>
    shared_globals_np (halt_state s1) (halt_state s2)
Proof
  simp[shared_globals_np_def, halt_state_def]
QED

Theorem revert_state_shared_globals_np:
  !s1 s2. shared_globals_np s1 s2 ==>
    shared_globals_np (revert_state s1) (revert_state s2)
Proof
  simp[shared_globals_np_def, revert_state_def]
QED

(* Per-category clone_np lemmas *)

Theorem exec_pure1_clone_np:
  !f prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone ==>
    case exec_pure1 f inst s_callee of
      OK sc => ?sc'. exec_pure1 f (clone_instruction prefix labels inst)
                       s_clone = OK sc' /\
                     clone_rel_np prefix labels sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  simp[exec_pure1_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `eval_operand h s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  irule update_var_clone_rel_np >> simp[]
QED

Theorem exec_pure2_clone_np:
  !f prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone ==>
    case exec_pure2 f inst s_callee of
      OK sc => ?sc'. exec_pure2 f (clone_instruction prefix labels inst)
                       s_clone = OK sc' /\
                     clone_rel_np prefix labels sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  simp[exec_pure2_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `eval_operand h' s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  irule update_var_clone_rel_np >> simp[]
QED

Theorem exec_pure3_clone_np:
  !f prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone ==>
    case exec_pure3 f inst s_callee of
      OK sc => ?sc'. exec_pure3 f (clone_instruction prefix labels inst)
                       s_clone = OK sc' /\
                     clone_rel_np prefix labels sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  simp[exec_pure3_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `eval_operand h s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `eval_operand h' s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `eval_operand h'' s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  irule update_var_clone_rel_np >> simp[]
QED

Theorem exec_read0_clone_np:
  !f prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    (!s1 s2. shared_globals_np s1 s2 ==> f s1 = f s2) ==>
    case exec_read0 f inst s_callee of
      OK sc => ?sc'. exec_read0 f (clone_instruction prefix labels inst)
                       s_clone = OK sc' /\
                     clone_rel_np prefix labels sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  simp[exec_read0_def, clone_instruction_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `f s_callee = f s_clone` by
    (first_x_assum irule >> fs[clone_rel_np_def]) >>
  simp[] >>
  irule update_var_clone_rel_np >> simp[]
QED

Theorem exec_read1_clone_np:
  !f prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    (!v s1 s2. shared_globals_np s1 s2 ==> f v s1 = f v s2) ==>
    case exec_read1 f inst s_callee of
      OK sc => ?sc'. exec_read1 f (clone_instruction prefix labels inst)
                       s_clone = OK sc' /\
                     clone_rel_np prefix labels sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  simp[exec_read1_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `eval_operand h s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `f x s_callee = f x s_clone` by
    (first_x_assum irule >> fs[clone_rel_np_def]) >>
  simp[] >>
  irule update_var_clone_rel_np >> simp[]
QED

Theorem exec_write2_clone_np:
  !f prefix labels inst s_callee s_clone.
    clone_rel_np prefix labels s_callee s_clone /\
    (!v1 v2 s1 s2. clone_rel_np prefix labels s1 s2 ==>
       clone_rel_np prefix labels (f v1 v2 s1) (f v1 v2 s2)) ==>
    case exec_write2 f inst s_callee of
      OK sc => ?sc'. exec_write2 f (clone_instruction prefix labels inst)
                       s_clone = OK sc' /\
                     clone_rel_np prefix labels sc sc'
    | _ => T
Proof
  rpt strip_tac >>
  simp[exec_write2_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  Cases_on `eval_operand h' s_callee` >> simp[] >>
  imp_res_tac eval_operand_clone_np_some >> simp[] >>
  first_x_assum irule >> simp[]
QED

(* resolve_phi commutes with clone_operand (needed for PHI opcode) *)
Theorem resolve_phi_clone:
  !prev ops prefix labels.
    EVERY (\op. !l. op = Label l ==> MEM l labels) ops ==>
    resolve_phi (STRCAT prefix prev)
      (MAP (clone_operand prefix labels) ops) =
    OPTION_MAP (clone_operand prefix labels) (resolve_phi prev ops)
Proof
  recInduct resolve_phi_ind >>
  simp[resolve_phi_def, clone_operand_def] >>
  rpt strip_tac >> fs[EVERY_DEF] >>
  Cases_on `MEM lbl labels` >> simp[resolve_phi_def] >>
  TRY (`(STRCAT prefix prev_bb = STRCAT prefix lbl) <=> (prev_bb = lbl)` by
    metis_tac[STRCAT_RIGHT_CANCEL] >> simp[]) >>
  IF_CASES_TAC >> simp[]
QED

(* ===== step_inst_base_clone_np =====
   ML-generated per-opcode theorems, then combined.
   Same pattern as functionInlinerCategoryScript but for clone_rel_np.

   Architecture:
   - Simple opcodes (16): use pre-computed SIB + EVERY_CASE_TAC (~0.2s each)
   - Ext call opcodes (5): use category-level helpers (exec_ext_call_clone_np etc.)
     to avoid EVERY_CASE_TAC on deeply nested case expressions
   - Copy/store opcodes (7): use params_irrel bridge approach
*)

val rec_eq = venomStateTheory.venom_state_component_equality;

(* --- Category-level helpers for ext calls under clone_rel_np --- *)

Theorem read_memory_np:
  !s1 s2 off sz. shared_globals_np s1 s2 ==>
    read_memory off sz s1 = read_memory off sz s2
Proof rw[read_memory_def, shared_globals_np_def]
QED

Theorem mvcs_np:
  !s1 s2 tgt gas val cd code is_st. shared_globals_np s1 s2 ==>
    make_venom_call_state s1 tgt gas val cd code is_st =
    make_venom_call_state s2 tgt gas val cd code is_st
Proof rw[make_venom_call_state_def, LET_THM, shared_globals_np_def,
         venom_to_tx_params_def]
QED

Theorem mvds_np:
  !s1 s2 tgt gas cd code is_st. shared_globals_np s1 s2 ==>
    make_venom_delegatecall_state s1 tgt gas cd code is_st =
    make_venom_delegatecall_state s2 tgt gas cd code is_st
Proof rw[make_venom_delegatecall_state_def, LET_THM, shared_globals_np_def,
         venom_to_tx_params_def]
QED

Theorem mvrs_np:
  !s1 s2 addr gas val ic. shared_globals_np s1 s2 ==>
    make_venom_create_state s1 addr gas val ic =
    make_venom_create_state s2 addr gas val ic
Proof rw[make_venom_create_state_def, LET_THM, shared_globals_np_def,
         venom_to_tx_params_def]
QED

Theorem evr_clone_np:
  !prefix labels s_callee s_clone ov ro rs rr output s_callee'.
    clone_rel_np prefix labels s_callee s_clone /\
    extract_venom_result s_callee ov ro rs rr = SOME (output, s_callee') ==>
    ?s_clone'.
      extract_venom_result s_clone ov ro rs rr = SOME (output, s_clone') /\
      clone_rel_np prefix labels s_callee' s_clone'
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[LET_THM] >>
  gvs[clone_rel_np_def, shared_globals_np_def,
      write_memory_with_expansion_def, LET_THM]
QED

Theorem evr_none_np:
  !prefix labels s1 s2 ov ro rs rr.
    clone_rel_np prefix labels s1 s2 ==>
    (extract_venom_result s1 ov ro rs rr = NONE <=>
     extract_venom_result s2 ov ro rs rr = NONE)
Proof
  rw[extract_venom_result_def, clone_rel_np_def, shared_globals_np_def,
     write_memory_with_expansion_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Shared tail for ext call clone_np proofs *)
val ext_np_tail =
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  irule update_var_clone_rel_np >> simp[];

(* exec_ext_call: CALL, STATICCALL *)
Theorem exec_ext_call_clone_np:
  !prefix labels inst s_callee s_clone
   gas addr value ao as_ ro rs is_st.
    clone_rel_np prefix labels s_callee s_clone ==>
    case exec_ext_call inst s_callee gas addr value ao as_ ro rs is_st of
      OK sc => ?sc'.
        exec_ext_call (clone_instruction prefix labels inst) s_clone
          gas addr value ao as_ ro rs is_st = OK sc' /\
        clone_rel_np prefix labels sc sc'
    | Error e => ?e'.
        exec_ext_call (clone_instruction prefix labels inst) s_clone
          gas addr value ao as_ ro rs is_st = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  `shared_globals_np s_callee s_clone` by fs[clone_rel_np_def] >>
  simp[exec_ext_call_def, LET_THM, clone_inst_outputs] >>
  `read_memory (w2n ao) (w2n as_) s_callee =
   read_memory (w2n ao) (w2n as_) s_clone` by
    (irule read_memory_np >> simp[]) >>
  `s_callee.vs_accounts = s_clone.vs_accounts` by gvs[shared_globals_np_def] >>
  `s_callee.vs_call_ctx = s_clone.vs_call_ctx` by gvs[shared_globals_np_def] >>
  `make_venom_call_state s_callee (w2w addr) (w2n gas) (w2n value)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code is_st =
   make_venom_call_state s_clone (w2w addr) (w2n gas) (w2n value)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code is_st` by
    (irule mvcs_np >> simp[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s_callee _ _ _ rr` >>
  Cases_on `extract_venom_result s_callee 1w (w2n ro) (w2n rs) rr` >> simp[]
  >- (imp_res_tac evr_none_np >> gvs[])
  >> Cases_on `x` >> imp_res_tac evr_clone_np >> gvs[] >> ext_np_tail
QED

(* exec_delegatecall: DELEGATECALL *)
Theorem exec_delegatecall_clone_np:
  !prefix labels inst s_callee s_clone
   gas addr ao as_ ro rs.
    clone_rel_np prefix labels s_callee s_clone ==>
    case exec_delegatecall inst s_callee gas addr ao as_ ro rs of
      OK sc => ?sc'.
        exec_delegatecall (clone_instruction prefix labels inst) s_clone
          gas addr ao as_ ro rs = OK sc' /\
        clone_rel_np prefix labels sc sc'
    | Error e => ?e'.
        exec_delegatecall (clone_instruction prefix labels inst) s_clone
          gas addr ao as_ ro rs = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  `shared_globals_np s_callee s_clone` by fs[clone_rel_np_def] >>
  simp[exec_delegatecall_def, LET_THM, clone_inst_outputs] >>
  `read_memory (w2n ao) (w2n as_) s_callee =
   read_memory (w2n ao) (w2n as_) s_clone` by
    (irule read_memory_np >> simp[]) >>
  `s_callee.vs_accounts = s_clone.vs_accounts` by gvs[shared_globals_np_def] >>
  `s_callee.vs_call_ctx = s_clone.vs_call_ctx` by gvs[shared_globals_np_def] >>
  `make_venom_delegatecall_state s_callee (w2w addr) (w2n gas)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code
     s_clone.vs_call_ctx.cc_static =
   make_venom_delegatecall_state s_clone (w2w addr) (w2n gas)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code
     s_clone.vs_call_ctx.cc_static` by
    (irule mvds_np >> simp[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s_callee _ _ _ rr` >>
  Cases_on `extract_venom_result s_callee 1w (w2n ro) (w2n rs) rr` >> simp[]
  >- (imp_res_tac evr_none_np >> gvs[])
  >> Cases_on `x` >> imp_res_tac evr_clone_np >> gvs[] >> ext_np_tail
QED

(* exec_create: CREATE, CREATE2 *)
Theorem exec_create_clone_np:
  !prefix labels inst s_callee s_clone value offset sz salt_opt.
    clone_rel_np prefix labels s_callee s_clone ==>
    case exec_create inst s_callee value offset sz salt_opt of
      OK sc => ?sc'.
        exec_create (clone_instruction prefix labels inst) s_clone
          value offset sz salt_opt = OK sc' /\
        clone_rel_np prefix labels sc sc'
    | Error e => ?e'.
        exec_create (clone_instruction prefix labels inst) s_clone
          value offset sz salt_opt = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  `shared_globals_np s_callee s_clone` by fs[clone_rel_np_def] >>
  `read_memory (w2n offset) (w2n sz) s_callee =
   read_memory (w2n offset) (w2n sz) s_clone` by
    (irule read_memory_np >> simp[]) >>
  `s_callee.vs_accounts = s_clone.vs_accounts /\
   s_callee.vs_call_ctx = s_clone.vs_call_ctx` by gvs[shared_globals_np_def] >>
  simp[exec_create_def, LET_THM, clone_inst_outputs] >>
  `!a g v ic. make_venom_create_state s_callee a g v ic =
              make_venom_create_state s_clone a g v ic` by
    (rpt gen_tac >> irule mvrs_np >> simp[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s_callee ov 0 0 rr` >>
  Cases_on `extract_venom_result s_callee ov 0 0 rr` >> simp[]
  >- (imp_res_tac evr_none_np >> gvs[])
  >> Cases_on `x` >> imp_res_tac evr_clone_np >> gvs[] >> ext_np_tail
QED

val _ = export_theory();

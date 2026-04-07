(*
 * Function Inliner — Step-Level Clone Simulation
 *
 * Proves that step_inst_base on a cloned instruction produces
 * clone_rel-related results when applied to clone_rel-related states.
 *
 * Architecture: 
 *   1. exec_*_clone lemmas (in CloneSim) handle OK-or-Error dispatch
 *   2. lift_oe bridges from OK-or-Error to full 5-case conclusion
 *   3. Per-opcode dispatch via Cases_on + category tactics
 *)

Theory functionInlinerStepClone
Ancestors
  functionInlinerCategory functionInlinerCloneSim functionInlinerDefs
  venomExecSemantics venomInst venomState stateEquiv

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory

(* ================================================================
   Resolve-phi correspondence for PHI case
   ================================================================ *)

Theorem resolve_phi_clone:
  !prefix labels prev ops.
    EVERY (\op. !l. op = Label l ==> MEM l labels) ops ==>
    resolve_phi (STRCAT prefix prev)
      (MAP (clone_operand prefix labels) ops) =
    OPTION_MAP (clone_operand prefix labels)
      (resolve_phi prev ops)
Proof
  ntac 3 gen_tac >>
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- simp[resolve_phi_def] >>
  rename1 `op1 :: rest1` >>
  Cases_on `rest1` >- (Cases_on `op1` >> simp[resolve_phi_def, clone_operand_def]) >>
  rename1 `op1 :: op2 :: rest2` >>
  strip_tac >>
  Cases_on `op1` >> gvs[clone_operand_def, resolve_phi_def] >>
  IF_CASES_TAC >> simp[]
QED

(* ================================================================
   Extract-labels correspondence for DJMP case
   ================================================================ *)

Theorem extract_labels_clone:
  !prefix labels ops lbls.
    extract_labels ops = SOME lbls ==>
    extract_labels (MAP (clone_operand prefix labels) ops) =
    SOME (MAP (\l. if MEM l labels then STRCAT prefix l else l) lbls)
Proof
  ntac 2 gen_tac >>
  Induct_on `ops` >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def, clone_operand_def] >>
  rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[extract_labels_def]
QED

Theorem extract_labels_clone_none[local]:
  !prefix labels ops.
    extract_labels ops = NONE ==>
    extract_labels (MAP (clone_operand prefix labels) ops) = NONE
Proof
  ntac 2 gen_tac >>
  Induct_on `ops` >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def, clone_operand_def] >>
  rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[extract_labels_def]
QED

Theorem extract_labels_every_mem[local]:
  !ops lbls P.
    extract_labels ops = SOME lbls /\
    EVERY (\op. !l. op = Label l ==> P l) ops ==>
    EVERY P lbls
Proof
  Induct_on `ops` >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def] >>
  rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Theorem resolve_phi_mem[local]:
  !prev ops x. resolve_phi prev ops = SOME x ==> MEM x ops
Proof
  ho_match_mp_tac resolve_phi_ind >>
  rw[resolve_phi_def]
QED

(* ================================================================
   write_memory_with_expansion clone
   ================================================================ *)

Theorem write_memory_clone:
  !prefix labels s_callee s_clone offset bytes.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (write_memory_with_expansion offset bytes s_callee)
      (write_memory_with_expansion offset bytes s_clone)
Proof
  simp[write_memory_with_expansion_def, LET_THM,
       clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

(* ================================================================
   Generic lifting: OK-or-Error result -> full 5-case conclusion
   ================================================================ *)

Theorem lift_oe[local]:
  !(g:exec_result) (g':exec_result) prefix labels.
    (case g of
       OK sc => ?sc'. g' = OK sc' /\ clone_rel prefix labels sc sc'
     | Error e => ?e'. g' = Error e'
     | _ => T) /\
    (!sc. g <> Halt sc) /\ (!a sc. g <> Abort a sc) /\
    (!v sc. g <> IntRet v sc) ==>
    case g of
      OK sc => ?sc'. g' = OK sc' /\ clone_rel prefix labels sc sc'
    | Halt sc => ?sc'. g' = Halt sc' /\ shared_globals sc sc'
    | Abort a sc => ?sc'. g' = Abort a sc' /\ shared_globals sc sc'
    | IntRet v sc => T
    | Error e => ?e'. g' = Error e'
Proof
  Cases_on `g` >> simp[]
QED

(* Direct lifting for specific result constructors *)
Theorem lift_halt[local]:
  !prefix labels inst s_callee s_clone sc sc'.
    step_inst_base inst s_callee = Halt sc /\
    step_inst_base (clone_instruction prefix labels inst) s_clone =
      Halt sc' /\
    shared_globals sc sc' ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = OK sc' /\ clone_rel prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Halt sc' /\ shared_globals sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Abort a sc' /\ shared_globals sc sc'
    | IntRet v sc => T
    | Error e => ?e'. step_inst_base (clone_instruction prefix labels inst)
               s_clone = Error e'
Proof
  rpt strip_tac >> gvs[]
QED

Theorem lift_abort[local]:
  !prefix labels inst s_callee s_clone a sc sc'.
    step_inst_base inst s_callee = Abort a sc /\
    step_inst_base (clone_instruction prefix labels inst) s_clone =
      Abort a sc' /\
    shared_globals sc sc' ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = OK sc' /\ clone_rel prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Halt sc' /\ shared_globals sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Abort a sc' /\ shared_globals sc sc'
    | IntRet v sc => T
    | Error e => ?e'. step_inst_base (clone_instruction prefix labels inst)
               s_clone = Error e'
Proof
  rpt strip_tac >> gvs[]
QED

Theorem lift_ok[local]:
  !prefix labels inst s_callee s_clone sc sc'.
    step_inst_base inst s_callee = OK sc /\
    step_inst_base (clone_instruction prefix labels inst) s_clone =
      OK sc' /\
    clone_rel prefix labels sc sc' ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = OK sc' /\ clone_rel prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Halt sc' /\ shared_globals sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Abort a sc' /\ shared_globals sc sc'
    | IntRet v sc => T
    | Error e => ?e'. step_inst_base (clone_instruction prefix labels inst)
               s_clone = Error e'
Proof
  rpt strip_tac >> gvs[]
QED

Theorem lift_error[local]:
  !prefix labels inst s_callee s_clone e e'.
    step_inst_base inst s_callee = Error e /\
    step_inst_base (clone_instruction prefix labels inst) s_clone =
      Error e' ==>
    case step_inst_base inst s_callee of
      OK sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = OK sc' /\ clone_rel prefix labels sc sc'
    | Halt sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Halt sc' /\ shared_globals sc sc'
    | Abort a sc => ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Abort a sc' /\ shared_globals sc sc'
    | IntRet v sc => T
    | Error e => ?e'. step_inst_base (clone_instruction prefix labels inst)
               s_clone = Error e'
Proof
  rpt strip_tac >> gvs[]
QED

(* ================================================================
   Operand helpers (local)
   ================================================================ *)

Theorem eval_op_clone_local[local]:
  !prefix labels op s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    eval_operand (clone_operand prefix labels op) s_clone =
    eval_operand op s_callee
Proof
  rpt strip_tac >>
  irule eval_operand_clone >> simp[]
QED

Theorem eval_op_none_clone[local]:
  !prefix labels op s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    eval_operand op s_callee = NONE ==>
    eval_operand (clone_operand prefix labels op) s_clone = NONE
Proof
  rpt strip_tac >> imp_res_tac eval_op_clone_local >> gvs[]
QED

Theorem eval_ops_clone_local[local]:
  !prefix labels ops s_callee s_clone vals.
    clone_rel prefix labels s_callee s_clone /\
    eval_operands ops s_callee = SOME vals ==>
    eval_operands (MAP (clone_operand prefix labels) ops) s_clone =
    SOME vals
Proof
  Induct_on `ops` >> rw[eval_operands_def] >> gvs[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac eval_op_clone_local >> gvs[] >>
  first_x_assum (qspecl_then [`prefix`,`labels`,`s_callee`,`s_clone`] mp_tac) >>
  simp[]
QED

(* ================================================================
   External call clone helper
   
   All external call functions (exec_ext_call, exec_delegatecall,
   exec_create) share a common pattern: they compute intermediate
   values from shared_globals fields only, then update_var on the
   output. This lemma captures the core: if the computation before
   update_var is identical on both sides (because shared_globals
   are equal), and the output variable is prefixed, clone_rel holds.
   ================================================================ *)

(* Helper: extract_venom_result preserves clone_rel *)
Theorem extract_venom_result_clone[local]:
  !prefix labels s_callee s_clone ov ro rs rr output s_callee'.
    clone_rel prefix labels s_callee s_clone /\
    extract_venom_result s_callee ov ro rs rr = SOME (output, s_callee') ==>
    ?s_clone'.
      extract_venom_result s_clone ov ro rs rr = SOME (output, s_clone') /\
      clone_rel prefix labels s_callee' s_clone'
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[LET_THM] >>
  gvs[clone_rel_def, shared_globals_def,
      write_memory_with_expansion_def, LET_THM]
QED

(* Symmetric: NONE on callee iff NONE on clone *)
Theorem extract_venom_result_none_clone[local]:
  !prefix labels s_callee s_clone ov ro rs rr.
    clone_rel prefix labels s_callee s_clone ==>
    (extract_venom_result s_callee ov ro rs rr = NONE <=>
     extract_venom_result s_clone ov ro rs rr = NONE)
Proof
  rw[extract_venom_result_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[LET_THM]
QED

(* Full ext_call output dispatch: given clone_rel states and same 
   extract_venom_result input, the output dispatch preserves clone_rel *)
Theorem ext_output_dispatch_clone[local]:
  !prefix labels s_callee s_clone ov ro rs rr inst msg msg2.
    clone_rel prefix labels s_callee s_clone ==>
    case (case extract_venom_result s_callee ov ro rs rr of
            NONE => Error msg
          | SOME (output, s'') =>
              case inst.inst_outputs of
                [out] => OK (update_var out output s'')
              | _ => Error msg2) of
      OK sc => ?sc'.
        (case extract_venom_result s_clone ov ro rs rr of
           NONE => Error msg
         | SOME (output, s'') =>
             case MAP (STRCAT prefix) inst.inst_outputs of
               [out] => OK (update_var out output s'')
             | _ => Error msg2) = OK sc' /\
        clone_rel prefix labels sc sc'
    | Error e => ?e'.
        (case extract_venom_result s_clone ov ro rs rr of
           NONE => Error msg
         | SOME (output, s'') =>
             case MAP (STRCAT prefix) inst.inst_outputs of
               [out] => OK (update_var out output s'')
             | _ => Error msg2) = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  Cases_on `extract_venom_result s_callee ov ro rs rr` >> simp[]
  >- (imp_res_tac extract_venom_result_none_clone >> gvs[])
  >> Cases_on `x` >>
  imp_res_tac extract_venom_result_clone >> gvs[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  irule clone_rel_update_var >> simp[]
QED

(* Helper: read_memory depends only on shared_globals *)
Theorem read_memory_shared[local]:
  !s1 s2 off sz.
    shared_globals s1 s2 ==>
    read_memory off sz s1 = read_memory off sz s2
Proof
  rw[read_memory_def, shared_globals_def]
QED

(* Helper: make_venom_call_state depends only on shared_globals *)
Theorem make_venom_call_state_shared[local]:
  !s1 s2 tgt gas val cd code is_st.
    shared_globals s1 s2 ==>
    make_venom_call_state s1 tgt gas val cd code is_st =
    make_venom_call_state s2 tgt gas val cd code is_st
Proof
  rw[make_venom_call_state_def, LET_THM, shared_globals_def,
     venom_to_tx_params_def]
QED

Theorem make_venom_delegatecall_state_shared[local]:
  !s1 s2 tgt gas cd code is_st.
    shared_globals s1 s2 ==>
    make_venom_delegatecall_state s1 tgt gas cd code is_st =
    make_venom_delegatecall_state s2 tgt gas cd code is_st
Proof
  rw[make_venom_delegatecall_state_def, LET_THM, shared_globals_def,
     venom_to_tx_params_def]
QED

Theorem make_venom_create_state_shared[local]:
  !s1 s2 addr gas val ic.
    shared_globals s1 s2 ==>
    make_venom_create_state s1 addr gas val ic =
    make_venom_create_state s2 addr gas val ic
Proof
  rw[make_venom_create_state_def, LET_THM, shared_globals_def,
     venom_to_tx_params_def]
QED

(* Helper: clone_rel implies shared_globals *)
val sg_from_cr = Q.prove(
  `clone_rel prefix labels s1 s2 ==> shared_globals s1 s2`,
  rw[clone_rel_def]);

(* Shared tactic for all external call clone proofs *)
val ext_sg_defs = [shared_globals_def, read_memory_def,
  make_venom_call_state_def, make_venom_delegatecall_state_def,
  make_venom_create_state_def, venom_to_tx_params_def];

(* Shared tactic for ext_call/delegatecall/create clone proofs.
   Pattern: expand def → establish intermediate equalities with >~ →
   case-split on extract_venom_result → use clone lemmas *)
val ext_call_common_tail =
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  irule clone_rel_update_var >> simp[];

(* Core pattern for exec_ext_call / exec_delegatecall / exec_create:
   After evaluating operands (same values on both sides), the
   computation uses only shared_globals fields. So the entire
   external call produces the same (output, s') on both sides,
   differing only in the update_var output name. *)
Theorem exec_ext_call_clone[local]:
  !prefix labels inst s_callee s_clone
   gas addr value ao as_ ro rs is_st.
    clone_rel prefix labels s_callee s_clone ==>
    case exec_ext_call inst s_callee gas addr value ao as_ ro rs is_st of
      OK sc => ?sc'.
        exec_ext_call (clone_instruction prefix labels inst) s_clone
          gas addr value ao as_ ro rs is_st = OK sc' /\
        clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_ext_call (clone_instruction prefix labels inst) s_clone
          gas addr value ao as_ ro rs is_st = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  imp_res_tac sg_from_cr >>
  simp[exec_ext_call_def, LET_THM, clone_inst_outputs] >>
  `read_memory (w2n ao) (w2n as_) s_callee =
   read_memory (w2n ao) (w2n as_) s_clone` by
    (irule read_memory_shared >> simp[])
  >~ [`make_venom_call_state`] >>
  `s_callee.vs_accounts = s_clone.vs_accounts` by
    gvs[shared_globals_def]
  >~ [`make_venom_call_state`] >>
  `make_venom_call_state s_callee (w2w addr) (w2n gas) (w2n value)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code is_st =
   make_venom_call_state s_clone (w2w addr) (w2n gas) (w2n value)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code is_st` by
    (irule make_venom_call_state_shared >> simp[])
  >~ [`extract_venom_result`] >>
  gvs[] >>
  Cases_on `extract_venom_result s_callee 1w (w2n ro) (w2n rs)
    (run (make_venom_call_state s_clone (w2w addr) (w2n gas) (w2n value)
       (read_memory (w2n ao) (w2n as_) s_clone)
       (lookup_account (w2w addr) s_clone.vs_accounts).code is_st))`
  >> simp[]
  >- (imp_res_tac extract_venom_result_none_clone >> gvs[])
  >> Cases_on `x` >>
  imp_res_tac extract_venom_result_clone >> gvs[] >>
  ext_call_common_tail
QED

(* delegatecall follows the same pattern *)
Theorem exec_delegatecall_clone[local]:
  !prefix labels inst s_callee s_clone
   gas addr ao as_ ro rs.
    clone_rel prefix labels s_callee s_clone ==>
    case exec_delegatecall inst s_callee gas addr ao as_ ro rs of
      OK sc => ?sc'.
        exec_delegatecall (clone_instruction prefix labels inst) s_clone
          gas addr ao as_ ro rs = OK sc' /\
        clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_delegatecall (clone_instruction prefix labels inst) s_clone
          gas addr ao as_ ro rs = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  imp_res_tac sg_from_cr >>
  simp[exec_delegatecall_def, LET_THM, clone_inst_outputs] >>
  `read_memory (w2n ao) (w2n as_) s_callee =
   read_memory (w2n ao) (w2n as_) s_clone` by
    (irule read_memory_shared >> simp[])
  >~ [`make_venom_delegatecall_state`] >>
  `s_callee.vs_accounts = s_clone.vs_accounts /\
   s_callee.vs_call_ctx = s_clone.vs_call_ctx` by
    gvs[shared_globals_def]
  >~ [`make_venom_delegatecall_state`] >> gvs[] >>
  `make_venom_delegatecall_state s_callee (w2w addr) (w2n gas)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code
     s_clone.vs_call_ctx.cc_static =
   make_venom_delegatecall_state s_clone (w2w addr) (w2n gas)
     (read_memory (w2n ao) (w2n as_) s_clone)
     (lookup_account (w2w addr) s_clone.vs_accounts).code
     s_clone.vs_call_ctx.cc_static` by
    (irule make_venom_delegatecall_state_shared >> simp[])
  >~ [`extract_venom_result`] >> gvs[] >>
  Cases_on `extract_venom_result s_callee 1w (w2n ro) (w2n rs)
    (run (make_venom_delegatecall_state s_clone (w2w addr) (w2n gas)
       (read_memory (w2n ao) (w2n as_) s_clone)
       (lookup_account (w2w addr) s_clone.vs_accounts).code
       s_clone.vs_call_ctx.cc_static))`
  >> simp[]
  >- (imp_res_tac extract_venom_result_none_clone >> gvs[])
  >> Cases_on `x` >>
  imp_res_tac extract_venom_result_clone >> gvs[] >>
  ext_call_common_tail
QED

(* create: slightly more complex intermediate values, same pattern *)
Theorem exec_create_clone[local]:
  !prefix labels inst s_callee s_clone
   value offset sz salt_opt.
    clone_rel prefix labels s_callee s_clone ==>
    case exec_create inst s_callee value offset sz salt_opt of
      OK sc => ?sc'.
        exec_create (clone_instruction prefix labels inst) s_clone
          value offset sz salt_opt = OK sc' /\
        clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_create (clone_instruction prefix labels inst) s_clone
          value offset sz salt_opt = Error e'
    | _ => T
Proof
  rpt strip_tac >>
  imp_res_tac sg_from_cr >>
  simp[exec_create_def, LET_THM, clone_inst_outputs] >>
  `read_memory (w2n offset) (w2n sz) s_callee =
   read_memory (w2n offset) (w2n sz) s_clone` by
    (irule read_memory_shared >> simp[])
  >~ [`make_venom_create_state`] >>
  `s_callee.vs_accounts = s_clone.vs_accounts /\
   s_callee.vs_call_ctx = s_clone.vs_call_ctx` by
    gvs[shared_globals_def]
  >~ [`make_venom_create_state`] >> gvs[] >>
  `make_venom_create_state s_callee = make_venom_create_state s_clone` by
    (rw[FUN_EQ_THM, make_venom_create_state_def, LET_THM,
        venom_to_tx_params_def] >>
     gvs[shared_globals_def])
  >~ [`extract_venom_result`] >> gvs[] >>
  Cases_on `extract_venom_result s_callee
    (w2w
       (case salt_opt of
          NONE =>
            address_for_create s_clone.vs_call_ctx.cc_address
              (lookup_account s_clone.vs_call_ctx.cc_address
                 s_clone.vs_accounts).nonce
        | SOME salt =>
          address_for_create2 s_clone.vs_call_ctx.cc_address salt
            (read_memory (w2n offset) (w2n sz) s_clone))) 0 0
    (run
       (make_venom_create_state s_clone
          (case salt_opt of
             NONE =>
               address_for_create s_clone.vs_call_ctx.cc_address
                 (lookup_account s_clone.vs_call_ctx.cc_address
                    s_clone.vs_accounts).nonce
           | SOME salt =>
             address_for_create2 s_clone.vs_call_ctx.cc_address salt
               (read_memory (w2n offset) (w2n sz) s_clone))
          (s_clone.vs_call_ctx.cc_gas - s_clone.vs_call_ctx.cc_gas DIV 64)
          (w2n value) (read_memory (w2n offset) (w2n sz) s_clone)))`
  >> simp[]
  >- (imp_res_tac extract_venom_result_none_clone >> gvs[])
  >> Cases_on `x` >>
  imp_res_tac extract_venom_result_clone >> gvs[] >>
  ext_call_common_tail
QED

(* exec_ext_call / exec_delegatecall / exec_create only return OK or Error.
   These discharge the impossible Halt/Abort/IntRet branches in step_base proofs. *)
Theorem exec_ext_call_ok_or_error[local]:
  !inst s gas addr value ao as_ ro rs is_st.
    (?sc. exec_ext_call inst s gas addr value ao as_ ro rs is_st = OK sc) \/
    (?e. exec_ext_call inst s gas addr value ao as_ ro rs is_st = Error e)
Proof
  rw[exec_ext_call_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC
QED

Theorem exec_delegatecall_ok_or_error[local]:
  !inst s gas addr ao as_ ro rs.
    (?sc. exec_delegatecall inst s gas addr ao as_ ro rs = OK sc) \/
    (?e. exec_delegatecall inst s gas addr ao as_ ro rs = Error e)
Proof
  rw[exec_delegatecall_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC
QED

Theorem exec_create_ok_or_error[local]:
  !inst s value offset sz salt_opt.
    (?sc. exec_create inst s value offset sz salt_opt = OK sc) \/
    (?e. exec_create inst s value offset sz salt_opt = Error e)
Proof
  rw[exec_create_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC
QED

(* ================================================================
   step_inst_base_clone — machinery and proof

   OFFSET is excluded because it looks up vs_labels by label
   name, and clone_operand changes the key. OFFSET is a deploy/linking
   construct that doesn't appear in callee bodies being inlined.

   Architecture:
   1. 59 category-opcode theorems (in functionInlinerCategory)
   2. Per-special-opcode hand-written theorems (below)
   3. Main theorem: Cases_on opcode, dispatch to all per-opcode thms
   ================================================================ *)

(* Import the 59 ML-generated theorems from Category theory *)
local open functionInlinerCategoryTheory in
val category_thms =
  [sbc_ADD, sbc_SUB, sbc_MUL, sbc_Div, sbc_Mod,
   sbc_SDIV, sbc_SMOD, sbc_Exp, sbc_EQ, sbc_LT, sbc_GT,
   sbc_SLT, sbc_SGT, sbc_AND, sbc_OR, sbc_XOR,
   sbc_SHL, sbc_SHR, sbc_SAR, sbc_SIGNEXTEND, sbc_BYTE,
   sbc_ISZERO, sbc_NOT, sbc_ADDMOD, sbc_MULMOD,
   sbc_CALLER, sbc_ADDRESS, sbc_CALLVALUE, sbc_GAS,
   sbc_ORIGIN, sbc_GASPRICE, sbc_CHAINID, sbc_COINBASE,
   sbc_TIMESTAMP, sbc_NUMBER, sbc_PREVRANDAO, sbc_GASLIMIT,
   sbc_BASEFEE, sbc_BLOBBASEFEE, sbc_SELFBALANCE,
   sbc_CALLDATASIZE, sbc_RETURNDATASIZE, sbc_MSIZE, sbc_CODESIZE,
   sbc_MLOAD, sbc_SLOAD, sbc_TLOAD, sbc_BLOCKHASH,
   sbc_BLOBHASH, sbc_BALANCE, sbc_CALLDATALOAD,
   sbc_EXTCODESIZE, sbc_ILOAD, sbc_DLOAD, sbc_EXTCODEHASH,
   sbc_MSTORE, sbc_MSTORE8, sbc_SSTORE, sbc_TSTORE]
end;

(* --- Helper for special opcodes: eval_operand on clone side --- *)
fun eval_clone_tac () =
  imp_res_tac sg_from_cr >>
  imp_res_tac eval_op_clone_local >> gvs[];

(* Shared tactic for establishing eval_operand equalities in ext_call proofs.
   Uses SUBGOAL_THEN ... >- pattern to avoid `by` precedence issues. *)
val eval_eq_tac =
  irule eval_op_clone_local >> simp[];

val sbc_concl =
  ``case step_inst_base inst s_callee of
      OK s_res =>
        ?s_res'. step_inst_base (clone_instruction prefix labels inst)
                   s_clone = OK s_res' /\
                 clone_rel prefix labels s_res s_res'
    | Halt s_res =>
        ?s_res'. step_inst_base (clone_instruction prefix labels inst)
                   s_clone = Halt s_res' /\
                 shared_globals s_res s_res'
    | Abort abt s_res =>
        ?s_res'. step_inst_base (clone_instruction prefix labels inst)
                   s_clone = Abort abt s_res' /\
                 shared_globals s_res s_res'
    | IntRet retv s_res => T
    | Error err =>
        ?err'. step_inst_base (clone_instruction prefix labels inst)
                 s_clone = Error err'``;

(* --- Special opcodes: control flow --- *)

Theorem step_base_jmp[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = JMP /\
    EVERY (\op. !l. op = Label l ==> MEM l labels)
          inst.inst_operands ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[clone_operand_def] >>
  Cases_on `t` >> gvs[] >>
  irule clone_rel_jump_to >> simp[]
QED

Theorem step_base_jnz[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = JNZ /\
    EVERY (\op. !l. op = Label l ==> MEM l labels)
          inst.inst_operands ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `h'` >> gvs[clone_operand_def] >>
  Cases_on `h''` >> gvs[clone_operand_def] >>
  Cases_on `t` >> gvs[clone_operand_def] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> simp[] >>
     Cases_on `h` >> gvs[eval_operand_def, lookup_var_def] >>
     Cases_on `FLOOKUP s_callee.vs_vars s''` >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[clone_operand_def] >>
  IF_CASES_TAC >> gvs[] >>
  irule clone_rel_jump_to >> simp[]
QED

Theorem step_base_djmp[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = DJMP /\
    EVERY (\op. !l. op = Label l ==> MEM l labels)
          inst.inst_operands ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> simp[] >>
     Cases_on `h` >> gvs[eval_operand_def, lookup_var_def] >>
     Cases_on `FLOOKUP s_callee.vs_vars s` >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `extract_labels t` >> gvs[]
  THEN1 (imp_res_tac extract_labels_clone_none >> gvs[]) >>
  imp_res_tac extract_labels_clone >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  `EVERY (\l. MEM l labels) x'` by
    (irule extract_labels_every_mem >> qexists_tac `t` >> simp[]) >>
  simp[EL_MAP] >>
  `MEM (EL (w2n x) x') labels` by
    (gvs[EVERY_EL]) >>
  gvs[] >>
  irule clone_rel_jump_to >> simp[]
QED

(* --- Special opcodes: halting/aborting --- *)

Theorem step_base_stop[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = STOP ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  irule shared_globals_halt >>
  gvs[clone_rel_def]
QED

Theorem step_base_sink[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = SINK ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  irule shared_globals_halt >>
  gvs[clone_rel_def]
QED

Theorem step_base_invalid[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = INVALID ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  irule shared_globals_halt >>
  irule shared_globals_set_returndata >>
  gvs[clone_rel_def]
QED

Theorem step_base_return[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = RETURN ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  `s_callee.vs_memory = s_clone.vs_memory` by
    gvs[clone_rel_def, shared_globals_def] >>
  gvs[] >>
  irule shared_globals_halt >>
  irule shared_globals_set_returndata >>
  gvs[clone_rel_def]
QED

Theorem step_base_revert[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = REVERT ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  `s_callee.vs_memory = s_clone.vs_memory` by
    gvs[clone_rel_def, shared_globals_def] >>
  gvs[] >>
  irule shared_globals_revert >>
  irule shared_globals_set_returndata >>
  gvs[clone_rel_def]
QED

(* --- Special opcodes: assertions --- *)

Theorem step_base_assert[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = ASSERT ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  irule shared_globals_revert >>
  irule shared_globals_set_returndata >>
  gvs[clone_rel_def]
QED

Theorem step_base_assert_unreachable[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  irule shared_globals_halt >>
  irule shared_globals_set_returndata >>
  gvs[clone_rel_def]
QED

(* --- Special opcodes: SSA --- *)

Theorem step_base_phi[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = PHI /\
    EVERY (\op. !l. op = Label l ==> MEM l labels)
          inst.inst_operands ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  (* Extract prev_bb correspondence without destroying clone_rel *)
  `s_clone.vs_prev_bb =
   OPTION_MAP (STRCAT prefix) s_callee.vs_prev_bb` by
    gvs[clone_rel_def] >>
  Cases_on `s_callee.vs_prev_bb` >> gvs[] >>
  imp_res_tac resolve_phi_clone >> gvs[] >>
  Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
  `MEM x' inst.inst_operands` by
    (irule resolve_phi_mem >> metis_tac[]) >>
  `eval_operand (clone_operand prefix labels x') s_clone =
   eval_operand x' s_callee` by
    (irule eval_op_clone_local >> simp[] >> metis_tac[]) >>
  simp[] >>
  Cases_on `eval_operand x' s_callee` >> gvs[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem step_base_assign[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = ASSIGN ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem step_base_nop[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = NOP ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode]
QED

(* --- Special opcodes: memory copy/hash --- *)

(* Tactic: establish shared_globals equality from clone_rel, unify,
   then apply write_memory_clone. Works for all memory-write opcodes
   regardless of which shared field the bytes depend on. *)
fun clone_write_mem_tac () =
  imp_res_tac sg_from_cr >>
  gvs[shared_globals_def] >>
  irule write_memory_clone >> simp[];

(* Helper for 3-operand copy-to-memory instructions *)
fun copy3_tac () =
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h'') s_clone =
   eval_operand h'' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[];

Theorem step_base_mcopy[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = MCOPY ==>
    ^sbc_concl
Proof
  copy3_tac () >> gvs[mcopy_def, LET_THM] >> clone_write_mem_tac ()
QED

Theorem step_base_calldatacopy[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = CALLDATACOPY ==>
    ^sbc_concl
Proof
  copy3_tac () >> clone_write_mem_tac ()
QED

Theorem step_base_returndatacopy[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = RETURNDATACOPY ==>
    ^sbc_concl
Proof
  copy3_tac () >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  IF_CASES_TAC >> gvs[halt_state_def, set_returndata_def] >>
  irule write_memory_clone >> simp[]
QED

Theorem step_base_codecopy[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = CODECOPY ==>
    ^sbc_concl
Proof
  copy3_tac () >> clone_write_mem_tac ()
QED

Theorem step_base_dloadbytes[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = DLOADBYTES ==>
    ^sbc_concl
Proof
  copy3_tac () >> clone_write_mem_tac ()
QED

Theorem step_base_extcodecopy[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = EXTCODECOPY ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h'') s_clone =
   eval_operand h'' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h'3') s_clone =
   eval_operand h'3' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'3' s_callee` >> gvs[] >>
  clone_write_mem_tac ()
QED

Theorem step_base_sha3[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = SHA3 ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode, LET_THM] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem step_base_istore[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = ISTORE ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  irule clone_rel_update_immutables >> simp[]
QED

(* --- Special opcodes: LOG --- *)


Theorem step_base_log[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = LOG ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode, LET_THM] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[clone_operand_def] >>
  IF_CASES_TAC >> gvs[] >>
  (* Use Cases_on t to expose HD and TL for MAP rewriting *)
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  simp[clone_operand_def, MAP_MAP_o, combinTheory.o_DEF] >>
  imp_res_tac eval_op_clone_local >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  imp_res_tac eval_operands_clone_full >> gvs[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  irule clone_rel_update_logs >> simp[]
QED

Theorem step_base_selfdestruct[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = SELFDESTRUCT ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode, LET_THM] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_op_clone_local >> simp[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  irule shared_globals_halt >>
  gvs[clone_rel_def, shared_globals_def, halt_state_def]
QED

(* --- Special opcodes: external calls --- *)

(* --- CALL: 7 operands, exec_ext_call, needs cc_static --- *)
Theorem step_base_call[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = CALL ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h) s_clone =
    eval_operand h s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h') s_clone =
    eval_operand h' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'') s_clone =
    eval_operand h'' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'3') s_clone =
    eval_operand h'3' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'4') s_clone =
    eval_operand h'4' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'5') s_clone =
    eval_operand h'5' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'6') s_clone =
    eval_operand h'6' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'3' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'4' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'5' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'6' s_callee` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  qspecl_then [`inst`,`s_callee`,`x`,`x'`,`x''`,`x'3'`,`x'4'`,`x'5'`,`x'6'`,
               `s_clone.vs_call_ctx.cc_static`]
    strip_assume_tac exec_ext_call_ok_or_error >>
  qspecl_then [`prefix`,`labels`,`inst`,`s_callee`,`s_clone`,
               `x`,`x'`,`x''`,`x'3'`,`x'4'`,`x'5'`,`x'6'`,
               `s_clone.vs_call_ctx.cc_static`]
    mp_tac exec_ext_call_clone >>
  gvs[]
QED

(* --- STATICCALL: 6 operands, exec_ext_call with value=0w, is_static=T --- *)
Theorem step_base_staticcall[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = STATICCALL ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h) s_clone =
    eval_operand h s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h') s_clone =
    eval_operand h' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'') s_clone =
    eval_operand h'' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'3') s_clone =
    eval_operand h'3' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'4') s_clone =
    eval_operand h'4' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'5') s_clone =
    eval_operand h'5' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'3' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'4' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'5' s_callee` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  qspecl_then [`inst`,`s_callee`,`x`,`x'`,`(0w:bytes32)`,`x''`,`x'3'`,
               `x'4'`,`x'5'`,`T`]
    strip_assume_tac exec_ext_call_ok_or_error >>
  qspecl_then [`prefix`,`labels`,`inst`,`s_callee`,`s_clone`,
               `x`,`x'`,`(0w:bytes32)`,`x''`,`x'3'`,`x'4'`,`x'5'`,`T`]
    mp_tac exec_ext_call_clone >>
  gvs[]
QED

(* --- DELEGATECALL: 6 operands, exec_delegatecall --- *)
Theorem step_base_delegatecall[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = DELEGATECALL ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h) s_clone =
    eval_operand h s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h') s_clone =
    eval_operand h' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'') s_clone =
    eval_operand h'' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'3') s_clone =
    eval_operand h'3' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'4') s_clone =
    eval_operand h'4' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'5') s_clone =
    eval_operand h'5' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'3' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'4' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'5' s_callee` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  qspecl_then [`inst`,`s_callee`,`x`,`x'`,`x''`,`x'3'`,`x'4'`,`x'5'`]
    strip_assume_tac exec_delegatecall_ok_or_error >>
  qspecl_then [`prefix`,`labels`,`inst`,`s_callee`,`s_clone`,
               `x`,`x'`,`x''`,`x'3'`,`x'4'`,`x'5'`]
    mp_tac exec_delegatecall_clone >>
  gvs[]
QED

(* --- CREATE: 3 operands, exec_create with salt_opt=NONE --- *)
Theorem step_base_create[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = CREATE ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h) s_clone =
    eval_operand h s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h') s_clone =
    eval_operand h' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'') s_clone =
    eval_operand h'' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  qspecl_then [`inst`,`s_callee`,`x`,`x'`,`x''`,`NONE`]
    strip_assume_tac exec_create_ok_or_error >>
  qspecl_then [`prefix`,`labels`,`inst`,`s_callee`,`s_clone`,
               `x`,`x'`,`x''`,`NONE`]
    mp_tac exec_create_clone >>
  gvs[]
QED

(* --- CREATE2: 4 operands, exec_create with salt_opt=SOME salt --- *)
Theorem step_base_create2[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = CREATE2 ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h) s_clone =
    eval_operand h s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h') s_clone =
    eval_operand h' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'') s_clone =
    eval_operand h'' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  SUBGOAL_THEN ``eval_operand (clone_operand prefix labels h'3') s_clone =
    eval_operand h'3' s_callee`` ASSUME_TAC >- eval_eq_tac >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'3' s_callee` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  qspecl_then [`inst`,`s_callee`,`x`,`x'`,`x''`,`SOME x'3'`]
    strip_assume_tac exec_create_ok_or_error >>
  qspecl_then [`prefix`,`labels`,`inst`,`s_callee`,`s_clone`,
               `x`,`x'`,`x''`,`SOME x'3'`]
    mp_tac exec_create_clone >>
  gvs[]
QED

Theorem step_base_alloca[local]:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode = ALLOCA /\
    EVERY (\op. !l. op = Label l ==> MEM l labels)
          inst.inst_operands ==>
    ^sbc_concl
Proof
  simp[step_inst_base_def, clone_inst_opcode, exec_alloca_def, LET_THM] >>
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[clone_operand_def] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  imp_res_tac sg_from_cr >> gvs[shared_globals_def] >>
  gvs[clone_instruction_def, next_alloca_offset_def] >>
  irule clone_rel_update_var >>
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >>
  gvs[clone_rel_def, shared_globals_def]
QED

(* --- Main theorem --- *)
Theorem step_inst_base_clone:
  !prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> RET /\
    inst.inst_opcode <> OFFSET /\
    EVERY (\op. !l. op = Label l ==> MEM l labels)
          inst.inst_operands ==>
    case step_inst_base inst s_callee of
      OK sc =>
        ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = OK sc' /\
              clone_rel prefix labels sc sc'
    | Halt sc =>
        ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Halt sc' /\
              shared_globals sc sc'
    | Abort a sc =>
        ?sc'. step_inst_base (clone_instruction prefix labels inst)
                s_clone = Abort a sc' /\
              shared_globals sc sc'
    | IntRet v sc => T
    | Error e =>
        ?e'. step_inst_base (clone_instruction prefix labels inst)
               s_clone = Error e'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  FIRST_PROVE (
    map (fn th => irule th >> simp[]) category_thms @
    [irule step_base_jmp >> simp[],
     irule step_base_jnz >> simp[],
     irule step_base_djmp >> simp[],
     irule step_base_stop >> simp[],
     irule step_base_sink >> simp[],
     irule step_base_invalid >> simp[],
     irule step_base_return >> simp[],
     irule step_base_revert >> simp[],
     irule step_base_assert >> simp[],
     irule step_base_assert_unreachable >> simp[],
     irule step_base_phi >> simp[],
     irule step_base_assign >> simp[],
     irule step_base_nop >> simp[],
     irule step_base_mcopy >> simp[],
     irule step_base_calldatacopy >> simp[],
     irule step_base_returndatacopy >> simp[],
     irule step_base_codecopy >> simp[],
     irule step_base_dloadbytes >> simp[],
     irule step_base_extcodecopy >> simp[],
     irule step_base_sha3 >> simp[],
     irule step_base_istore >> simp[],
     irule step_base_log >> simp[],
     irule step_base_selfdestruct >> simp[],
     irule step_base_call >> simp[],
     irule step_base_staticcall >> simp[],
     irule step_base_delegatecall >> simp[],
     irule step_base_create >> simp[],
     irule step_base_create2 >> simp[],
     irule step_base_alloca >> simp[]]
  )
QED

val _ = export_theory();

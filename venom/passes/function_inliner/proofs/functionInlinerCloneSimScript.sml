(*
 * Function Inliner — Clone Simulation
 *
 * Proves that cloned callee code (prefixed labels/vars) simulates
 * the original callee's execution, with a state relation (clone_rel)
 * that maps callee var x to caller var (prefix ++ x) and shares globals.
 *
 * Structure:
 *   1. shared_globals + clone_rel definitions
 *   2. Preservation lemmas
 *   3. Operand evaluation correspondence
 *   4. step_inst_base_clone (single big theorem)
 *   5. inline_candidate_correct (uses step_inst_base_clone)
 *)

Theory functionInlinerCloneSim
Ancestors
  functionInlinerDefs functionInlinerFresh functionInlinerSim
  venomExecSemantics stateEquivProps cfgTransform

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory

(* ================================================================
   Part 1: State Relation Definitions
   ================================================================ *)

(* Shared global/context state — the fields that are equal between
   callee and clone. Preserved by most operations. *)
Definition shared_globals_def:
  shared_globals (s1 : venom_state) (s2 : venom_state) <=>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_code = s2.vs_code /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes
End

(* Full clone relation: vars mapped through prefix, local fields
   correspond, globals shared. *)
Definition clone_rel_def:
  clone_rel (prefix : string) (labels : string list)
            (s_callee : venom_state) (s_clone : venom_state) <=>
    (!v. FLOOKUP s_clone.vs_vars (STRCAT prefix v) =
         FLOOKUP s_callee.vs_vars v) /\
    s_clone.vs_current_bb = STRCAT prefix s_callee.vs_current_bb /\
    s_clone.vs_prev_bb =
      OPTION_MAP (STRCAT prefix) s_callee.vs_prev_bb /\
    s_clone.vs_inst_idx = s_callee.vs_inst_idx /\
    s_clone.vs_halted = s_callee.vs_halted /\
    FDOM s_callee.vs_labels = {} /\
    FDOM s_clone.vs_labels = {} /\
    shared_globals s_callee s_clone
End

(* ================================================================
   Part 2: Preservation Lemmas
   ================================================================ *)

Theorem shared_globals_refl[simp]:
  !s. shared_globals s s
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_var:
  !s1 s2 v1 v2 w. shared_globals s1 s2 ==>
    shared_globals (update_var v1 w s1) (update_var v2 w s2)
Proof
  rw[shared_globals_def, update_var_def]
QED

Theorem shared_globals_jump_to:
  !s1 s2 l1 l2. shared_globals s1 s2 ==>
    shared_globals (jump_to l1 s1) (jump_to l2 s2)
Proof
  rw[shared_globals_def, jump_to_def]
QED

Theorem shared_globals_halt:
  !s1 s2. shared_globals s1 s2 ==>
    shared_globals (halt_state s1) (halt_state s2)
Proof
  rw[shared_globals_def, halt_state_def]
QED

Theorem shared_globals_revert:
  !s1 s2. shared_globals s1 s2 ==>
    shared_globals (revert_state s1) (revert_state s2)
Proof
  rw[shared_globals_def, revert_state_def]
QED

Theorem shared_globals_set_returndata:
  !s1 s2 rd. shared_globals s1 s2 ==>
    shared_globals (set_returndata rd s1) (set_returndata rd s2)
Proof
  rw[shared_globals_def, set_returndata_def]
QED

Theorem shared_globals_update_memory:
  !s1 s2 mem. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_memory := mem) (s2 with vs_memory := mem)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_logs:
  !s1 s2 logs. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_logs := logs) (s2 with vs_logs := logs)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_accounts:
  !s1 s2 a. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_accounts := a) (s2 with vs_accounts := a)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_transient:
  !s1 s2 tr. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_transient := tr) (s2 with vs_transient := tr)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_immutables:
  !s1 s2 imm. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_immutables := imm)
                   (s2 with vs_immutables := imm)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_returndata:
  !s1 s2 rd. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_returndata := rd) (s2 with vs_returndata := rd)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_allocas:
  !s1 s2 al1 al2. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_allocas := al1) (s2 with vs_allocas := al2)
Proof
  rw[shared_globals_def]
QED

Theorem shared_globals_update_alloca_next:
  !s1 s2 an. shared_globals s1 s2 ==>
    shared_globals (s1 with vs_alloca_next := an) (s2 with vs_alloca_next := an)
Proof
  rw[shared_globals_def]
QED

(* clone_rel preservation *)

(* All preservation lemmas: FDOM s_clone.vs_labels = {} follows from
   FDOM s_callee.vs_labels = {} + s_callee.vs_labels = s_clone.vs_labels
   (the latter from shared_globals). simp handles record updates,
   gvs substitutes the label equality. *)

Theorem clone_rel_update_var:
  !prefix labels s_callee s_clone v val.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (update_var v val s_callee)
      (update_var (STRCAT prefix v) val s_clone)
Proof
  simp[clone_rel_def, shared_globals_def, update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[FLOOKUP_UPDATE, STRCAT_11]
QED

Theorem clone_rel_jump_to:
  !prefix labels s_callee s_clone lbl.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (jump_to lbl s_callee)
      (jump_to (STRCAT prefix lbl) s_clone)
Proof
  simp[clone_rel_def, shared_globals_def, jump_to_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem clone_rel_halt:
  !prefix labels s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels (halt_state s_callee) (halt_state s_clone)
Proof
  simp[clone_rel_def, shared_globals_def, halt_state_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem clone_rel_revert:
  !prefix labels s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels (revert_state s_callee) (revert_state s_clone)
Proof
  simp[clone_rel_def, shared_globals_def, revert_state_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem clone_rel_set_returndata:
  !prefix labels s_callee s_clone rd.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (set_returndata rd s_callee) (set_returndata rd s_clone)
Proof
  simp[clone_rel_def, shared_globals_def, set_returndata_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_memory:
  !prefix labels s_callee s_clone mem.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_memory := mem) (s_clone with vs_memory := mem)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_logs:
  !prefix labels s_callee s_clone logs.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_logs := logs) (s_clone with vs_logs := logs)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_accounts:
  !prefix labels s_callee s_clone accts.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_accounts := accts)
      (s_clone with vs_accounts := accts)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_transient:
  !prefix labels s_callee s_clone tr.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_transient := tr) (s_clone with vs_transient := tr)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_immutables:
  !prefix labels s_callee s_clone imm.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_immutables := imm)
      (s_clone with vs_immutables := imm)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_returndata:
  !prefix labels s_callee s_clone rd.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_returndata := rd)
      (s_clone with vs_returndata := rd)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_allocas:
  !prefix labels s_callee s_clone al1 al2.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_allocas := al1) (s_clone with vs_allocas := al2)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_update_alloca_next:
  !prefix labels s_callee s_clone an.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_alloca_next := an) (s_clone with vs_alloca_next := an)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

Theorem clone_rel_inst_idx:
  !prefix labels s_callee s_clone n.
    clone_rel prefix labels s_callee s_clone ==>
    clone_rel prefix labels
      (s_callee with vs_inst_idx := n)
      (s_clone with vs_inst_idx := n)
Proof
  simp[clone_rel_def, shared_globals_def] >> rpt strip_tac >> gvs[]
QED

(* ================================================================
   Part 3: Operand Evaluation Correspondence
   ================================================================ *)

Theorem eval_operand_clone:
  !prefix labels op s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    eval_operand (clone_operand prefix labels op) s_clone =
    eval_operand op s_callee
Proof
  Cases_on `op` >>
  rw[clone_operand_def, eval_operand_def, lookup_var_def] >>
  gvs[clone_rel_def, shared_globals_def, FLOOKUP_DEF]
QED

Theorem eval_operands_clone_full:
  !ops prefix labels s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    eval_operands (MAP (clone_operand prefix labels) ops) s_clone =
    eval_operands ops s_callee
Proof
  Induct >> rw[eval_operands_def] >>
  imp_res_tac eval_operand_clone >> gvs[] >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  first_x_assum (qspecl_then [`prefix`,`labels`,`s_callee`,`s_clone`] mp_tac) >>
  simp[]
QED

(* clone_instruction helpers *)
Theorem clone_inst_opcode[simp]:
  (clone_instruction prefix labels inst).inst_opcode = inst.inst_opcode
Proof
  rw[clone_instruction_def]
QED

Theorem clone_inst_operands[simp]:
  (clone_instruction prefix labels inst).inst_operands =
  MAP (clone_operand prefix labels) inst.inst_operands
Proof
  rw[clone_instruction_def]
QED

Theorem clone_inst_outputs[simp]:
  (clone_instruction prefix labels inst).inst_outputs =
  MAP (\v. STRCAT prefix v) inst.inst_outputs
Proof
  rw[clone_instruction_def]
QED

(* ================================================================
   Part 4: Exec Helper Clone Lemmas
   ================================================================ *)

(* Helper: eval_operand succeeds implies var is defined *)
Theorem eval_operand_some_var_defined[local]:
  !op s v. eval_operand op s = SOME v ==>
    (!w. op = Var w ==> FLOOKUP s.vs_vars w <> NONE)
Proof
  Cases >> rw[eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars s'` >> gvs[]
QED

(* eval_operand on clone = eval_operand on original (corollaries) *)
Theorem eval_operand_clone_ok[local]:
  !prefix labels op s_callee s_clone v.
    clone_rel prefix labels s_callee s_clone /\
    eval_operand op s_callee = SOME v ==>
    eval_operand (clone_operand prefix labels op) s_clone = SOME v
Proof
  rpt strip_tac >> imp_res_tac eval_operand_clone >> gvs[]
QED

(* Uniform proof pattern for exec_* full clone lemmas:
   1. Expand def + clone_instruction_def
   2. Case on inst.inst_operands to match arity
   3. Use eval_operand_clone to rewrite clone-side evals
   4. Case on eval results + outputs
   5. clone_rel_update_var at OK leaves *)

Theorem exec_pure1_clone:
  !f prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    case exec_pure1 f inst s_callee of
      OK sc => ?sc'.
        exec_pure1 f (clone_instruction prefix labels inst) s_clone =
        OK sc' /\ clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_pure1 f (clone_instruction prefix labels inst) s_clone =
        Error e'
    | _ => T
Proof
  rpt strip_tac >> simp[exec_pure1_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem exec_pure2_clone:
  !f prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    case exec_pure2 f inst s_callee of
      OK sc => ?sc'.
        exec_pure2 f (clone_instruction prefix labels inst) s_clone =
        OK sc' /\ clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_pure2 f (clone_instruction prefix labels inst) s_clone =
        Error e'
    | _ => T
Proof
  rpt strip_tac >> simp[exec_pure2_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem exec_pure3_clone:
  !f prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone ==>
    case exec_pure3 f inst s_callee of
      OK sc => ?sc'.
        exec_pure3 f (clone_instruction prefix labels inst) s_clone =
        OK sc' /\ clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_pure3 f (clone_instruction prefix labels inst) s_clone =
        Error e'
    | _ => T
Proof
  rpt strip_tac >> simp[exec_pure3_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  `eval_operand (clone_operand prefix labels h'') s_clone =
   eval_operand h'' s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[] >>
  Cases_on `eval_operand h'' s_callee` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem exec_read0_clone:
  !f prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    (!s1 s2. shared_globals s1 s2 ==> f s1 = f s2) ==>
    case exec_read0 f inst s_callee of
      OK sc => ?sc'.
        exec_read0 f (clone_instruction prefix labels inst) s_clone =
        OK sc' /\ clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_read0 f (clone_instruction prefix labels inst) s_clone =
        Error e'
    | _ => T
Proof
  rpt strip_tac >> simp[exec_read0_def, clone_instruction_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `f s_callee = f s_clone` by
    (first_x_assum irule >> gvs[clone_rel_def]) >>
  gvs[] >> irule clone_rel_update_var >> simp[]
QED

Theorem exec_read1_clone:
  !f prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    (!v s1 s2. shared_globals s1 s2 ==> f v s1 = f v s2) ==>
    case exec_read1 f inst s_callee of
      OK sc => ?sc'.
        exec_read1 f (clone_instruction prefix labels inst) s_clone =
        OK sc' /\ clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_read1 f (clone_instruction prefix labels inst) s_clone =
        Error e'
    | _ => T
Proof
  rpt strip_tac >> simp[exec_read1_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  `f x s_callee = f x s_clone` by
    (first_x_assum irule >> gvs[clone_rel_def]) >>
  gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  irule clone_rel_update_var >> simp[]
QED

Theorem exec_write2_clone:
  !f prefix labels inst s_callee s_clone.
    clone_rel prefix labels s_callee s_clone /\
    (!v1 v2 s1 s2. clone_rel prefix labels s1 s2 ==>
       clone_rel prefix labels (f v1 v2 s1) (f v1 v2 s2)) ==>
    case exec_write2 f inst s_callee of
      OK sc => ?sc'.
        exec_write2 f (clone_instruction prefix labels inst) s_clone =
        OK sc' /\ clone_rel prefix labels sc sc'
    | Error e => ?e'.
        exec_write2 f (clone_instruction prefix labels inst) s_clone =
        Error e'
    | _ => T
Proof
  rpt strip_tac >> simp[exec_write2_def, clone_instruction_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  `eval_operand (clone_operand prefix labels h) s_clone =
   eval_operand h s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  `eval_operand (clone_operand prefix labels h') s_clone =
   eval_operand h' s_callee` by
    (irule eval_operand_clone >> gvs[]) >>
  Cases_on `eval_operand h s_callee` >> gvs[] >>
  Cases_on `eval_operand h' s_callee` >> gvs[]
QED

(* ===== FOLDL inline preserves fn_names ===== *)

Triviality foldl_inline_names:
  !fns acc ist0 callee fns' ist1.
    FOLDL (\(fns_acc, st) caller_fn.
      let max_sites = LENGTH (fn_insts caller_fn) in
      let (caller', st') = inline_at_sites max_sites caller_fn callee st in
      (SNOC caller' fns_acc, st'))
      (acc, ist0) fns = (fns', ist1) ==>
    MAP (\f. f.fn_name) fns' =
    MAP (\f. f.fn_name) acc ++ MAP (\f. f.fn_name) fns
Proof
  Induct_on `fns` >> rw[] >> gvs[] >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac inline_at_sites_fn_name >>
  gvs[MAP_SNOC, SNOC_APPEND]
QED

val _ = export_theory();

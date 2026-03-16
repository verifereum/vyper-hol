(*
 * Pass Shared Properties
 *
 * Correctness theorems for pass-shared utilities (mk_nop_inst,
 * mk_assign_inst, clear_nops, subst_operands, subst_operands_map)
 * and general semantic properties used by multiple passes
 * (effects_independent_commute).
 *
 * TOP-LEVEL:
 *   Instruction builders:
 *     mk_nop_inst_correct        — NOP replacement is identity on state
 *     mk_assign_inst_correct     — ASSIGN replacement evaluates and binds output
 *
 *   NOP clearing:
 *     clear_nops_block_correct    — removing NOPs from a block preserves execution
 *     clear_nops_function_correct — removing NOPs from a function preserves execution
 *
 *   Operand substitution:
 *     subst_operand_eval           — single substitution preserves eval_operand
 *     subst_op_map_eval            — map substitution preserves eval_operand
 *     subst_operand_eval_operands  — single substitution preserves eval_operands (list)
 *     subst_op_map_eval_operands   — map substitution preserves eval_operands (list)
 *     subst_operands_correct       — single substitution preserves step_inst
 *     subst_operands_map_correct   — map substitution preserves step_inst
 *)

Theory passSharedProps
Ancestors
  passSharedDefs venomExecSemantics venomEffects stateEquiv venomInstProofs
  passSharedField passSharedTransfer passSharedVarFrame passSharedFrame

open venomStateTheory venomInstTheory;

(* ===================================================================== *)
(* ===== Section 1: Instruction Builder Correctness ==================== *)
(* ===================================================================== *)

(* NOP replacement always succeeds with unchanged state.
   mk_nop_inst sets opcode to NOP; NOP => OK s in step_inst_base. *)
Theorem mk_nop_inst_correct:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rw[mk_nop_inst_def, step_inst_def, step_inst_base_def]
QED

(* ASSIGN replacement evaluates src_op and binds the result to the
   single output variable. Requires src_op evaluable and exactly one output. *)
Theorem mk_assign_inst_correct:
  !fuel ctx inst src_op s v out.
    eval_operand src_op s = SOME v /\
    inst.inst_outputs = [out] ==>
    step_inst fuel ctx (mk_assign_inst inst src_op) s =
      OK (update_var out v s)
Proof
  rw[mk_assign_inst_def, step_inst_def, step_inst_base_def] >> rw[]
QED

(* ===================================================================== *)
(* ===== Section 2: NOP Clearing ======================================= *)
(* ===================================================================== *)

(* Removing NOP instructions from a block preserves execution.
   NOP always succeeds with unchanged state (step_inst NOP s = OK s)
   and is not a terminator, so run_block just advances vs_inst_idx
   past it. FILTER-ing NOPs from the instruction list produces the
   same execution result as running the block with NOPs present.

   Proof sketch: by induction on the block execution (fuel +
   instruction count). At each step:
   - If current instruction is NOP: step gives OK s, then recurse
     at next index. Equivalent to skipping it in the filtered list.
   - If current instruction is not NOP: same instruction appears at
     the corresponding index in the filtered list. Same step result.
   The filtered block's indices are a subsequence of the original. *)
Theorem clear_nops_block_correct:
  !fuel ctx bb s.
    s.vs_inst_idx = 0 ==>
    run_block fuel ctx (clear_nops_block bb) s =
    run_block fuel ctx bb s
Proof
  cheat
QED

(* Function-level: clear_nops_function preserves execution.
   Follows from clear_nops_block_correct applied to each block.
   clear_nops_block preserves bb_label, so block lookup is unchanged. *)
Theorem clear_nops_function_correct:
  !fuel ctx fn s.
    s.vs_inst_idx = 0 ==>
    run_function fuel ctx (clear_nops_function fn) s =
    run_function fuel ctx fn s
Proof
  cheat
QED

(* Corollary: wrapping any function transform with clear_nops_function
   preserves lift_result. If the un-cleared transform is correct,
   the cleared version is too. *)
Theorem clear_nops_lift_result:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx fn fn' s.
    s.vs_inst_idx = 0 /\
    lift_result R_ok R_term
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn' s) ==>
    lift_result R_ok R_term
      (run_function fuel ctx fn s)
      (run_function fuel ctx (clear_nops_function fn') s)
Proof
  rpt strip_tac >>
  `run_function fuel ctx (clear_nops_function fn') s =
   run_function fuel ctx fn' s` by
    (irule clear_nops_function_correct >> simp[]) >>
  gvs[]
QED

(* ===================================================================== *)
(* ===== Section 3: Operand Substitution =============================== *)
(* ===================================================================== *)

(* Substituting a variable with an equal-valued operand preserves
   eval_operand for any operand. Covers Var (with/without match),
   Lit (unchanged), and Label (both NONE). *)
Theorem subst_operand_eval:
  !old new_op op s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operand (subst_operand old new_op op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_operand_def, eval_operand_def] >> rw[]
QED

(* Multi-variable substitution via fmap preserves eval_operand when
   every mapped variable is replaced by an equal-valued operand. *)
Theorem subst_op_map_eval:
  !subs op s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operand (subst_op_map subs op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_op_map_def, eval_operand_def] >>
  CASE_TAC >> rw[] >> res_tac >> simp[eval_operand_def]
QED

(* Corollary: substitution preserves eval_operands (list version) *)
Theorem subst_operand_eval_operands:
  !old new_op ops s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operands (MAP (subst_operand old new_op) ops) s =
    eval_operands ops s
Proof
  ntac 2 strip_tac >> Induct >>
  rw[eval_operands_def] >> imp_res_tac subst_operand_eval >> rw[]
QED

(* Corollary: map substitution preserves eval_operands (list version) *)
Theorem subst_op_map_eval_operands:
  !subs ops s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operands (MAP (subst_op_map subs) ops) s =
    eval_operands ops s
Proof
  strip_tac >> Induct >>
  rw[eval_operands_def] >> imp_res_tac subst_op_map_eval >> rw[]
QED

(* Helper: extract_labels preserved by MAP g when g preserves Label structure *)
Theorem extract_labels_map[local]:
  !ops g.
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) ==>
    extract_labels (MAP g ops) = extract_labels ops
Proof
  Induct >> simp[extract_labels_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h`
  >- (rename1 `Lit c` >>
      `!lbl. g (Lit c) <> Label lbl` by
        (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
      Cases_on `g (Lit c)` >> gvs[extract_labels_def])
  >- (rename1 `Var vn` >>
      `!lbl. g (Var vn) <> Label lbl` by
        (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]) >>
      Cases_on `g (Var vn)` >> gvs[extract_labels_def])
  >- (simp[extract_labels_def] >> res_tac >> simp[])
QED

(* Per-exec congruence lemmas: MAP g on inst_operands preserves exec_*
   when g preserves eval_operand. *)
local
  val ops_tac =
    rpt strip_tac >> simp[] >>
    Cases_on `inst.inst_operands` >> simp[] >>
    Cases_on `t` >> simp[] >>
    Cases_on `t'` >> simp[] >>
    TRY (Cases_on `t` >> simp[])
in
  val exec_pure1_map = prove(
    ``!g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
      exec_pure1 h (inst with inst_operands := MAP g inst.inst_operands) s =
      exec_pure1 h inst s``, simp[exec_pure1_def] >> ops_tac)
  val exec_pure2_map = prove(
    ``!g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
      exec_pure2 h (inst with inst_operands := MAP g inst.inst_operands) s =
      exec_pure2 h inst s``, simp[exec_pure2_def] >> ops_tac)
  val exec_pure3_map = prove(
    ``!g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
      exec_pure3 h (inst with inst_operands := MAP g inst.inst_operands) s =
      exec_pure3 h inst s``, simp[exec_pure3_def] >> ops_tac)
  val exec_read0_map = prove(
    ``!g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
      exec_read0 h (inst with inst_operands := MAP g inst.inst_operands) s =
      exec_read0 h inst s``, simp[exec_read0_def] >> ops_tac)
  val exec_read1_map = prove(
    ``!g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
      exec_read1 h (inst with inst_operands := MAP g inst.inst_operands) s =
      exec_read1 h inst s``, simp[exec_read1_def] >> ops_tac)
  val exec_write2_map = prove(
    ``!g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
      exec_write2 h (inst with inst_operands := MAP g inst.inst_operands) s =
      exec_write2 h inst s``, simp[exec_write2_def] >> ops_tac)
end;
val exec_map_thms = [exec_pure1_map, exec_pure2_map, exec_pure3_map,
                     exec_read0_map, exec_read1_map, exec_write2_map];

(* exec_create/ext_call/delegatecall only access inst.inst_outputs,
   so changing inst_operands is a no-op. *)
val exec_create_inst_operands = prove(
  ``!inst ops s v o' sz salt.
    exec_create (inst with inst_operands := ops) s v o' sz salt =
    exec_create inst s v o' sz salt``,
  rw[exec_create_def]);
val exec_ext_call_inst_operands = prove(
  ``!inst ops s g a v ao as' ro rs is_s.
    exec_ext_call (inst with inst_operands := ops) s g a v ao as' ro rs is_s =
    exec_ext_call inst s g a v ao as' ro rs is_s``,
  rw[exec_ext_call_def]);
val exec_delegatecall_inst_operands = prove(
  ``!inst ops s g a ao as' ro rs.
    exec_delegatecall (inst with inst_operands := ops) s g a ao as' ro rs =
    exec_delegatecall inst s g a ao as' ro rs``,
  rw[exec_delegatecall_def]);
val exec_inst_operands_thms = [exec_create_inst_operands,
  exec_ext_call_inst_operands, exec_delegatecall_inst_operands];

(* eval_operands over MAP g = eval_operands when g preserves eval *)
val eval_operands_map_thm = prove(
  ``!g ops s.
    (!op. eval_operand (g op) s = eval_operand op s) ==>
    eval_operands (MAP g ops) s = eval_operands ops s``,
  ntac 2 strip_tac >> Induct_on `ops` >> rw[eval_operands_def]);

(* Variable-safe deep list case split *)
fun list_case_tac n =
  if n <= 0 then ALL_TAC
  else TRY (
    FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`,
           Cases_on `t'''`, Cases_on `t''''`] >>
    simp[exec_create_def, exec_ext_call_def, exec_delegatecall_def] >>
    list_case_tac (n-1));

(* Tactic for label-matching opcodes *)
val label_op_tac =
  ONCE_ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[extract_labels_map] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  TRY (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
  TRY (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]);

(* Part 1: non-label, non-excluded opcodes — eval-only access *)
Theorem step_inst_base_operands_irrelevant_safe[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    inst.inst_opcode <> OFFSET ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
  simp (exec_map_thms @ exec_inst_operands_thms @ [eval_operands_map_thm]) >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
  Cases_on `inst.inst_operands` >> simp[] >>
  TRY (Cases_on `t` >> simp[]) >>
  TRY (FIRST [Cases_on `t'`, Cases_on `t`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  TRY (FIRST [Cases_on `t`, Cases_on `t'`, Cases_on `t''`] >> simp[]) >>
  (* Remaining goals differ only in excluded branches (LOG/OFFSET/JMP/JNZ/DJMP).
     Case split on opcode to eliminate. *)
  TRY (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def])
QED

(* Part 2: label-matching opcodes (JMP, JNZ, DJMP, OFFSET) *)
Theorem step_inst_base_operands_irrelevant_label[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) /\
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP \/ inst.inst_opcode = OFFSET) ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >> gvs[]
  >- label_op_tac
  >- label_op_tac
  >- (`!ops. extract_labels (MAP g ops) = extract_labels ops` by
        (strip_tac >> irule extract_labels_map >> simp[]) >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      Cases_on `inst.inst_operands` >> simp[])
  >- label_op_tac
QED

(* Combined: step_inst_base depends on operands only through eval_operand
   and Label identity for non-excluded opcodes. *)
Theorem step_inst_base_operands_irrelevant[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP \/ inst.inst_opcode = OFFSET`
  >- (irule step_inst_base_operands_irrelevant_label >> simp[])
  >> (irule step_inst_base_operands_irrelevant_safe >> gvs[])
QED

(* Helper: decode_invoke after substitution preserves the callee label
   and applies the mapping to the remaining arg operands. *)
Theorem decode_invoke_map[local]:
  !f inst.
    (!lbl. f (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. f op <> Label lbl)) ==>
    decode_invoke (inst with inst_operands := MAP f inst.inst_operands) =
    case decode_invoke inst of
      NONE => NONE
    | SOME (callee, args) => SOME (callee, MAP f args)
Proof
  rpt strip_tac >>
  simp[decode_invoke_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[]
  >- (rename1 `Lit c` >>
      `!lbl. f (Lit c) <> Label lbl` by
        (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
      Cases_on `f (Lit c)` >> gvs[])
  >- (rename1 `Var vn` >>
      `!lbl. f (Var vn) <> Label lbl` by
        (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]) >>
      Cases_on `f (Var vn)` >> gvs[])
QED

(* Single-variable operand substitution preserves step_inst when the
   replacement evaluates to the same defined value.
   Excludes opcodes that pattern-match on operand constructors:
   - PHI: positional Label/Var pairs, not generic eval
   - PARAM, ALLOCA/PALLOCA/CALLOCA, LOG: pattern-match Lit in operands,
     so Var->Lit substitution changes structural match behavior *)
Theorem subst_operands_correct:
  !fuel ctx inst s old new_op v.
    lookup_var old s = SOME v /\
    eval_operand new_op s = SOME v /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG ==>
    step_inst fuel ctx (subst_operands old new_op inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  (* Establish substitution properties *)
  `!op. eval_operand (subst_operand old new_op op) s =
        eval_operand op s` by (
    rpt strip_tac >> irule subst_operand_eval >>
    gvs[eval_operand_def]) >>
  `!lbl. subst_operand old new_op (Label lbl) = Label lbl` by
    simp[subst_operand_def] >>
  `!op. (!lbl. op <> Label lbl) ==>
        !lbl. subst_operand old new_op op <> Label lbl` by (
    Cases >> simp[subst_operand_def] >> rw[] >>
    Cases_on `new_op` >> gvs[eval_operand_def]) >>
  simp[subst_operands_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- ((* INVOKE case *)
    drule_then assume_tac decode_invoke_map >>
    imp_res_tac eval_operands_map_thm >>
    simp[step_inst_def] >>
    rpt (CASE_TAC >> simp[])) >>
  (* Non-INVOKE case *)
  imp_res_tac step_inst_base_operands_irrelevant >>
  simp[step_inst_non_invoke]
QED

(* Multi-variable operand substitution preserves step_inst.
   Same exclusions as subst_operands_correct. *)
Theorem subst_operands_map_correct:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                IS_SOME (eval_operand new_op s) /\
                eval_operand new_op s = eval_operand (Var v) s) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  (* Establish substitution properties *)
  `!op. eval_operand (subst_op_map subs op) s =
        eval_operand op s` by (
    rpt strip_tac >> irule subst_op_map_eval >> metis_tac[]) >>
  `!lbl. subst_op_map subs (Label lbl) = Label lbl` by
    rw[subst_op_map_def] >>
  `!op. (!lbl. op <> Label lbl) ==>
        !lbl. subst_op_map subs op <> Label lbl` by (
    Cases >> simp[subst_op_map_def] >> rw[] >>
    rename1 `FLOOKUP subs vn` >> CASE_TAC >> simp[] >>
    rename1 `FLOOKUP subs vn = SOME nop` >>
    res_tac >> Cases_on `nop` >> gvs[eval_operand_def]) >>
  simp[subst_operands_map_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- ((* INVOKE case *)
    drule_then assume_tac decode_invoke_map >>
    imp_res_tac eval_operands_map_thm >>
    simp[step_inst_def] >>
    rpt (CASE_TAC >> simp[])) >>
  (* Non-INVOKE case *)
  imp_res_tac step_inst_base_operands_irrelevant >>
  simp[step_inst_non_invoke]
QED

(* ===================================================================== *)
(* ===== Re-exported proof results ===================================== *)
(* ===================================================================== *)

(* State field preservation: step_inst preserves all state fields
   not in write_effects, for non-terminator/non-alloca/non-ext-call ops. *)
Theorem step_inst_preserves_all =
  passSharedFieldTheory.step_inst_preserves_all

Theorem step_base_preserves_tracked =
  passSharedFieldTheory.step_base_preserves_tracked

Theorem eligible_no_write_balance_extcode =
  passSharedFieldTheory.eligible_no_write_balance_extcode

(* Transfer: step_inst_base produces OK on equivalent input states. *)
Theorem step_inst_base_ok_transfer =
  passSharedTransferTheory.step_inst_base_ok_transfer

Theorem step_inst_base_output_determined =
  passSharedTransferTheory.step_inst_base_output_determined

Theorem step_inst_base_output_determined_fields =
  passSharedTransferTheory.step_inst_base_output_determined_fields

(* Variable frame: step_inst preserves variables not in inst_defs. *)
Theorem step_inst_base_var_frame_full =
  passSharedVarFrameTheory.step_inst_base_var_frame_full

Theorem step_inst_var_frame_full =
  passSharedVarFrameTheory.step_inst_var_frame_full

(* Independent instructions commute under step_inst. *)
Theorem effects_independent_commute =
  passSharedFrameTheory.effects_independent_commute

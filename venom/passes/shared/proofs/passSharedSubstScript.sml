(*
 * Pass Shared Operand Substitution Proofs
 *
 * Proves that operand substitution (single-variable and fmap-based)
 * preserves step_inst semantics.
 *
 * TOP-LEVEL:
 *   subst_operand_eval           — single substitution preserves eval_operand
 *   subst_op_map_eval            — map substitution preserves eval_operand
 *   subst_operand_eval_operands  — single substitution preserves eval_operands
 *   subst_op_map_eval_operands   — map substitution preserves eval_operands
 *   subst_operands_correct       — single substitution preserves step_inst
 *   subst_operands_map_correct   — map substitution preserves step_inst
 *)

Theory passSharedSubst
Ancestors
  passSharedDefs venomExecSemantics venomWf

open venomStateTheory venomInstTheory;

(* ===================================================================== *)
(* ===== Operand eval preservation ===================================== *)
(* ===================================================================== *)

Theorem subst_operand_eval:
  !old new_op op s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operand (subst_operand old new_op op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_operand_def, eval_operand_def] >> rw[]
QED

Theorem subst_op_map_eval:
  !subs op s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operand (subst_op_map subs op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_op_map_def, eval_operand_def] >>
  CASE_TAC >> rw[] >> res_tac >> simp[eval_operand_def]
QED

Theorem subst_operand_eval_operands:
  !old new_op ops s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operands (MAP (subst_operand old new_op) ops) s =
    eval_operands ops s
Proof
  ntac 2 strip_tac >> Induct >>
  rw[eval_operands_def] >> imp_res_tac subst_operand_eval >> rw[]
QED

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

(* ===================================================================== *)
(* ===== step_inst_base operand irrelevance ============================ *)
(* ===================================================================== *)

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

val eval_operands_map_thm = prove(
  ``!g ops s.
    (!op. eval_operand (g op) s = eval_operand op s) ==>
    eval_operands (MAP g ops) s = eval_operands ops s``,
  ntac 2 strip_tac >> Induct_on `ops` >> rw[eval_operands_def]);

val label_op_tac =
  ONCE_ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[extract_labels_map] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  TRY (first_x_assum (qspec_then `Lit c` mp_tac) >> simp[]) >>
  TRY (first_x_assum (qspec_then `Var vn` mp_tac) >> simp[]);

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
  TRY (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def])
QED

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

(* ===================================================================== *)
(* ===== INVOKE decode helper ========================================== *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(* ===== step_inst substitution correctness ============================ *)
(* ===================================================================== *)

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
  >- (drule_then assume_tac decode_invoke_map >>
      imp_res_tac eval_operands_map_thm >>
      simp[step_inst_def] >>
      rpt (CASE_TAC >> simp[])) >>
  imp_res_tac step_inst_base_operands_irrelevant >>
  simp[step_inst_non_invoke]
QED

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
  >- (drule_then assume_tac decode_invoke_map >>
      imp_res_tac eval_operands_map_thm >>
      simp[step_inst_def] >>
      rpt (CASE_TAC >> simp[])) >>
  imp_res_tac step_inst_base_operands_irrelevant >>
  simp[step_inst_non_invoke]
QED

(* Helper: subst_op_map preserves all-Label lists (from inst_wf DJMP) *)
Triviality subst_op_map_preserves_labels:
  !ops subs. EVERY (\op. IS_SOME (get_label op)) ops ==>
    MAP (subst_op_map subs) ops = ops
Proof
  Induct >> rw[] >> Cases_on `h` >> gvs[get_label_def, subst_op_map_def]
QED

(* Helper: if MAP (subst_op_map subs) preserves operands, subst is identity *)
Triviality subst_operands_map_id:
  !subs inst. MAP (subst_op_map subs) inst.inst_operands = inst.inst_operands ==>
    subst_operands_map subs inst = inst
Proof
  rw[subst_operands_map_def] >> Cases_on `inst` >>
  gvs[venomInstTheory.instruction_fn_updates,
      venomInstTheory.instruction_accessors]
QED

(* Stronger version: inst_wf handles structural positions, only PHI excluded.
   Strategy: structural opcodes (PARAM, ALLOCA, PALLOCA, CALLOCA, LOG,
   JMP, JNZ, DJMP, OFFSET, INVOKE) handled by inst_wf + definition unfolding.
   All other non-PHI opcodes handled by step_inst_base_operands_irrelevant_safe
   (which only needs eval_operand equivalence). *)
Theorem subst_operands_map_correct_wf:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) /\
    inst_wf inst /\
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `!op. eval_operand (subst_op_map subs op) s =
        eval_operand op s` by
    (rpt strip_tac >> irule subst_op_map_eval >> metis_tac[]) >>
  (* Non-structural opcodes *)
  Cases_on `inst.inst_opcode <> PARAM /\
            ~is_alloca_op inst.inst_opcode /\
            inst.inst_opcode <> LOG /\
            inst.inst_opcode <> JMP /\
            inst.inst_opcode <> JNZ /\
            inst.inst_opcode <> DJMP /\
            inst.inst_opcode <> OFFSET /\
            inst.inst_opcode <> INVOKE`
  >- (simp[subst_operands_map_def, step_inst_non_invoke] >>
      irule step_inst_base_operands_irrelevant_safe >> gvs[])
  >>
  (* Structural: inst_wf resolves operand shapes *)
  gvs[is_alloca_op_def] >> gvs[inst_wf_def] >>
  (* Trivial: all Lit/Label operands => subst is identity *)
  TRY (`subst_operands_map subs inst = inst` by
         (irule subst_operands_map_id >> simp[subst_op_map_def]) >>
       simp[] >> NO_TAC) >>
  gvs[subst_operands_map_def, subst_op_map_def] >|
  [(* CALLOCA: resolve is_alloca_op *)
   `inst.inst_opcode = ALLOCA \/ inst.inst_opcode = PALLOCA \/
    inst.inst_opcode = CALLOCA` by
     (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
   gvs[inst_wf_def, subst_op_map_def, step_inst_def, exec_alloca_def] >>
   simp[Once step_inst_base_def, SimpLHS] >>
   simp[Once step_inst_base_def, SimpRHS] >> simp[exec_alloca_def],
   (* LOG *)
   `rest <> []` by (Cases_on `rest` >> gvs[]) >>
   simp[step_inst_non_invoke] >>
   simp[Once step_inst_base_def] >>
   simp[Once step_inst_base_def] >>
   simp[GSYM listTheory.MAP_DROP, listTheory.EL_MAP,
        rich_listTheory.MAP_HD] >>
   `eval_operands (MAP (subst_op_map subs) (DROP 2 rest)) s =
    eval_operands (DROP 2 rest) s` by
     (irule eval_operands_map_thm >> metis_tac[]) >> simp[],
   (* JNZ *)
   simp[step_inst_non_invoke] >>
   simp[Once step_inst_base_def] >>
   simp[Once step_inst_base_def],
   (* DJMP *)
   imp_res_tac subst_op_map_preserves_labels >>
   simp[step_inst_non_invoke] >>
   simp[Once step_inst_base_def] >>
   simp[Once step_inst_base_def],
   (* OFFSET *)
   simp[step_inst_non_invoke] >>
   simp[Once step_inst_base_def] >>
   simp[Once step_inst_base_def],
   (* INVOKE *)
   simp[step_inst_def, decode_invoke_def] >>
   `eval_operands (MAP (subst_op_map subs) args) s =
    eval_operands args s` by
     (irule eval_operands_map_thm >> metis_tac[]) >>
   simp[] >> rpt (CASE_TAC >> simp[])
  ]
QED

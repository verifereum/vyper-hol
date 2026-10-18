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
  passSharedDefs venomExecSemantics venomWf venomState venomInst
Libs
  listTheory rich_listTheory

(* ===================================================================== *)
(* ===== Operand eval preservation ===================================== *)
(* ===================================================================== *)

Theorem subst_operand_eval:
  !old new_op op s.
    eval_operand new_op s = eval_operand (Var old) s ==>
    eval_operand (subst_operand old new_op op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_operand_def, eval_operand_def]
QED

Theorem subst_op_map_eval:
  !subs op s.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) ==>
    eval_operand (subst_op_map subs op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[subst_op_map_def, eval_operand_def] >>
  rename1 `FLOOKUP subs vn` >>
  Cases_on `FLOOKUP subs vn` >> rw[] >> res_tac >> simp[eval_operand_def]
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

val ops_tac =
  rpt strip_tac >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  TRY (Cases_on `t` >> simp[]);

Triviality exec_pure1_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_pure1 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_pure1 h inst s
Proof simp[exec_pure1_def] >> ops_tac
QED
Triviality exec_pure2_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_pure2 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_pure2 h inst s
Proof simp[exec_pure2_def] >> ops_tac
QED
Triviality exec_pure3_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_pure3 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_pure3 h inst s
Proof simp[exec_pure3_def] >> ops_tac
QED
Triviality exec_read0_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_read0 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_read0 h inst s
Proof simp[exec_read0_def] >> ops_tac
QED
Triviality exec_read1_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_read1 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_read1 h inst s
Proof simp[exec_read1_def] >> ops_tac
QED
Triviality exec_write2_map[local]:
  !g h inst s. (!op. eval_operand (g op) s = eval_operand op s) ==>
    exec_write2 h (inst with inst_operands := MAP g inst.inst_operands) s =
    exec_write2 h inst s
Proof simp[exec_write2_def] >> ops_tac
QED

val exec_map_thms = [exec_pure1_map, exec_pure2_map, exec_pure3_map,
                     exec_read0_map, exec_read1_map, exec_write2_map];

(* ===================================================================== *)
(* ===== Positional operand equivalence ================================ *)
(* ===================================================================== *)

(* Per-element eval_operand agreement implies eval_operands agreement *)
Theorem eval_operands_positional:
  !ops1 ops2 st. LENGTH ops1 = LENGTH ops2 /\
    (!i. i < LENGTH ops1 ==>
         eval_operand (EL i ops1) st = eval_operand (EL i ops2) st) ==>
    eval_operands ops1 st = eval_operands ops2 st
Proof
  Induct >> simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `ops2` >> gvs[eval_operands_def] >>
  `eval_operand h st = eval_operand h' st` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `eval_operands ops1 st = eval_operands t st` by (
    first_x_assum irule >> simp[] >>
    rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[]
QED

(* Positional exec_* thms: arbitrary new_ops with per-element eval agreement.
   Only operand-list shape matters: rewrite the three observed evaluations
   directly, without splitting evaluation results or instruction outputs. *)
val exec_pos_ss = bool_ss ++ numSimps.REDUCE_ss ++ numSimps.ARITH_RWTS_ss ++
  rewrites [numTheory.NOT_SUC, GSYM numTheory.NOT_SUC,
    LENGTH, EL, EL_simp_restricted, HD, TL, list_case_def,
    instruction_accfupds, combinTheory.K_THM];

fun exec_pos_prove def = let
  val simplify = full_simp_tac (exec_pos_ss ++ rewrites [def]) []
  val indices = map (numSyntax.mk_numeral o Arbnum.fromInt) [0, 1, 2]
  val finish =
    qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
      (fn th => MAP_EVERY (fn i => assume_tac (SPEC i th)) indices) >>
    simplify
  fun operand_case tm =
    #3 (listSyntax.dest_list_case (find_term (fn t =>
      listSyntax.is_list_case t andalso
      type_of (#3 (listSyntax.dest_list_case t)) = ``:operand list``) tm))
  fun split_ops (asl, goal) =
    case total (fn t => (operand_case (lhs t), operand_case (rhs t))) goal of
      NONE => finish (asl, goal)
    | SOME (xs, ys) =>
        (Cases_on [ANTIQUOTE xs] >> Cases_on [ANTIQUOTE ys] >>
         simplify >> split_ops) (asl, goal)
in
  rpt gen_tac >> strip_tac >> simplify >> split_ops
end;

Triviality exec_pure1_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_pure1 f (inst with inst_operands := new_ops) st = exec_pure1 f inst st
Proof
  exec_pos_prove exec_pure1_def
QED

Triviality exec_pure2_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_pure2 f (inst with inst_operands := new_ops) st = exec_pure2 f inst st
Proof
  exec_pos_prove exec_pure2_def
QED

Triviality exec_pure3_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_pure3 f (inst with inst_operands := new_ops) st = exec_pure3 f inst st
Proof
  exec_pos_prove exec_pure3_def
QED

Triviality exec_read0_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_read0 f (inst with inst_operands := new_ops) st = exec_read0 f inst st
Proof
  exec_pos_prove exec_read0_def
QED

Triviality exec_read1_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_read1 f (inst with inst_operands := new_ops) st = exec_read1 f inst st
Proof
  exec_pos_prove exec_read1_def
QED

Triviality exec_write2_pos[local]:
  !f inst new_ops st.
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    exec_write2 f (inst with inst_operands := new_ops) st = exec_write2 f inst st
Proof
  exec_pos_prove exec_write2_def
QED

val exec_pos_thms = [exec_pure1_pos, exec_pure2_pos, exec_pure3_pos,
                     exec_read0_pos, exec_read1_pos, exec_write2_pos];

Triviality exec_create_inst_operands[local]:
  !inst ops s v o' sz salt.
    exec_create (inst with inst_operands := ops) s v o' sz salt =
    exec_create inst s v o' sz salt
Proof rw[exec_create_def]
QED
Triviality exec_ext_call_inst_operands[local]:
  !inst ops s g a v ao as' ro rs is_s.
    exec_ext_call (inst with inst_operands := ops) s g a v ao as' ro rs is_s =
    exec_ext_call inst s g a v ao as' ro rs is_s
Proof rw[exec_ext_call_def]
QED
Triviality exec_delegatecall_inst_operands[local]:
  !inst ops s g a ao as' ro rs.
    exec_delegatecall (inst with inst_operands := ops) s g a ao as' ro rs =
    exec_delegatecall inst s g a ao as' ro rs
Proof rw[exec_delegatecall_def]
QED

val exec_inst_operands_thms = [exec_create_inst_operands,
  exec_ext_call_inst_operands, exec_delegatecall_inst_operands];

Triviality eval_operands_map_thm[local]:
  !g ops s.
    (!op. eval_operand (g op) s = eval_operand op s) ==>
    eval_operands (MAP g ops) s = eval_operands ops s
Proof
  ntac 2 strip_tac >> Induct_on `ops` >> rw[eval_operands_def]
QED

(* Dispatch/shape filtering must not unfold operand evaluation or semantic
   bodies. Cache this small simpset for the sibling opcode case proofs. *)
val opcode_filter_ss = bool_ss ++ numSimps.REDUCE_ss ++
  numSimps.ARITH_RWTS_ss ++ simpLib.type_ssfrag ``:opcode`` ++ rewrites
    [is_alloca_op_def, LENGTH];
val opcode_filter_tac = full_simp_tac opcode_filter_ss [];

val opcode_cases_tac =
  Cases_on `inst.inst_opcode` >> opcode_filter_tac;


Theorem parse_dret_shape_subst_operand[local]:
  !old new_op inst.
    IS_SOME (parse_dret_shape inst) ==>
    parse_dret_shape
      (inst with inst_operands :=
         MAP (subst_operand old new_op) inst.inst_operands) =
    parse_dret_shape inst
Proof
  rpt strip_tac >> Cases_on `inst.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >> Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_operand_def]
QED

Theorem parse_dret_shape_subst_op_map[local]:
  !subs inst.
    IS_SOME (parse_dret_shape inst) ==>
    parse_dret_shape
      (inst with inst_operands := MAP (subst_op_map subs) inst.inst_operands) =
    parse_dret_shape inst
Proof
  rpt strip_tac >> Cases_on `inst.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >> Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_op_map_def]
QED

Triviality step_inst_base_dret_map[local]:
  !g inst s.
    inst.inst_opcode = DRET /\
    parse_dret_shape
      (inst with inst_operands := MAP g inst.inst_operands) =
      parse_dret_shape inst /\
    eval_operands (MAP g inst.inst_operands) s =
      eval_operands inst.inst_operands s ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  simp[step_inst_base_DRET]
QED

(* Reuse the exported branches rather than rebuilding the full dispatch. *)
val step_inst_base_opcode_rewrites = CONJUNCTS step_inst_base_opcode_eqs;

(* Cache only record projections and the selected proved dispatch equation.
   Goal-only rewriting avoids both the global semantic simpset and traversal
   of operand-preservation hypotheses in every opcode branch. *)
val opcode_projection_ss = bool_ss ++ rewrites
  [instruction_accfupds, combinTheory.K_THM];
val opcode_dispatch_rules = map (fn th => let
  val rule = SPEC_ALL th
  val guard = fst (dest_imp (concl rule))
  val inst = rand (lhs guard)
  val updated = SIMP_RULE opcode_projection_ss []
    (INST [inst |-> ``^inst with inst_operands := ops``] rule)
in (rhs guard, (rule, updated)) end) step_inst_base_opcode_rewrites;

fun rewrite_step_inst_base_opcode eq = let
  val (rule, updated) = #2 (valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq))) opcode_dispatch_rules))
in
  PURE_ONCE_REWRITE_TAC [MATCH_MP updated eq, MATCH_MP rule eq] >>
  TRY REFL_TAC
end;

(* Push MAP through list observation, without enumerating list lengths or
   semantic results. The two branch bodies then agree by eval preservation. *)
Triviality list_case_map[local]:
  !g xs nil cons.
    list_CASE (MAP g xs) nil cons =
    list_CASE xs nil (\h t. cons (g h) (MAP g t))
Proof
  Cases_on `xs` >> simp[]
QED

val operand_map_ss = bool_ss ++ rewrites
  ([list_case_map, pairTheory.pair_case_thm] @ exec_inst_operands_thms);

fun operand_map_finish eval_th = let
  val rules = map (fn th => MATCH_MP th eval_th)
    (eval_operands_map_thm :: exec_map_thms)
in simp_tac operand_map_ss (eval_th :: rules) end;

(* JMP only observes a singleton Label. Keep evaluation out of its simpset. *)
val label_op_ss = bool_ss ++ rewrites
  [combinTheory.K_THM, MAP, list_case_def, operand_case_def,
   operand_distinct, operand_11,
   instruction_accfupds,
   valOf (List.find
     (fn th => aconv (rhs (fst (dest_imp (concl (SPEC_ALL th))))) ``JMP``)
     step_inst_base_opcode_rewrites)];
val label_op_simp = full_simp_tac label_op_ss [];

val label_op_tac =
  label_op_simp >>
  Cases_on `inst.inst_operands` >> label_op_simp >>
  Cases_on `t` >> label_op_simp >>
  Cases_on `h` >> label_op_simp >>
  FIRST [
    rename1 `Lit c` >>
    `!lbl. g (Lit c) <> Label lbl` by
      (qpat_x_assum `!op. (!lbl. op <> Label lbl) ==> _`
         (qspec_then `Lit c` mp_tac) >> label_op_simp) >>
    Cases_on `g (Lit c)` >> label_op_simp,
    rename1 `Var vn` >>
    `!lbl. g (Var vn) <> Label lbl` by
      (qpat_x_assum `!op. (!lbl. op <> Label lbl) ==> _`
         (qspec_then `Var vn` mp_tac) >> label_op_simp) >>
    Cases_on `g (Var vn)` >> label_op_simp];

Theorem step_inst_base_operands_irrelevant_safe[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    inst.inst_opcode <> DRET /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> opcode_filter_tac >>
  qpat_x_assum `inst.inst_opcode = _` rewrite_step_inst_base_opcode >>
  qpat_x_assum `!op. eval_operand (g op) s = _` operand_map_finish
QED

Triviality operand_case_nonlabel[local]:
  !op e f. (!lbl. op <> Label lbl) ==>
    operand_CASE op (\c. e) (\vn. e) f = e
Proof
  Cases_on `op` >> simp[]
QED

(* JNZ observes only list/Label shape and the first operand evaluation.
   Keep its two generic operand hypotheses out of the simplifier. *)
val jnz_op_ss = bool_ss ++ rewrites
  [combinTheory.K_THM, MAP, list_case_def, operand_case_def,
   operand_distinct, operand_11];
val jnz_op_simp = full_simp_tac jnz_op_ss [];
val jnz_dispatch_ss = jnz_op_ss ++ rewrites
  [instruction_accfupds,
   valOf (List.find
     (fn th => aconv (rhs (fst (dest_imp (concl (SPEC_ALL th))))) ``JNZ``)
     step_inst_base_opcode_rewrites)];

Triviality step_inst_base_jnz_map[local]:
  !g inst s.
    inst.inst_opcode = JNZ /\
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  qpat_x_assum `!op. eval_operand (g op) s = _` (fn eval_th =>
  qpat_x_assum `!op. (!lbl. op <> Label lbl) ==> _` (fn label_th => let
    fun nonlabel tm =
      full_simp_tac jnz_op_ss
        [MATCH_MP operand_case_nonlabel
          (SIMP_RULE label_op_ss [] (Q.SPEC tm label_th))]
    fun label_case tm =
      Cases_on tm >> jnz_op_simp >>
      FIRST [
        rename1 `Lit c` >> nonlabel `Lit c`,
        rename1 `Var vn` >> nonlabel `Var vn`,
        ALL_TAC]
  in
    full_simp_tac jnz_dispatch_ss [] >>
    Cases_on `inst.inst_operands` >> jnz_op_simp >>
    Cases_on `t` >> jnz_op_simp >>
    label_case `h'` >>
    Cases_on `t'` >> jnz_op_simp >>
    label_case `h'` >>
    Cases_on `t` >> jnz_op_simp >>
    assume_tac (Q.SPEC `h` eval_th) >> jnz_op_simp
  end))
QED

(* DJMP needs only its exported dispatch equation and list shape.  Supply
   evaluation/label preservation explicitly, never the guarded hypothesis. *)
val djmp_op_ss = bool_ss ++ rewrites
  [combinTheory.K_THM, MAP, list_case_def, instruction_accfupds,
   valOf (List.find
     (fn th => aconv (rhs (fst (dest_imp (concl (SPEC_ALL th))))) ``DJMP``)
     step_inst_base_opcode_rewrites)];

Theorem step_inst_base_operands_irrelevant_label[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) /\
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac
  >- label_op_tac
  >- (irule step_inst_base_jnz_map >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (`!ops. extract_labels (MAP g ops) = extract_labels ops` by
        (strip_tac >> irule extract_labels_map >>
         conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `inst.inst_opcode = DJMP` (fn opcode_th =>
      qpat_x_assum `!ops. extract_labels (MAP g ops) = _` (fn labels_th =>
      qpat_x_assum `!op. eval_operand (g op) s = _` (fn eval_th =>
        simp_tac djmp_op_ss [opcode_th] >>
        Cases_on `inst.inst_operands` >>
        pop_assum (fn ops_th =>
          simp_tac djmp_op_ss [ops_th, labels_th, eval_th])))))
QED

Theorem step_inst_base_operands_irrelevant[local]:
  !g inst s.
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    inst.inst_opcode <> DRET /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG ==>
    step_inst_base (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
            inst.inst_opcode = DJMP`
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

(* The INVOKE continuation is identical after decoding and argument
   evaluation. Do not split function lookup, callee setup, or run_blocks. *)
val invoke_ss = bool_ss ++ rewrites
  [step_inst_def, instruction_accfupds, combinTheory.K_THM,
   optionTheory.option_case_def, pairTheory.pair_case_thm];

Triviality step_inst_invoke_args[local]:
  !fuel ctx inst new_ops s name args new_args.
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (name, args) /\
    decode_invoke (inst with inst_operands := new_ops) =
      SOME (name, new_args) /\
    eval_operands new_args s = eval_operands args s ==>
    step_inst fuel ctx (inst with inst_operands := new_ops) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >> asm_simp_tac invoke_ss []
QED

Triviality step_inst_invoke_map[local]:
  !g fuel ctx inst s.
    inst.inst_opcode = INVOKE /\
    (!op. eval_operand (g op) s = eval_operand op s) /\
    (!lbl. g (Label lbl) = Label lbl) /\
    (!op. (!lbl. op <> Label lbl) ==> (!lbl. g op <> Label lbl)) ==>
    step_inst fuel ctx (inst with inst_operands := MAP g inst.inst_operands) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `decode_invoke (inst with inst_operands := MAP g inst.inst_operands) =
    case decode_invoke inst of
      NONE => NONE
    | SOME (name, args) => SOME (name, MAP g args)` by
    (irule decode_invoke_map >> simp[]) >>
  `!ops. eval_operands (MAP g ops) s = eval_operands ops s` by
    (strip_tac >> irule eval_operands_map_thm >> first_assum ACCEPT_TAC) >>
  Cases_on `decode_invoke inst`
  >- asm_simp_tac invoke_ss [] >>
  rename1 `decode_invoke inst = SOME decoded` >>
  PairCases_on `decoded` >>
  irule step_inst_invoke_args >> simp[]
QED

(* Cache the one-level well-formedness dispatch. Only its selected branch
   enters each goal; neither comparisons nor allocation filtering traverses
   the other hundred branches. Preserve the opcode equation for finishers. *)
val wf_opcode_rules = map (fn th => let
  val opc = rhs (fst (dest_imp (concl (SPEC_ALL th))))
  val eq = mk_eq (``inst.inst_opcode``, opc)
  val rule = CONV_RULE
    (RAND_CONV (REWRITE_CONV [ASSUME eq, opcode_case_def]))
    (Q.SPEC `inst` inst_wf_def)
in (opc, rule) end) step_inst_base_opcode_rewrites;

val wf_opcode_resolve_tac =
  qpat_x_assum `inst.inst_opcode = _` (fn eq => let
    val rule = #2 (valOf (List.find
      (fn (opc, _) => aconv opc (rhs (concl eq))) wf_opcode_rules))
  in
    assume_tac eq >>
    qpat_x_assum `inst_wf inst`
      (strip_assume_tac o EQ_MP (PROVE_HYP eq rule))
  end);

Triviality is_alloca_opcode[local]:
  !opc. is_alloca_op opc <=> opc = ALLOCA
Proof
  Cases >> simp_tac opcode_filter_ss []
QED

(* Only operand structure and already-proved evaluation agreements enter
   structural finishers, not the full step_inst_base dispatch. *)
val operand_shape_ss = bool_ss ++ numSimps.REDUCE_ss ++
  numSimps.ARITH_ss ++ rewrites
  [instruction_accfupds, combinTheory.K_THM, LET_THM,
   MAP, LENGTH, LENGTH_MAP, LENGTH_REVERSE, REVERSE_EQ_NIL, HD, TL, EL,
   list_case_def, operand_case_def, pairTheory.pair_case_thm,
   GSYM MAP_REVERSE, GSYM MAP_DROP, EL_MAP, rich_listTheory.MAP_HD];
val operand_shape_tac = asm_simp_tac operand_shape_ss [];

(* ===================================================================== *)
(* ===== step_inst substitution correctness ============================ *)
(* ===================================================================== *)

Theorem subst_operands_correct:
  !fuel ctx inst s old new_op v.
    lookup_var old s = SOME v /\
    eval_operand new_op s = SOME v /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    (inst.inst_opcode = DRET ==> IS_SOME (parse_dret_shape inst)) /\
    (!lbl. new_op <> Label lbl) ==>
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
    Cases >> simp[subst_operand_def] >> rw[]) >>
  simp[subst_operands_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule step_inst_invoke_map >> simp[]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (simp[step_inst_non_invoke] >>
      irule step_inst_base_dret_map >>
      simp[parse_dret_shape_subst_operand, eval_operands_map_thm]) >>
  simp[step_inst_non_invoke] >>
  irule step_inst_base_operands_irrelevant >> simp[]
QED

Theorem subst_operands_map_correct:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                IS_SOME (eval_operand new_op s) /\
                eval_operand new_op s = eval_operand (Var v) s /\
                (!lbl. new_op <> Label lbl)) /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> LOG /\
    (inst.inst_opcode = DRET ==> IS_SOME (parse_dret_shape inst)) ==>
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
    rename1 `FLOOKUP subs vn` >> Cases_on `FLOOKUP subs vn` >> simp[] >>
    rename1 `FLOOKUP subs vn = SOME nop` >>
    first_x_assum drule >> simp[]) >>
  simp[subst_operands_map_def] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (irule step_inst_invoke_map >> simp[]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (simp[step_inst_non_invoke] >>
      irule step_inst_base_dret_map >>
      simp[parse_dret_shape_subst_op_map, eval_operands_map_thm]) >>
  simp[step_inst_non_invoke] >>
  irule step_inst_base_operands_irrelevant >> simp[]
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
   Strategy: structural opcodes (PARAM, FMP_PARAM, RETPC_PARAM, ALLOCA, LOG,
   JMP, JNZ, DJMP, INVOKE) handled by inst_wf + definition unfolding.
   OFFSET is exec_pure2 (positional), handled by step_inst_base_operands_irrelevant_safe.
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
  Cases_on `inst.inst_opcode = DRET`
  >- (wf_opcode_resolve_tac >>
      simp[subst_operands_map_def, step_inst_non_invoke] >>
      irule step_inst_base_dret_map >>
      simp[parse_dret_shape_subst_op_map, eval_operands_map_thm]) >>
  (* Non-structural opcodes *)
  Cases_on `inst.inst_opcode <> PARAM /\
            inst.inst_opcode <> FMP_PARAM /\
            inst.inst_opcode <> RETPC_PARAM /\
            ~is_alloca_op inst.inst_opcode /\
            inst.inst_opcode <> LOG /\
            inst.inst_opcode <> JMP /\
            inst.inst_opcode <> JNZ /\
            inst.inst_opcode <> DJMP /\
            inst.inst_opcode <> INVOKE`
  >- (simp[subst_operands_map_def, step_inst_non_invoke] >>
      irule step_inst_base_operands_irrelevant_safe >> gvs[])
  >>
  (* Structural: inst_wf resolves operand shapes *)
  gvs[is_alloca_opcode] >> wf_opcode_resolve_tac >>
  (* Trivial: all Lit/Label operands => subst is identity *)
  TRY (`subst_operands_map subs inst = inst` by
         (irule subst_operands_map_id >> simp[subst_op_map_def]) >>
       simp[] >> NO_TAC) >>
  gvs[subst_operands_map_def, subst_op_map_def]
  >- ((* LOG *)
    `rest <> []` by (Cases_on `rest` >> gvs[]) >>
    simp[step_inst_non_invoke] >>
    qpat_x_assum `inst.inst_opcode = LOG` rewrite_step_inst_base_opcode >>
    `eval_operands (MAP (subst_op_map subs) (DROP 2 (REVERSE rest))) s =
     eval_operands (DROP 2 (REVERSE rest)) s` by
      (irule eval_operands_map_thm >> metis_tac[]) >>
    operand_shape_tac)
  >- ((* JNZ *)
    simp[step_inst_non_invoke] >>
    qpat_x_assum `inst.inst_opcode = JNZ` rewrite_step_inst_base_opcode >>
    operand_shape_tac)
  >- ((* DJMP *)
    drule_then assume_tac subst_op_map_preserves_labels >>
    simp[step_inst_non_invoke] >>
    qpat_x_assum `inst.inst_opcode = DJMP` rewrite_step_inst_base_opcode >>
    operand_shape_tac)
  >- ((* INVOKE *)
    irule step_inst_invoke_args >>
    simp[decode_invoke_def] >>
    irule eval_operands_map_thm >> first_assum ACCEPT_TAC)
QED

(* ===================================================================== *)
(* ===== General positional operand replacement ======================== *)
(* ===================================================================== *)

(* ML tactic: find the eval_operand universal hypothesis and instantiate at
   indices 0..max_idx. Uses ASSUME (non-consuming) so the original stays. *)
fun inst_eval_tac (asl, g) = let
  val eval_hyp = valOf (List.find (fn a =>
    is_forall a andalso
    can (find_term (fn t => (fst(dest_const t) = "eval_operand") handle _ => false)) a andalso
    not (can (find_term (fn t => (fst(dest_const t) = "Label") handle _ => false)) a)
    ) asl)
  val th = ASSUME eval_hyp
  fun inst_at n = ASSUME_TAC (SIMP_RULE (srw_ss()) []
    (SPEC (numSyntax.mk_numeral (Arbnum.fromInt n)) th))
  fun go n = if n > 12 then ALL_TAC else inst_at n >> go (n+1)
in go 0 (asl, g) end handle _ => ALL_TAC (asl, g);

val wf_opcode_finish_tac =
  Cases_on `inst.inst_opcode` >>
  opcode_filter_tac;
Triviality step_inst_base_RET_eval_operands[local]:
  !inst new_ops st.
    inst.inst_opcode = RET /\
    eval_operands new_ops st = eval_operands inst.inst_operands st ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt strip_tac >>
  qpat_x_assum `inst.inst_opcode = RET` rewrite_step_inst_base_opcode >>
  qpat_x_assum `eval_operands new_ops st = _`
    (fn th => simp_tac bool_ss [th])
QED

val ret_long_finish_tac =
  irule step_inst_base_RET_eval_operands >> simp[];


(* Select the already-resolved branch before simplifying.  In particular,
   STOP/NOP and read0 instructions need neither record cases nor the full
   opcode dispatch (and its unrelated semantic bodies) in the goal. *)
val pos_finish_ss = exec_pos_ss ++ rewrites
  ([instruction_accfupds, combinTheory.K_THM, list_case_def,
    pairTheory.pair_case_thm, optionTheory.option_case_def,
    operand_case_def] @ exec_pos_thms @ exec_inst_operands_thms);
val pos_finish_branches = map (fn th =>
  (rhs (fst (dest_imp (concl (SPEC_ALL th)))),
   pos_finish_ss ++ rewrites [th])) step_inst_base_opcode_rewrites;

fun pos_branch_finish_tac (asl, goal) = let
  val eq = valOf (List.find (can (match_term ``inst.inst_opcode = opc``)) asl)
  val ss = #2 (valOf (List.find
    (fn (opc, _) => aconv opc (rhs eq)) pos_finish_branches))
in
  asm_simp_tac ss [] (asl, goal)
end;

val long_safe_finish_tac = pos_branch_finish_tac;

Triviality step_inst_base_CALL_pos[local]:
  !inst new_ops st.
    inst.inst_opcode = CALL /\
    LENGTH inst.inst_operands = 7 /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st =
         eval_operand (EL i inst.inst_operands) st) ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  inst_eval_tac >> gvs[] >>
  pos_branch_finish_tac
QED

val call_long_finish_tac =
  qpat_x_assum `inst.inst_opcode = CALL` assume_tac >>
  irule step_inst_base_CALL_pos >> simp[];

val long_or_call_finish_tac =
  call_long_finish_tac ORELSE long_safe_finish_tac;

(* Reject fixed short arities using just the two length facts, without
   simplifying evaluation hypotheses in the many impossible branches. *)
val long_operand_bound_tac =
  TRY (qpat_x_assum `LENGTH inst.inst_operands = _` (fn len =>
    qpat_x_assum `6 < LENGTH inst.inst_operands`
      (CONTR_TAC o SIMP_RULE opcode_filter_ss [len])));

Triviality step_inst_base_pos_safe_long[local]:
  !inst new_ops st.
    inst_wf inst /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    6 < LENGTH inst.inst_operands /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (inst.inst_opcode = DRET ==>
      parse_dret_shape (inst with inst_operands := new_ops) =
      parse_dret_shape inst) /\
    eval_operands new_ops st = eval_operands inst.inst_operands st /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st =
         eval_operand (EL i inst.inst_operands) st) ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  wf_opcode_resolve_tac >>
  long_operand_bound_tac >>
  opcode_filter_tac
  >- long_safe_finish_tac
  >- ret_long_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_safe_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac
  >- long_or_call_finish_tac >>
  opcode_filter_tac
QED

val wf_opcode_contra_tac =
  qsuff_tac `F` >- simp[] >>
  qpat_x_assum `inst_wf inst` (mp_tac o REWRITE_RULE [inst_wf_def]) >>
  Cases_on `inst.inst_opcode` >>
  opcode_filter_tac;

val pos_semantics_ss = pos_finish_ss ++ rewrites
  [exec_pure1_def, exec_pure2_def, exec_pure3_def,
   exec_read0_def, exec_read1_def, exec_write2_def];

(* Try the positional helper before expanding fixed operand shapes. Most
   opcodes then need no list witnesses or instantiated index hypotheses. *)
val pos_opcode_finish_tac =
  pos_branch_finish_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  inst_eval_tac >> gvs[] >>
  pos_branch_finish_tac >>
  asm_simp_tac pos_semantics_ss [];

Triviality step_inst_base_pos_safe[local]:
  !inst new_ops st.
    inst_wf inst /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> LOG /\
    inst.inst_opcode <> JMP /\
    inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (inst.inst_opcode = DRET ==>
      parse_dret_shape (inst with inst_operands := new_ops) =
      parse_dret_shape inst) /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) (st:venom_state) =
         eval_operand (EL i inst.inst_operands) st) ==>
    step_inst_base (inst with inst_operands := new_ops) st =
    step_inst_base inst st
Proof
  rpt strip_tac >>
  `eval_operands new_ops st = eval_operands inst.inst_operands st` by
    (irule eval_operands_positional >> simp[]) >>
  Cases_on `6 < LENGTH inst.inst_operands` >-
   (irule step_inst_base_pos_safe_long >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  wf_opcode_resolve_tac >>
  opcode_filter_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
  >- pos_opcode_finish_tac
QED

(*
 * step_inst_operands_equiv: replacing operands with evaluation-equivalent
 * ones preserves step_inst semantics.
 *
 * Hypotheses:
 *   - inst_wf: well-formed instruction (gives operand count/shape)
 *   - LENGTH: new_ops same length as original
 *   - eval agreement: per-element eval_operand agreement
 *   - label preservation: Label operands structurally preserved
 *   - HD preservation for LOG: first operand (topic count Lit) preserved
 *   - excluded: PHI (not executable), ALLOCA/PALLOCA/CALLOCA (need Lit),
 *     PARAM (needs Lit)
 *)
Triviality log_reverse_operand_agreement:
  !xs ys st.
    LENGTH xs = LENGTH ys /\
    (!i. i < LENGTH xs ==>
      eval_operand (EL i xs) st = eval_operand (EL i ys) st) ==>
    !i. i < LENGTH xs ==>
      eval_operand (EL i (REVERSE xs)) st =
      eval_operand (EL i (REVERSE ys)) st
Proof
  rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH xs ==> _`
    (qspec_then `PRE (LENGTH xs - i)` mp_tac) >>
  (impl_tac >- DECIDE_TAC) >> simp[EL_REVERSE]
QED

Theorem step_inst_operands_equiv:
  !fuel ctx inst new_ops st.
    inst_wf inst /\
    ~is_alloca_op inst.inst_opcode /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> RETPC_PARAM /\
    inst.inst_opcode <> PHI /\
    LENGTH new_ops = LENGTH inst.inst_operands /\
    (inst.inst_opcode = DRET ==>
      parse_dret_shape (inst with inst_operands := new_ops) =
      parse_dret_shape inst) /\
    (!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st = eval_operand (EL i inst.inst_operands) st) /\
    (!i. i < LENGTH inst.inst_operands ==>
         !lbl. EL i inst.inst_operands = Label lbl ==> EL i new_ops = Label lbl) /\
    (inst.inst_opcode = LOG ==> HD new_ops = HD inst.inst_operands) ==>
    step_inst fuel ctx (inst with inst_operands := new_ops) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >>
  (* INVOKE: decode label + eval_operands on args *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (wf_opcode_resolve_tac >> gvs[] >>
      Cases_on `new_ops` >> gvs[] >>
      `h = Label lbl` by
        (qpat_x_assum `!i. i < _ ==> !lbl'. _ = Label lbl' ==> _`
           (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[] >>
      `eval_operands t st = eval_operands args st` by (
        irule eval_operands_positional >> simp[] >>
        rpt strip_tac >>
        qpat_x_assum `!j. j < SUC _ ==> eval_operand _ _ = _`
          (qspec_then `SUC i` mp_tac) >> simp[]) >>
      irule step_inst_invoke_args >> simp[decode_invoke_def]) >>
  simp[step_inst_non_invoke] >>
  (* Non-structural: use ML-level step_inst_base_pos_safe *)
  Cases_on `inst.inst_opcode <> LOG /\ inst.inst_opcode <> JMP /\
            inst.inst_opcode <> JNZ /\ inst.inst_opcode <> DJMP`
  >- (irule step_inst_base_pos_safe >> simp[]) >>
  (* Structural opcodes: LOG, JMP, JNZ, DJMP *)
  gvs[] >> wf_opcode_resolve_tac
  >- ( (* LOG: Lit tc :: rest *)
      Cases_on `new_ops` >> gvs[] >>
      `!i. i < LENGTH t ==>
        eval_operand (EL i t) st = eval_operand (EL i rest) st` by (
        rpt strip_tac >>
        qpat_x_assum `!j. _ ==> eval_operand (EL j (Lit tc::t)) st = _`
          (qspec_then `SUC i` mp_tac) >> simp[]) >>
      `!i. i < LENGTH t ==>
        eval_operand (EL i (REVERSE t)) st =
        eval_operand (EL i (REVERSE rest)) st` by
        (qspecl_then [`t`, `rest`, `st`] mp_tac
           log_reverse_operand_agreement >> simp[]) >>
      `eval_operand (HD (REVERSE t)) st =
       eval_operand (HD (REVERSE rest)) st` by
        (qpat_x_assum `!i. i < LENGTH t ==> _`
          (qspec_then `0` mp_tac) >> simp[]) >>
      `eval_operand (EL 1 (REVERSE t)) st =
       eval_operand (EL 1 (REVERSE rest)) st` by
        (qpat_x_assum `!i. i < LENGTH t ==> _`
          (qspec_then `1` mp_tac) >> simp[]) >>
      `eval_operands (DROP 2 (REVERSE t)) st =
       eval_operands (DROP 2 (REVERSE rest)) st` by (
        irule eval_operands_positional >> simp[LENGTH_DROP] >>
        rpt strip_tac >>
        `EL i (DROP 2 (REVERSE t)) = EL (i + 2) (REVERSE t)` by
          (irule EL_DROP >> simp[]) >>
        `EL i (DROP 2 (REVERSE rest)) = EL (i + 2) (REVERSE rest)` by
          (irule EL_DROP >> simp[]) >>
        simp[] >>
        qpat_x_assum `!j. j < LENGTH t ==> _`
          (qspec_then `i + 2` mp_tac) >> simp[]) >>
      qpat_x_assum `inst.inst_opcode = LOG` rewrite_step_inst_base_opcode >>
      operand_shape_tac)
  >- ( (* JMP: [Label lbl] *)
      Cases_on `new_ops` >> gvs[] >>
      qpat_x_assum `inst.inst_opcode = JMP` rewrite_step_inst_base_opcode >>
      operand_shape_tac)
  >- ( (* JNZ: [c; Label l1; Label l2] *)
      `EL 1 new_ops = Label l1` by (
        qpat_x_assum `!i. _ ==> !lbl. _ ==> _`
          (qspec_then `1` mp_tac) >> simp[]) >>
      `EL 2 new_ops = Label l2` by (
        qpat_x_assum `!i. _ ==> !lbl. _ ==> _`
          (qspec_then `2` mp_tac) >> simp[]) >>
      `eval_operand (HD new_ops) st = eval_operand c st` by (
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[LENGTH_EQ_NUM_compute] >>
      qpat_x_assum `inst.inst_opcode = JNZ` rewrite_step_inst_base_opcode >>
      operand_shape_tac)
  >> ( (* DJMP: sel :: label_ops, need t = label_ops *)
      Cases_on `new_ops` >> gvs[] >>
      `t = label_ops` by (
        irule LIST_EQ >> simp[] >> rpt strip_tac >>
        rename1 `x < LENGTH label_ops` >>
        `(\op. IS_SOME (get_label op)) (EL x label_ops)` by
          (irule (iffLR EVERY_EL) >> simp[]) >> fs[] >>
        Cases_on `EL x label_ops` >> gvs[get_label_def] >>
        qpat_x_assum `!i. i < _ ==> !lbl. _ = Label lbl ==> _`
          (qspec_then `SUC x` mp_tac) >> simp[]) >>
      `eval_operand h st = eval_operand sel st` by (
        qpat_x_assum `!i. _ ==> eval_operand _ _ = _`
          (qspec_then `0` mp_tac) >> simp[]) >>
      gvs[] >>
      qpat_x_assum `inst.inst_opcode = DJMP` rewrite_step_inst_base_opcode >>
      operand_shape_tac)
QED

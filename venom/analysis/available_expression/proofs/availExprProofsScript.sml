(*
 * Available Expression Analysis — Proofs (internal)
 *
 * Cheated proofs for safety properties. The externally-facing API
 * is in availExprAnalysisPropsScript.sml (ACCEPT_TAC wrappers).
 *)

Theory availExprProofs
Ancestors
  availExprDefs

(* ===== avail_add ===== *)

Theorem avail_add_FDOM:
  ∀ae expr inst. FDOM (avail_add ae expr inst) = expr INSERT FDOM ae
Proof
  rw[avail_add_def] >> CASE_TAC >> simp[]
QED

Theorem avail_add_lookup_same:
  ∀ae expr inst.
    FLOOKUP ae expr = NONE ⇒
    FLOOKUP (avail_add ae expr inst) expr = SOME [inst]
Proof
  rw[avail_add_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Adding to an existing key appends to the instruction list *)
Theorem avail_add_lookup_existing:
  ∀ae expr inst insts.
    FLOOKUP ae expr = SOME insts ⇒
    FLOOKUP (avail_add ae expr inst) expr = SOME (insts ++ [inst])
Proof
  rw[avail_add_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem avail_add_lookup_other:
  ∀ae expr expr' inst.
    expr' ≠ expr ⇒
    FLOOKUP (avail_add ae expr inst) expr' = FLOOKUP ae expr'
Proof
  rw[avail_add_def] >> CASE_TAC >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* ===== Kill / Remove-Effect ===== *)

Theorem avail_remove_effect_empty:
  ∀ae. avail_remove_effect ae empty_effects = ae
Proof
  simp[avail_remove_effect_def]
QED

Theorem avail_remove_effect_preserves:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = SOME insts
Proof
  rw[avail_remove_effect_def] >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT] >>
  fs[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem avail_remove_effect_kills:
  ∀ae expr eff insts.
    FLOOKUP ae expr = SOME insts ∧
    ¬DISJOINT (expr_effects expr) eff ⇒
    FLOOKUP (avail_remove_effect ae eff) expr = NONE
Proof
  rw[avail_remove_effect_def]
  >- metis_tac[venomEffectsTheory.empty_effects_def,
               pred_setTheory.DISJOINT_EMPTY] >>
  simp[finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem avail_remove_effect_FDOM_SUBSET:
  ∀ae eff. FDOM (avail_remove_effect ae eff) ⊆ FDOM ae
Proof
  rw[avail_remove_effect_def, finite_mapTheory.FDOM_DRESTRICT,
     pred_setTheory.SUBSET_DEF, pred_setTheory.IN_INTER]
QED

(* ===== Meet / Lattice ===== *)

Theorem inter_fdom_finite[local]:
  ∀(a : avail_exprs) (b : avail_exprs). FINITE (FDOM a ∩ FDOM b)
Proof
  metis_tac[pred_setTheory.INTER_FINITE, finite_mapTheory.FDOM_FINITE]
QED

Theorem avail_meet_two_FDOM:
  ∀a b. FDOM (avail_meet_two a b) = FDOM a ∩ FDOM b
Proof
  rw[avail_meet_two_def] >>
  simp[finite_mapTheory.FUN_FMAP_DEF, inter_fdom_finite]
QED

Theorem avail_meet_two_FDOM_SUBSET_l:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM a
Proof
  simp[avail_meet_two_FDOM, pred_setTheory.INTER_SUBSET]
QED

Theorem avail_meet_two_FDOM_SUBSET_r:
  ∀a b. FDOM (avail_meet_two a b) ⊆ FDOM b
Proof
  simp[avail_meet_two_FDOM, pred_setTheory.INTER_SUBSET]
QED

(* ===== Transfer ===== *)

Theorem avail_transfer_inst_skip:
  ∀dfg inst ae.
    (is_pseudo inst.inst_opcode ∨
     inst.inst_opcode = ASSIGN ∨
     is_terminator inst.inst_opcode) ⇒
    avail_transfer_inst dfg inst ae = ae
Proof
  simp[avail_transfer_inst_def]
QED

Theorem avail_transfer_inst_nonidempotent_no_add:
  ∀dfg inst ae.
    is_nonidempotent inst.inst_opcode ⇒
    FDOM (avail_transfer_inst dfg inst ae) ⊆ FDOM ae
Proof
  rw[avail_transfer_inst_def] >>
  simp[avail_remove_effect_FDOM_SUBSET]
QED

Theorem avail_transfer_inst_preserves:
  ∀dfg inst ae expr insts.
    FLOOKUP ae expr = SOME insts ∧
    DISJOINT (expr_effects expr) (write_effects inst.inst_opcode) ∧
    expr ≠ mk_expr dfg inst ⇒
    FLOOKUP (avail_transfer_inst dfg inst ae) expr = SOME insts
Proof
  rw[avail_transfer_inst_def] >>
  simp[avail_add_lookup_other, avail_remove_effect_preserves]
QED

Theorem avail_transfer_inst_adds:
  ∀dfg inst ae.
    ¬is_pseudo inst.inst_opcode ∧
    inst.inst_opcode ≠ ASSIGN ∧
    ¬is_terminator inst.inst_opcode ∧
    LENGTH inst.inst_outputs ≤ 1 ∧
    ¬is_nonidempotent inst.inst_opcode ∧
    ¬has_conflicting_effects inst.inst_opcode ∧
    mk_expr dfg inst ∉ FDOM (avail_remove_effect ae
                               (write_effects inst.inst_opcode)) ⇒
    FLOOKUP (avail_transfer_inst dfg inst ae)
            (mk_expr dfg inst) = SOME [inst]
Proof
  rw[avail_transfer_inst_def] >>
  irule avail_add_lookup_same >>
  fs[finite_mapTheory.FLOOKUP_DEF]
QED

(* ===== Expression Effects ===== *)

Theorem expr_effects_var:
  ∀v. expr_effects (ExprVar v) = empty_effects
Proof
  simp[expr_effects_def]
QED

Theorem expr_effects_lit:
  ∀l. expr_effects (ExprLit l) = empty_effects
Proof
  simp[expr_effects_def]
QED

Theorem expr_effects_pure_op:
  ∀op args.
    read_effects op = empty_effects ∧
    write_effects op = empty_effects ∧
    EVERY (λe. expr_effects e = empty_effects) args ⇒
    expr_effects (ExprOp op args) = empty_effects
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_effects_def] >>
  Induct_on `args` >> rw[] >>
  fs[listTheory.EVERY_DEF]
QED

(* ===== expr_leq total order properties ===== *)

(* expr_leq is antisymmetric *)
Theorem expr_leq_antisym[local]:
  (∀x y. expr_leq x y ∧ expr_leq y x ⇒ x = y) ∧
  (∀l1 l2. expr_list_leq l1 l2 ∧ expr_list_leq l2 l1 ⇒ l1 = l2)
Proof
  ho_match_mp_tac expr_leq_ind >> simp[expr_leq_def] >>
  rpt conj_tac >| [
    rw[stringTheory.string_le_def] >> metis_tac[stringTheory.string_lt_antisym],
    rw[] >> metis_tac[wordsTheory.w2n_11, arithmeticTheory.LESS_EQUAL_ANTISYM],
    rw[] >> `opcode2num op1 = opcode2num op2` by DECIDE_TAC >>
      fs[venomInstTheory.opcode2num_11],
    Cases_on `l2` >> simp[expr_leq_def],
    rw[] >> fs[]
  ]
QED

(* expr_leq is total *)
Theorem expr_leq_total[local]:
  (∀x y. expr_leq x y ∨ expr_leq y x) ∧
  (∀l1 l2. expr_list_leq l1 l2 ∨ expr_list_leq l2 l1)
Proof
  ho_match_mp_tac expr_leq_ind >> simp[expr_leq_def] >>
  rpt conj_tac >| [
    rw[stringTheory.string_le_def] >> metis_tac[stringTheory.string_lt_cases],
    rw[] >> `opcode2num op1 < opcode2num op2 ∨
             opcode2num op1 = opcode2num op2 ∨
             opcode2num op2 < opcode2num op1` by DECIDE_TAC >>
      fs[] >> metis_tac[],
    rw[] >> metis_tac[]
  ]
QED

(* expr_leq is transitive *)
Theorem expr_leq_trans[local]:
  (∀x y z. expr_leq x y ∧ expr_leq y z ⇒ expr_leq x z) ∧
  (∀l1 l2 l3. expr_list_leq l1 l2 ∧ expr_list_leq l2 l3 ⇒ expr_list_leq l1 l3)
Proof
  ho_match_mp_tac avail_expr_induction >> rpt conj_tac >| [
    (* ExprVar *)
    Cases_on `y` >> Cases_on `z` >> simp[expr_leq_def] >>
    rw[stringTheory.string_le_def] >>
    metis_tac[stringTheory.string_lt_trans, stringTheory.string_lt_cases],
    (* ExprLit *)
    Cases_on `y` >> Cases_on `z` >> simp[expr_leq_def],
    (* ExprOp *)
    rw[] >> Cases_on `y` >> Cases_on `z` >> fs[expr_leq_def] >>
    `opcode2num o' < opcode2num o'' ∨
     opcode2num o' = opcode2num o''` by DECIDE_TAC >| [
      DISJ1_TAC >> DECIDE_TAC,
      `opcode2num o'' < opcode2num o'³' ∨
       opcode2num o'' = opcode2num o'³'` by DECIDE_TAC >| [
        DISJ1_TAC >> DECIDE_TAC,
        DISJ2_TAC >> metis_tac[]
      ]
    ],
    (* [] *)
    simp[expr_leq_def],
    (* x::l1 *)
    rw[] >> Cases_on `l2` >> Cases_on `l3` >> fs[expr_leq_def] >>
    Cases_on `x = h` >> Cases_on `h = h'` >> fs[] >-
      (first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >> simp[]) >>
    `expr_leq x h'` by (first_x_assum (qspecl_then [`h`, `h'`] mp_tac) >> simp[]) >>
    Cases_on `x = h'` >> fs[] >>
    `h = h'` by metis_tac[CONJUNCT1 expr_leq_antisym] >> fs[]
  ]
QED

(* ===== Canonicalization ===== *)

(* ML-level: establish expr_leq is a total order for QSORT reasoning *)
val expr_leq_total_order =
  let
    fun mk_prop def thm =
      EQ_MP (SYM (Q.SPEC `expr_leq`
        (INST_TYPE [alpha |-> ``:avail_expr``] def)))
        (CONJUNCT1 thm)
  in
    CONJ (mk_prop relationTheory.total_def expr_leq_total)
         (CONJ (mk_prop relationTheory.transitive_def expr_leq_trans)
               (mk_prop relationTheory.antisymmetric_def expr_leq_antisym))
  end;

val qsort_expr_perm = MATCH_MP sortingTheory.QSORT_eq_if_PERM expr_leq_total_order;

val qsort_expr_idem = prove(
  ``!l. QSORT expr_leq (QSORT expr_leq l) = QSORT expr_leq l``,
  rw[qsort_expr_perm] >>
  metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_SYM]);

val map_fixpoint = prove(
  ``!f l. EVERY (\x. f x = x) l ==> (MAP f l = l)``,
  Induct_on `l` >> rw[]);

val map_idem_pointwise = prove(
  ``!f l. MAP f (MAP f l) = MAP f l ==> !x. MEM x (MAP f l) ==> (f x = x)``,
  rw[listTheory.MEM_MAP] >>
  `MAP (f o f) l = MAP f l` by fs[GSYM listTheory.MAP_MAP_o] >>
  fs[listTheory.MAP_EQ_f, combinTheory.o_DEF]);

val map_qsort_idem = prove(
  ``!f R l. MAP f (MAP f l) = MAP f l ==>
    (MAP f (QSORT R (MAP f l)) = QSORT R (MAP f l))``,
  rw[] >>
  match_mp_tac map_fixpoint >>
  rw[listTheory.EVERY_MEM] >>
  imp_res_tac map_idem_pointwise >>
  metis_tac[sortingTheory.QSORT_MEM]);

Theorem canon_expr_idempotent:
  ∀e. canon_expr (canon_expr e) = canon_expr e
Proof
  `(∀e. canon_expr (canon_expr e) = canon_expr e) ∧
   (∀l. MAP canon_expr (MAP canon_expr l) = MAP canon_expr l)`
    suffices_by simp[] >>
  ho_match_mp_tac avail_expr_induction >> rpt conj_tac >>
  rw[canon_expr_def] >>
  Cases_on `is_commutative o'` >> simp[canon_expr_def] >| [
    imp_res_tac (ISPECL [``canon_expr``, ``expr_leq``] map_qsort_idem) >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >> fs[qsort_expr_idem],
    CONV_TAC (DEPTH_CONV ETA_CONV) >> fs[]
  ]
QED

Theorem canon_expr_comm:
  ∀op a b.
    is_commutative op ⇒
    canon_expr (ExprOp op [a; b]) = canon_expr (ExprOp op [b; a])
Proof
  rw[canon_expr_def, sortingTheory.QSORT_DEF,
     sortingTheory.PARTITION_DEF, sortingTheory.PART_DEF] >>
  metis_tac[CONJUNCT1 expr_leq_antisym, CONJUNCT1 expr_leq_total]
QED

Theorem mk_expr_canonical:
  ∀dfg inst. canon_expr (mk_expr dfg inst) = mk_expr dfg inst
Proof
  rw[mk_expr_def, mk_operand_expr_def, canon_expr_idempotent]
QED

(* ===== Query API ===== *)

Theorem avail_get_expression_diff:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    src.inst_id ≠ inst.inst_id
Proof
  simp_tac std_ss [avail_get_expression_def, avail_get_source_def] >>
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >> fs[]
QED

Theorem avail_get_expression_available:
  ∀fn lbl idx inst expr src.
    avail_get_expression fn lbl idx inst = SOME (expr, src) ⇒
    ∃insts. FLOOKUP (ae_lookup_inst fn lbl idx) expr = SOME insts ∧
            MEM src insts
Proof
  simp_tac std_ss [avail_get_expression_def, avail_get_source_def] >>
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> fs[]) >>
  qexists_tac `h::t` >> gvs[listTheory.MEM]
QED

(*
 * CFG Transform Properties (public interface)
 *
 * Stable, generally useful properties of CFG transform definitions.  Longer
 * proof-engineering lemmas live in cfgTransformProofs; this theory owns the
 * public theorem names below and proves them directly when the proof is short.
 *
 * TOP-LEVEL (block ops):
 *   lookup_block_remove_neq/eq  -- remove_block preserves/removes lookup
 *   fn_labels_remove_block      -- labels after removing a block
 *   ALL_DISTINCT_remove_block   -- distinctness preserved by removal
 *   lookup_block_replace_neq/eq -- replace_block preserves/updates lookup
 *   fn_labels_replace_block     -- labels preserved by same-label replace
 *
 * TOP-LEVEL (label substitution):
 *   fn_labels_subst_label_fn    -- block labels unchanged by subst
 *   lookup_block_subst_label_fn -- lookup finds substituted block
 *
 * TOP-LEVEL (PHI correctness):
 *   resolve_phi_subst_label     -- core lemma: label subst + resolve
 *   resolve_phi_subst_label_Var -- corollary for Var results
 *   resolve_phi_subst_other     -- subst transparent for unrelated labels
 *   resolve_phi_remove_other    -- removal preserves unrelated resolve
 *
 * TOP-LEVEL (well-formedness + reachability):
 *   bb_well_formed_subst_label  -- wf preserved by label subst
 *   wf_function_remove_block    -- wf preserved by non-entry removal
 *   entry_block_remove_neq      -- entry preserved by non-entry removal
 *   fn_entry_label_remove_neq   -- entry label preserved
 *   reachable_entry/step/trans  -- reachability properties
 *)

Theory cfgTransformProps
Ancestors
  cfgTransform venomExecSemantics venomInst venomWf
Libs
  listTheory

(* ===== Local Proof Helpers ===== *)

Theorem FIND_FILTER[local]:
  !P Q l. FIND P (FILTER Q l) = FIND (\x. P x /\ Q x) l
Proof
  Induct_on `l` >> rw[FIND_thm, FILTER] >> fs[]
QED

Theorem FIND_MAP_cong[local]:
  !P f l. (!x. P (f x) = P x) ==>
          FIND P (MAP f l) = OPTION_MAP f (FIND P l)
Proof
  Induct_on `l` >> rw[FIND_thm, MAP, optionTheory.OPTION_MAP_DEF]
QED

Theorem FIND_MAP_id[local]:
  !P f l. (!x. P x ==> f x = x) /\ (!x. ~P x ==> ~P (f x)) ==>
          FIND P (MAP f l) = FIND P l
Proof
  Induct_on `l` >> rw[FIND_thm, MAP] >>
  Cases_on `P h` >> fs[]
QED

Theorem subst_label_inst_fields[local]:
  !old new inst.
    (subst_label_inst old new inst).inst_id = inst.inst_id /\
    (subst_label_inst old new inst).inst_opcode = inst.inst_opcode /\
    (subst_label_inst old new inst).inst_outputs = inst.inst_outputs
Proof
  rw[subst_label_inst_def]
QED

Theorem ALL_DISTINCT_FLAT_MAP_FILTER[local]:
  !P f l. ALL_DISTINCT (FLAT (MAP f l)) ==>
          ALL_DISTINCT (FLAT (MAP f (FILTER P l)))
Proof
  gen_tac >> gen_tac >> Induct >> rw[FILTER] >>
  fs[ALL_DISTINCT_APPEND] >> rw[] >> strip_tac >>
  `MEM e (FLAT (MAP f l))` suffices_by metis_tac[] >>
  fs[MEM_FLAT, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem MEM_remove_block_iff[local]:
  !bb lbl bbs.
    MEM bb (remove_block lbl bbs) <=> MEM bb bbs /\ bb.bb_label <> lbl
Proof
  rw[remove_block_def, MEM_FILTER] >> metis_tac[]
QED

(* ===== Block List Operations: remove_block ===== *)

Theorem lookup_block_remove_neq:
  !lbl other bbs.
    lbl <> other ==>
    lookup_block lbl (remove_block other bbs) = lookup_block lbl bbs
Proof
  rw[lookup_block_def, remove_block_def, FIND_FILTER] >>
  AP_THM_TAC >> AP_TERM_TAC >> rw[FUN_EQ_THM] >> metis_tac[]
QED

Theorem lookup_block_remove_eq:
  !lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl (remove_block lbl bbs) = NONE
Proof
  rw[lookup_block_def, remove_block_def, FIND_FILTER] >>
  Induct_on `bbs` >> rw[FIND_thm]
QED

Theorem fn_labels_remove_block:
  !lbl bbs.
    MAP (\bb. bb.bb_label) (remove_block lbl bbs) =
    FILTER (\l. l <> lbl) (MAP (\bb. bb.bb_label) bbs)
Proof
  Induct_on `bbs` >> rw[remove_block_def, FILTER, MAP] >>
  fs[remove_block_def]
QED

Theorem ALL_DISTINCT_remove_block:
  !lbl bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (remove_block lbl bbs))
Proof
  rw[fn_labels_remove_block] >> irule FILTER_ALL_DISTINCT >> simp[]
QED

(* ===== Block List Operations: replace_block ===== *)

Theorem lookup_block_replace_neq:
  !lbl other new_bb bbs.
    lbl <> other /\ new_bb.bb_label = other ==>
    lookup_block lbl (replace_block other new_bb bbs) =
    lookup_block lbl bbs
Proof
  rw[lookup_block_def, replace_block_def] >>
  irule FIND_MAP_id >> rw[]
QED

Theorem lookup_block_replace_eq:
  !lbl new_bb bbs.
    (?bb. lookup_block lbl bbs = SOME bb) /\
    new_bb.bb_label = lbl ==>
    lookup_block lbl (replace_block lbl new_bb bbs) = SOME new_bb
Proof
  Induct_on `bbs` >>
  rw[lookup_block_def, replace_block_def, FIND_thm, MAP] >>
  fs[FIND_thm, replace_block_def, lookup_block_def]
QED

Theorem fn_labels_replace_block:
  !lbl new_bb bbs.
    new_bb.bb_label = lbl ==>
    MAP (\bb. bb.bb_label) (replace_block lbl new_bb bbs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `bbs` >> rw[replace_block_def, MAP] >>
  fs[replace_block_def]
QED

(* ===== Label Substitution ===== *)

Theorem fn_labels_subst_label_fn:
  !old new fn.
    MAP (\bb. bb.bb_label)
        (subst_label_fn old new fn).fn_blocks =
    MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  rw[subst_label_fn_def, MAP_MAP_o, combinTheory.o_DEF,
     subst_label_block_def]
QED

Theorem lookup_block_subst_label_fn:
  !old new bbs lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    lookup_block lbl (MAP (subst_label_block old new) bbs) =
      SOME (subst_label_block old new bb)
Proof
  rw[lookup_block_def] >>
  `FIND (\bb. bb.bb_label = lbl) (MAP (subst_label_block old new) bbs) =
   OPTION_MAP (subst_label_block old new)
              (FIND (\bb. bb.bb_label = lbl) bbs)`
    by (irule FIND_MAP_cong >> rw[subst_label_block_def]) >>
  rw[optionTheory.OPTION_MAP_DEF]
QED

(* ===== PHI Label-Substitution Correctness ===== *)

Theorem resolve_phi_subst_label:
  !old new ops.
    ~MEM (Label new) ops ==>
    resolve_phi new (MAP (subst_label_op old new) ops) =
      OPTION_MAP (subst_label_op old new) (resolve_phi old ops)
Proof
  gen_tac >> ho_match_mp_tac resolve_phi_ind >>
  rw[resolve_phi_def, subst_label_op_def, MAP,
     optionTheory.OPTION_MAP_DEF]
QED

Theorem resolve_phi_subst_label_Var:
  !old new ops v.
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME (Var v) ==>
    resolve_phi new (MAP (subst_label_op old new) ops) = SOME (Var v)
Proof
  rw[resolve_phi_subst_label, subst_label_op_def,
     optionTheory.OPTION_MAP_DEF]
QED

Theorem resolve_phi_subst_other:
  !old new prev ops.
    prev <> old /\ prev <> new ==>
    resolve_phi prev (MAP (subst_label_op old new) ops) =
      OPTION_MAP (subst_label_op old new) (resolve_phi prev ops)
Proof
  ntac 2 gen_tac >> ho_match_mp_tac resolve_phi_ind >>
  rw[resolve_phi_def, subst_label_op_def, MAP,
     optionTheory.OPTION_MAP_DEF]
QED

Theorem resolve_phi_remove_other_aux[local]:
  !lbl ops prev.
    prev <> lbl ==>
    resolve_phi prev (remove_phi_label lbl ops) = resolve_phi prev ops
Proof
  ho_match_mp_tac remove_phi_label_ind >>
  rw[remove_phi_label_def, resolve_phi_def]
QED

Theorem resolve_phi_remove_other:
  !lbl prev ops.
    prev <> lbl ==>
    resolve_phi prev (remove_phi_label lbl ops) = resolve_phi prev ops
Proof
  metis_tac[resolve_phi_remove_other_aux]
QED

(* ===== Well-formedness Preservation ===== *)

Theorem bb_well_formed_subst_label:
  !old new bb.
    bb_well_formed bb ==>
    bb_well_formed (subst_label_block old new bb)
Proof
  rw[bb_well_formed_def, subst_label_block_def] >>
  gvs[LAST_MAP, EL_MAP, subst_label_inst_fields] >>
  metis_tac[]
QED

Theorem wf_function_remove_block:
  !fn lbl.
    wf_function fn /\
    fn_entry_label fn <> SOME lbl /\
    (!bb. MEM bb (remove_block lbl fn.fn_blocks) ==>
          ~MEM lbl (bb_succs bb)) ==>
    wf_function (fn with fn_blocks := remove_block lbl fn.fn_blocks)
Proof
  rw[wf_function_def] >-
   (fs[fn_labels_def] >> irule ALL_DISTINCT_remove_block >> simp[]) >-
   (fs[fn_has_entry_def, remove_block_def] >>
    Cases_on `fn.fn_blocks` >> fs[] >>
    fs[fn_entry_label_def, entry_block_def] >>
    rw[FILTER_NEQ_NIL] >> qexists_tac `h` >> rw[]) >-
   (fs[MEM_remove_block_iff] >> metis_tac[]) >-
   (fs[fn_succs_closed_def, fn_labels_def] >>
    rw[MEM_remove_block_iff] >>
    rw[fn_labels_remove_block, MEM_FILTER] >>
    `MEM bb fn.fn_blocks` by fs[MEM_remove_block_iff] >>
    `MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)` by metis_tac[] >>
    rw[] >> CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `bb` mp_tac) >> rw[MEM_remove_block_iff]) >>
  fs[fn_inst_ids_distinct_def, remove_block_def] >>
  irule ALL_DISTINCT_FLAT_MAP_FILTER >> simp[]
QED

(* ===== Entry Preservation ===== *)

Theorem entry_block_remove_neq:
  !fn lbl.
    fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label <> lbl ==>
    entry_block (fn with fn_blocks := remove_block lbl fn.fn_blocks) =
    entry_block fn
Proof
  rw[entry_block_def, remove_block_def] >>
  Cases_on `fn.fn_blocks` >> fs[FILTER, NULL_DEF] >>
  CCONTR_TAC >> fs[NULL_DEF]
QED

Theorem fn_entry_label_remove_neq:
  !fn lbl.
    fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label <> lbl ==>
    fn_entry_label (fn with fn_blocks := remove_block lbl fn.fn_blocks) =
    fn_entry_label fn
Proof
  rw[fn_entry_label_def, entry_block_remove_neq]
QED

(* ===== Reachability ===== *)

Theorem reachable_entry:
  !fn lbl.
    fn_entry_label fn = SOME lbl ==>
    reachable fn lbl
Proof
  rw[reachable_def]
QED

Theorem reachable_step:
  !fn a b.
    reachable fn a /\ fn_succ fn a b ==>
    reachable fn b
Proof
  rw[reachable_def] >>
  qexists_tac `entry` >> rw[] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES_RIGHT1)) >>
  qexists_tac `a` >> rw[]
QED

Theorem reachable_trans:
  !fn a b.
    reachable fn a /\ RTC (fn_succ fn) a b ==>
    reachable fn b
Proof
  rw[reachable_def] >>
  qexists_tac `entry` >> rw[] >>
  metis_tac[relationTheory.RTC_RTC]
QED

(*
 * SSA Construction: Dominance Utilities
 *
 * This theory defines dominator and dominance-frontier computations
 * using simple fixed-point iteration with explicit fuel.
 *)

Theory mkSsaDominance
Ancestors
  mkSsaCfg mkSsaTransform list finite_map pred_set

(* ===== Dominator Computation ===== *)

Type dom_map = ``:(string, string set) fmap``

(* Helper: lookup dominator set for a label. *)
Definition get_doms_def:
  get_doms doms lbl =
    case FLOOKUP doms lbl of
      SOME s => s
    | NONE => {}
End

(* Single iteration step. *)
Definition dom_step_def:
  dom_step preds entry all_labels (doms:dom_map) =
    FUN_FMAP (λlbl.
      if lbl = entry then {entry}
      else
        let ps = get_preds preds lbl in
        if ps = {} then all_labels
        else lbl INSERT BIGINTER {get_doms doms p | p IN ps}
    ) all_labels
End

(* Initial dominator map. *)
Definition init_doms_def:
  init_doms entry all_labels =
    FUN_FMAP (λlbl. if lbl = entry then {entry} else all_labels) all_labels
End

(* Iterate to a fixed point with fuel. *)
Definition compute_doms_fuel_def:
  compute_doms_fuel 0 _ _ _ doms = doms /\
  compute_doms_fuel (SUC n) preds entry all_labels doms =
    let doms' = dom_step preds entry all_labels doms in
    if doms' = doms then doms
    else compute_doms_fuel n preds entry all_labels doms'
End

(* Main dominator computation. *)
Definition compute_dominators_def:
  compute_dominators preds entry all_labels =
    let init = init_doms entry all_labels in
    let fuel = (CARD all_labels) * (CARD all_labels) in
    compute_doms_fuel fuel preds entry all_labels init
End

Definition dominates_def:
  dominates doms a b <=> a IN get_doms doms b
End

Definition sdom_def:
  sdom doms a b <=> dominates doms a b /\ a <> b
End

(* Helper: every node dominates itself. *)
Definition doms_self_def:
  doms_self all_labels doms <=>
    !lbl. lbl IN all_labels ==> lbl IN get_doms doms lbl
End

(* Helper: entry dominates all nodes. *)
Definition entry_doms_def:
  entry_doms entry all_labels doms <=>
    !lbl. lbl IN all_labels ==> entry IN get_doms doms lbl
End

(* ===== Immediate Dominator (approximate) ===== *)

Definition compute_idom_def:
  compute_idom doms entry all_labels =
    FUN_FMAP (λlbl.
      if lbl = entry then NONE
      else
        let strict = get_doms doms lbl DELETE lbl in
        if strict = {} then NONE else SOME (CHOICE strict)
    ) all_labels
End

Definition get_idom_def:
  get_idom idoms lbl =
    case FLOOKUP idoms lbl of
      SOME x => x
    | NONE => NONE
End

(* Helper: dominance from idom chain with fuel. *)
Definition idom_chain_fuel_def:
  idom_chain_fuel 0 _ _ _ = F /\
  idom_chain_fuel (SUC n) idoms a b =
    if a = b then T
    else
      case get_idom idoms b of
        NONE => F
      | SOME p => idom_chain_fuel n idoms a p
End

Definition dominates_from_idoms_def:
  dominates_from_idoms idoms a b =
    idom_chain_fuel (CARD (FDOM idoms) + 1) idoms a b
End

Definition sdom_from_idoms_def:
  sdom_from_idoms idoms a b <=>
    dominates_from_idoms idoms a b /\ a <> b
End

(* ===== Dominance Frontier ===== *)

Definition df_runner_fuel_def:
  df_runner_fuel 0 _ _ _ _ df = df /\
  df_runner_fuel (SUC n) runner target bb idoms df =
    if runner = target then df
    else
      case get_idom idoms runner of
        NONE => df
      | SOME next =>
          let curr = case FLOOKUP df runner of SOME s => s | NONE => {} in
          let df' = df |+ (runner, bb INSERT curr) in
          df_runner_fuel n next target bb idoms df'
End

Definition compute_df_def:
  compute_df preds idoms all_labels =
    FUN_FMAP (λd.
      {b | b IN all_labels /\
           (?p. p IN get_preds preds b /\
                dominates_from_idoms idoms d p) /\
           ~sdom_from_idoms idoms d b}
    ) all_labels
End

(* ===== Basic Properties ===== *)

Theorem dom_step_self:
  !preds entry all_labels doms lbl.
    lbl IN all_labels ==>
    lbl IN get_doms (dom_step preds entry all_labels doms) lbl
Proof
  rpt strip_tac >>
  Cases_on `lbl = entry`
  >- (
    qpat_x_assum `lbl IN all_labels` mp_tac >>
    simp[dom_step_def, get_doms_def, FLOOKUP_FUN_FMAP]
  )
  >- (
    simp[dom_step_def, get_doms_def, FLOOKUP_FUN_FMAP] >>
    Cases_on `get_preds preds lbl = {}` >> simp[]
  )
QED

Theorem init_doms_self:
  !entry all_labels. doms_self all_labels (init_doms entry all_labels)
Proof
  rw[doms_self_def, init_doms_def, get_doms_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `lbl = entry` >> simp[]
QED

Theorem compute_doms_fuel_self:
  !n preds entry all_labels doms.
    doms_self all_labels doms ==>
    doms_self all_labels (compute_doms_fuel n preds entry all_labels doms)
Proof
  Induct_on `n` >> simp[compute_doms_fuel_def, doms_self_def] >>
  rpt strip_tac >>
  Cases_on `dom_step preds entry all_labels doms = doms` >> simp[] >>
  first_x_assum irule >>
  rw[doms_self_def] >>
  irule dom_step_self >> simp[]
QED

Theorem compute_dominators_self:
  !preds entry all_labels.
    doms_self all_labels (compute_dominators preds entry all_labels)
Proof
  simp[compute_dominators_def] >>
  irule compute_doms_fuel_self >>
  simp[init_doms_self]
QED

Theorem dominates_refl:
  !preds entry all_labels doms lbl.
    doms = compute_dominators preds entry all_labels /\
    lbl IN all_labels ==>
    dominates doms lbl lbl
Proof
  rpt strip_tac >>
  subst_all_tac >>
  `doms_self all_labels (compute_dominators preds entry all_labels)` by
    simp[compute_dominators_self] >>
  fs[dominates_def, doms_self_def]
QED

Definition doms_closed_def:
  doms_closed doms <=>
    !a b. dominates doms a b ==> get_doms doms a SUBSET get_doms doms b
End

Theorem dominates_trans:
  !doms a b c.
    dominates doms a b /\
    dominates doms b c /\
    doms_closed doms ==>
    dominates doms a c
Proof
  rw[dominates_def, doms_closed_def, SUBSET_DEF] >>
  first_x_assum irule >> simp[]
QED

Theorem init_doms_entry:
  !entry all_labels.
    entry IN all_labels ==>
    entry_doms entry all_labels (init_doms entry all_labels)
Proof
  rw[entry_doms_def, init_doms_def, get_doms_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `lbl = entry` >> simp[]
QED

Theorem dom_step_entry:
  !preds entry all_labels doms.
    entry IN all_labels /\
    (!b p. p IN get_preds preds b ==> p IN all_labels) /\
    entry_doms entry all_labels doms ==>
    entry_doms entry all_labels (dom_step preds entry all_labels doms)
Proof
  rw[entry_doms_def, dom_step_def, get_doms_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `lbl = entry` >> simp[] >>
  Cases_on `get_preds preds lbl = {}` >> simp[] >>
  simp[IN_BIGINTER] >> rpt strip_tac >>
  rename1 `p IN get_preds preds lbl` >>
  `p IN all_labels` by (
    qpat_x_assum `!b p. p IN get_preds preds b ==> p IN all_labels`
      (qspecl_then [`lbl`, `p`] mp_tac) >> simp[]
  ) >>
  qpat_x_assum `entry_doms entry all_labels doms` (qspec_then `p` mp_tac) >>
  simp[entry_doms_def]
QED

Theorem compute_doms_fuel_entry:
  !n preds entry all_labels doms.
    entry IN all_labels /\
    (!b p. p IN get_preds preds b ==> p IN all_labels) /\
    entry_doms entry all_labels doms ==>
    entry_doms entry all_labels (compute_doms_fuel n preds entry all_labels doms)
Proof
  Induct_on `n` >> simp[compute_doms_fuel_def] >>
  rpt strip_tac >>
  Cases_on `dom_step preds entry all_labels doms = doms` >> simp[] >>
  first_x_assum irule >>
  simp[] >>
  irule dom_step_entry >> simp[]
QED

Theorem entry_dominates_all:
  !preds entry all_labels doms lbl.
    doms = compute_dominators preds entry all_labels /\
    entry IN all_labels /\
    lbl IN all_labels /\
    (!b p. p IN get_preds preds b ==> p IN all_labels) ==>
    dominates doms entry lbl
Proof
  rpt strip_tac >>
  subst_all_tac >>
  `entry_doms entry all_labels (compute_dominators preds entry all_labels)` by (
    simp[compute_dominators_def] >>
    irule compute_doms_fuel_entry >> simp[init_doms_entry]
  ) >>
  fs[dominates_def, entry_doms_def]
QED

Theorem df_correct:
  !df preds idoms all_labels b d.
    df = compute_df preds idoms all_labels /\
    d IN all_labels ==>
    (b IN get_dom_frontier df d <=>
     b IN all_labels /\
     (?p. p IN get_preds preds b /\
          dominates_from_idoms idoms d p) /\
     ~sdom_from_idoms idoms d b)
Proof
  rw[compute_df_def, get_dom_frontier_def, FLOOKUP_FUN_FMAP, IN_DEF]
QED

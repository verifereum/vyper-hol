(*
 * DFT Pass — Helper Lemmas
 *
 * Generic helper lemmas for the DFT correctness proof.
 * This file MUST NOT depend on dftCorrectnessTheory (circular dependency).
 *)

Theory dftHelpers
Ancestors
  dftIdempotent dftStructural dftDefs
  venomInst
  list rich_list pred_set sorting relation

(* ===== unique_defs is permutation-invariant ===== *)

Theorem unique_defs_perm:
  !l1 l2.
    unique_defs l1 /\ ALL_DISTINCT l1 /\ PERM l1 l2 ==> unique_defs l2
  (* Permuting an all-distinct list with unique defs preserves unique defs *)
Proof
  simp[unique_defs_def, inst_defs_def] >> rpt strip_tac >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `LENGTH l1 = LENGTH l2` by metis_tac[PERM_LENGTH] >>
  `i < LENGTH l2` by decide_tac >>
  `?a. a < LENGTH l1 /\ EL a l1 = EL i l2` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `?b. b < LENGTH l1 /\ EL b l1 = EL j l2` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `a <> b` by
    (spose_not_then assume_tac >>
     `i < LENGTH l2` by decide_tac >>
     `l2❲i❳ = l2❲j❳` by metis_tac[] >>
     `i = j` by metis_tac[ALL_DISTINCT_EL_IMP] >>
     decide_tac) >>
  Cases_on `a < b`
  >- (first_x_assum (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> metis_tac[])
  >> (`b < a` by decide_tac >>
      once_rewrite_tac[DISJOINT_SYM] >>
      first_x_assum (qspecl_then [`b`,`a`] mp_tac) >> simp[])
QED

(* ===== unique_defs is preserved under FILTER ===== *)

Theorem unique_defs_filter:
  !P l. unique_defs l /\ ALL_DISTINCT l ==> unique_defs (FILTER P l)
  (* Filtering an all-distinct list with unique defs preserves unique defs *)
Proof
  simp[unique_defs_def] >> rpt strip_tac >>
  `ALL_DISTINCT (FILTER P l)` by simp[FILTER_ALL_DISTINCT] >>
  `i < LENGTH (FILTER P l)` by decide_tac >>
  `MEM (EL i (FILTER P l)) l` by metis_tac[EL_MEM, IS_EL_FILTER] >>
  `MEM (EL j (FILTER P l)) l` by metis_tac[EL_MEM, IS_EL_FILTER] >>
  `?a. a < LENGTH l /\ EL a l = EL i (FILTER P l)` by metis_tac[MEM_EL] >>
  `?b. b < LENGTH l /\ EL b l = EL j (FILTER P l)` by metis_tac[MEM_EL] >>
  `a <> b` by
    (spose_not_then assume_tac >>
     `EL i (FILTER P l) = EL j (FILTER P l)` by fs[] >>
     qspecl_then [`FILTER P l`,`i`,`j`] mp_tac ALL_DISTINCT_EL_IMP >>
     simp[] >> decide_tac) >>
  Cases_on `a < b`
  >- (first_x_assum (qspecl_then [`a`,`b`] mp_tac) >> simp[]) >>
  `b < a` by decide_tac >>
  once_rewrite_tac[DISJOINT_SYM] >>
  first_x_assum (qspecl_then [`b`,`a`] mp_tac) >> simp[]
QED

(* ===== PERM_TRANSFER helpers ===== *)

Triviality p_bound[local]:
  !p n i. p PERMUTES count n /\ i < n ==> p i < n
  (* A permutation of count n maps every element below n into count n *)
Proof
  rpt strip_tac >>
  `INJ p (count n) (count n)` by metis_tac[BIJ_DEF] >>
  pop_assum mp_tac >> simp[INJ_DEF, IN_COUNT]
QED

Triviality f_eq_from_bijection[local]:
  !f l1 l2 p n i.
    MAP f l2 = GENLIST (\j. EL (p j) (MAP f l1)) n /\
    i < n /\ p i < LENGTH l1 /\ i < LENGTH l2 ==>
    f (EL i l2) = f (EL (p i) l1)
  (* Corresponding elements under a bijection on f-images have equal f-values *)
Proof
  rpt strip_tac >>
  `EL i (MAP f l2) = EL (p i) (MAP f l1)` suffices_by metis_tac[EL_MAP] >>
  qpat_x_assum `MAP f l2 = GENLIST _ _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  simp[EL_GENLIST]
QED

Triviality g_image_genlist[local]:
  !g l1 l2 p n.
    (!i. i < n ==> g (EL i l2) = g (EL (p i) l1)) /\
    (!i. i < n ==> p i < LENGTH l1) /\
    LENGTH l1 = n /\ LENGTH l2 = n ==>
    MAP g l2 = GENLIST (\i. EL (p i) (MAP g l1)) n
  (* Elementwise g-agreement under a bijection lets g-images be expressed as a GENLIST *)
Proof
  rpt strip_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_MAP, EL_GENLIST, EL_MAP]
QED

(* ===== PERM_TRANSFER ===== *)

Theorem PERM_TRANSFER:
  !f g l1 l2.
    PERM (MAP f l1) (MAP f l2) /\
    ALL_DISTINCT (MAP f l1) /\
    (!x y. MEM x l1 /\ MEM y l2 /\ f x = f y ==> g x = g y) ==>
    PERM (MAP g l1) (MAP g l2)
  (* A permutation on f-images transfers to g-images when f is injective and g agrees with f on matching elements *)
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP f l2)` by metis_tac[ALL_DISTINCT_PERM] >>
  `LENGTH l1 = LENGTH l2` by metis_tac[PERM_LENGTH, LENGTH_MAP] >>
  drule (iffLR PERM_BIJ_IFF) >> simp[LENGTH_MAP] >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  `!i. i < LENGTH l1 ==> p i < LENGTH l1` by metis_tac[p_bound] >>
  `!i. i < LENGTH l1 ==> f (EL i l2) = f (EL (p i) l1)` by
    metis_tac[f_eq_from_bijection] >>
  `!i. i < LENGTH l1 ==> g (EL i l2) = g (EL (p i) l1)` by (
    rpt strip_tac >>
    `MEM (EL i l2) l2` by simp[EL_MEM] >>
    `MEM (EL (p i) l1) l1` by simp[EL_MEM] >>
    metis_tac[]) >>
  `MAP g l2 = GENLIST (\i. EL (p i) (MAP g l1)) (LENGTH l1)` by
    metis_tac[g_image_genlist] >>
  irule (iffRL PERM_BIJ_IFF) >> simp[LENGTH_MAP] >>
  qexists `p` >> simp[]
QED

(* ===== Monomorphic PERM_TRANSFER for instruction inst_id → inst_outputs ===== *)
(* Avoids polymorphic type variable unification issues in tactic proofs *)

Theorem PERM_TRANSFER_inst_id_inst_outputs:
  !l1 l2.
    PERM (MAP (\i:instruction. i.inst_id) l1) (MAP (\i. i.inst_id) l2) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    (!x y. MEM x l1 /\ MEM y l2 /\ x.inst_id = y.inst_id ==>
            x.inst_outputs = y.inst_outputs) ==>
    PERM (MAP (\i. i.inst_outputs) l1) (MAP (\i. i.inst_outputs) l2)
  (* Monomorphic PERM_TRANSFER: permuting by inst_id implies permuting by inst_outputs *)
Proof
  rpt strip_tac >>
  qspecl_then [`(\i:instruction. i.inst_id)`, `(\i:instruction. i.inst_outputs)`, `l1`, `l2`]
    mp_tac PERM_TRANSFER >>
  simp[]
QED

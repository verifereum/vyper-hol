(*
 * merge_jumpdests refines its input.
 *
 * At a LABEL x followed by LABEL y, or by PUSHLABEL y JUMP, the rule
 * renames every PUSHLABEL x in the program to PUSHLABEL y. No instruction
 * moves, so the two runs are related at equal pcs, on the stack and in
 * memory, with Lab x 0 on the original side allowed to be Lab y 0 on the
 * renamed side. The two values differ only as jump targets, and jumping to
 * x gets to y's code with nothing else changed: LABEL x falls through to
 * LABEL y, or pushes y and jumps there. Any other use of Lab x 0 is a
 * label misuse in the original (x is a code label), so it needs no match.
 *
 * TOP-LEVEL:
 *   merge_jumpdests_refines — asm_refines p (FST (merge_jumpdests p))
 *)

Theory asmOptMergeJumpdests
Ancestors
  asmSplice asmSymPc asmSymBridge finalizerContract asmSymSem asmOptimizer
  asmWf asmSem symbolResolve list rich_list finite_map

(* ===== The renamed program's static facts ===== *)

Theorem rename_push_label_facts[local]:
  (rename_push_label x y i = AsmLabel l ⇔ i = AsmLabel l) ∧
  (rename_push_label x y i = AsmDataHeader l ⇔ i = AsmDataHeader l) ∧
  (rename_push_label x y i = AsmDataLabel l ⇔ i = AsmDataLabel l) ∧
  (rename_push_label x y i = AsmOp n ⇔ i = AsmOp n) ∧
  (rename_push_label x y i = AsmPush b ⇔ i = AsmPush b) ∧
  (rename_push_label x y i = AsmPushOfst l d ⇔ i = AsmPushOfst l d) ∧
  (AsmLabel l = rename_push_label x y i ⇔ AsmLabel l = i) ∧
  (AsmDataHeader l = rename_push_label x y i ⇔ AsmDataHeader l = i) ∧
  (AsmDataLabel l = rename_push_label x y i ⇔ AsmDataLabel l = i) ∧
  (is_data_inst (rename_push_label x y i) ⇔ is_data_inst i) ∧
  asm_inst_size (rename_push_label x y i) = asm_inst_size i
Proof
  Cases_on `i` >> rw[rename_push_label_def, is_data_inst_def, asm_inst_size_def]
QED

Theorem rename_push_label_other[local]:
  i ≠ AsmPushLabel x ⇒ rename_push_label x y i = i
Proof
  Cases_on `i` >> rw[rename_push_label_def]
QED

Theorem rename_label_offsets[local]:
  compute_label_offsets (MAP (rename_push_label x y) p) =
  compute_label_offsets p
Proof
  simp[compute_label_offsets_def] >>
  qspec_tac (`(0:num, FEMPTY:string |-> num)`, `acc`) >>
  Induct_on `p` >> simp[] >> rpt gen_tac >> PairCases_on `acc` >>
  Cases_on `h` >> rw[rename_push_label_def, asm_inst_size_def]
QED

Theorem rename_labels_unique[local]:
  asm_labels_unique (MAP (rename_push_label x y) p) ⇔ asm_labels_unique p
Proof
  simp[asm_labels_unique_def, MAP_MAP_o] >> AP_TERM_TAC >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> Cases >> rw[rename_push_label_def]
QED

Theorem rename_filter_data[local]:
  FILTER is_data_inst (MAP (rename_push_label x y) p) = FILTER is_data_inst p
Proof
  Induct_on `p` >> rw[rename_push_label_facts] >>
  Cases_on `h` >> gvs[is_data_inst_def, rename_push_label_def]
QED

Theorem mem_rename[local]:
  (MEM (AsmLabel l) (MAP (rename_push_label x y) p) ⇔ MEM (AsmLabel l) p) ∧
  (MEM (AsmDataHeader l) (MAP (rename_push_label x y) p) ⇔
   MEM (AsmDataHeader l) p) ∧
  (MEM (AsmDataLabel l) (MAP (rename_push_label x y) p) ⇔
   MEM (AsmDataLabel l) p)
Proof
  simp[MEM_MAP, rename_push_label_facts]
QED

Theorem index_of_label_rename[local]:
  INDEX_OF (AsmLabel l) (MAP (rename_push_label x y) p) =
  INDEX_OF (AsmLabel l) p
Proof
  Induct_on `p` >> simp[INDEX_OF_CONS, INDEX_OF_NIL, rename_push_label_facts]
QED

Theorem rename_label_refs[local]:
  MEM l (asm_label_refs (MAP (rename_push_label x y) p)) ⇒
  MEM l (asm_label_refs p) ∨ l = y
Proof
  simp[asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  rename1 `MEM i p` >> Cases_on `i = AsmPushLabel x`
  >- gvs[rename_push_label_def] >>
  gvs[rename_push_label_other] >>
  disj1_tac >> first_assum (irule_at Any) >> simp[]
QED

Theorem rename_encoding_wf[local]:
  asm_encoding_wf p ⇒ asm_encoding_wf (MAP (rename_push_label x y) p)
Proof
  simp[asm_encoding_wf_def, rename_label_offsets] >>
  pairarg_tac >> rw[] >> gvs[EL_MAP, rename_push_label_facts] >>
  metis_tac[]
QED

Theorem rename_data_at_end[local]:
  asm_data_at_end p ⇒ asm_data_at_end (MAP (rename_push_label x y) p)
Proof
  rw[asm_data_at_end_def, EL_MAP] >>
  Cases_on `rename_push_label x y (EL i p)` >> simp[] >>
  gvs[rename_push_label_facts] >> first_x_assum drule >> simp[] >>
  rpt strip_tac >> gvs[EL_MAP, rename_push_label_facts]
QED

Theorem rename_static_wf[local]:
  asm_static_wf p ∧ (MEM (AsmLabel y) p ∨ MEM y (asm_label_refs p)) ⇒
  asm_static_wf (MAP (rename_push_label x y) p)
Proof
  strip_tac >> fs[asm_static_wf_def] >>
  `∀l. MEM l (asm_label_refs (MAP (rename_push_label x y) p)) ⇒
       MEM (AsmLabel l) p ∨ MEM (AsmDataHeader l) p`
    by (rpt strip_tac >> drule rename_label_refs >> metis_tac[]) >>
  `∀i. i < LENGTH p ∧ is_data_inst (EL i (MAP (rename_push_label x y) p)) ⇒
       ∃j l. j ≤ i ∧ EL j (MAP (rename_push_label x y) p) = AsmDataHeader l`
    by (rpt strip_tac >> gvs[EL_MAP, rename_push_label_facts] >>
        first_x_assum drule_all >> strip_tac >>
        qexistsl [`j`, `l`] >> gvs[EL_MAP, rename_push_label_facts]) >>
  fs[rename_labels_unique, mem_rename, rename_encoding_wf,
     rename_data_at_end]
QED

(* ===== The simulation relation ===== *)

(* Lab x 0 on the original side may be Lab y 0 on the renamed side. It
   need not be: a PUSHOFST x 0 still pushes Lab x 0 after the rename. *)
Definition sv_rel_def:
  sv_rel x y v v' ⇔ v' = v ∨ v = Lab x 0 ∧ v' = Lab y 0
End

Definition ml_rel_def:
  ml_rel x y (m : num |-> string # num # num) m' ⇔
    ∀k. OPTREL (λ(l, d, j) (l', d', j').
                  j' = j ∧ sv_rel x y (Lab l d) (Lab l' d'))
          (FLOOKUP m k) (FLOOKUP m' k)
End

(* Memory bytes holding a label value come in blocks of 32 written by one
   MSTORE: bytes from the same block start hold the same label value. So
   MLOAD sees the same intact label on both sides, not x in one and a mix
   of x and y bytes in the other. *)
Definition mem_blocks_ok_def:
  mem_blocks_ok (m : num |-> string # num # num) ⇔
    ∀k1 k2 l1 d1 j1 l2 d2 j2.
      FLOOKUP m k1 = SOME (l1, d1, j1) ∧ FLOOKUP m k2 = SOME (l2, d2, j2) ⇒
      j1 < 32 ∧ (k1 + j2 = k2 + j1 ⇒ l1 = l2 ∧ d1 = d2)
End

Definition rn_rel_def:
  rn_rel x y ss ss' ⇔
    ss'.sym_base = ss.sym_base ∧ ss.sym_base.as_stack = [] ∧
    ss'.sym_own_code = ss.sym_own_code ∧
    LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
    ml_rel x y ss.sym_mem_labels ss'.sym_mem_labels ∧
    mem_blocks_ok ss.sym_mem_labels ∧ mem_blocks_ok ss'.sym_mem_labels
End

(* What one step of the original gives against one step of the renamed
   program; errors and label misuses in the original need nothing. *)
Definition res_rel_def:
  res_rel x y (SymOK t) r' = (∃t'. r' = SymOK t' ∧ rn_rel x y t t') ∧
  res_rel x y (SymHalt t) r' =
    (∃t'. r' = SymHalt t' ∧ t'.sym_base = t.sym_base) ∧
  res_rel x y (SymRevert t) r' =
    (∃t'. r' = SymRevert t' ∧ t'.sym_base = t.sym_base) ∧
  res_rel x y (SymFault t) r' =
    (∃t'. r' = SymFault t' ∧ t'.sym_base = t.sym_base) ∧
  res_rel x y (SymError e) r' = T ∧
  res_rel x y (SymBad e) r' = T
End

Theorem sv_rel_refl[local,simp]:
  sv_rel x y v v
Proof
  simp[sv_rel_def]
QED

Theorem sv_rel_val[local]:
  (sv_rel x y (Val w) v' ⇔ v' = Val w) ∧
  (sv_rel x y v (Val w) ⇔ v = Val w)
Proof
  Cases_on `v` >> rw[sv_rel_def] >> metis_tac[]
QED

Theorem list_rel_sv_refl[local,simp]:
  LIST_REL (sv_rel x y) l l
Proof
  simp[LIST_REL_EL_EQN]
QED

(* ===== The memory label map ===== *)

Theorem ml_rel_fdom[local]:
  ml_rel x y m m' ⇒ FDOM m' = FDOM m
Proof
  rw[ml_rel_def, pred_setTheory.EXTENSION, FLOOKUP_DEF] >>
  first_x_assum (qspec_then `x'` mp_tac) >> rw[] >> gvs[]
QED

Theorem ml_rel_clear[local]:
  ml_rel x y m m' ⇒
  ml_rel x y (mem_labels_clear m P) (mem_labels_clear m' P)
Proof
  rw[ml_rel_def, mem_labels_clear_def, FLOOKUP_DRESTRICT] >> rw[]
QED

Theorem blocks_clear[local]:
  mem_blocks_ok m ⇒ mem_blocks_ok (mem_labels_clear m P)
Proof
  rw[mem_blocks_ok_def, mem_labels_clear_def, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

Theorem ml_rel_store[local]:
  ml_rel x y m m' ∧ sv_rel x y (Lab l d) (Lab l' d') ⇒
  ml_rel x y (m |++ GENLIST (λj. (a + j, (l, d, j))) 32)
             (m' |++ GENLIST (λj. (a + j, (l', d', j))) 32)
Proof
  rw[ml_rel_def, mstore_labels_lookup] >> IF_CASES_TAC >>
  fs[optionTheory.OPTREL_SOME]
QED

Theorem blocks_store[local]:
  mem_blocks_ok m ⇒
  mem_blocks_ok (m |++ GENLIST (λj. (a + j, (l, d, j))) 32)
Proof
  rw[mem_blocks_ok_def, mstore_labels_lookup] >>
  `∀k l d j. FLOOKUP m k = SOME (l, d, j) ⇒ j < 32` by metis_tac[] >>
  Cases_on `a ≤ k1 ∧ k1 < a + 32` >> Cases_on `a ≤ k2 ∧ k2 < a + 32` >>
  gvs[] >> rpt strip_tac >> res_tac >> gvs[]
QED

Theorem ml_rel_store_comm[local] =
  ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] ml_rel_store

Theorem blocks_store_comm[local] =
  ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] blocks_store

Theorem block_follow[local]:
  ∀m m' off l d l' d'.
  (∀k l d j. FLOOKUP m k = SOME (l, d, j) ⇒
             ∃l' d'. FLOOKUP m' k = SOME (l', d', j)) ∧
  mem_blocks_ok m' ∧ FLOOKUP m' off = SOME (l', d', 0) ∧
  (∀i. i < 32 ⇒ FLOOKUP m (i + off) = SOME (l, d, i)) ⇒
  ∀i. i < 32 ⇒ FLOOKUP m' (i + off) = SOME (l', d', i)
Proof
  rpt gen_tac >> rw[mem_blocks_ok_def] >>
  `∃l2 d2. FLOOKUP m' (i + off) = SOME (l2, d2, i)` by metis_tac[] >>
  qpat_x_assum `∀k1 k2 l1 d1 j1 l2 d2 j2. _`
    (qspecl_then [`off`, `i + off`, `l'`, `d'`, `0`, `l2`, `d2`, `i`] mp_tac) >>
  simp[]
QED

Theorem mem_label_at_rel[local]:
  ml_rel x y m m' ∧ mem_blocks_ok m ∧ mem_blocks_ok m' ⇒
  OPTREL (λ(l, d) (l', d'). sv_rel x y (Lab l d) (Lab l' d'))
    (mem_label_at m off) (mem_label_at m' off)
Proof
  rw[ml_rel_def] >>
  `∀k l d j. FLOOKUP m k = SOME (l, d, j) ⇒
             ∃l' d'. FLOOKUP m' k = SOME (l', d', j)`
    by (rpt strip_tac >>
        qpat_x_assum `∀k. OPTREL _ _ _` (qspec_then `k` mp_tac) >>
        Cases_on `FLOOKUP m' k` >> gvs[optionTheory.OPTREL_def] >>
        rename1 `FLOOKUP m' k = SOME q` >> PairCases_on `q` >> gvs[]) >>
  `∀k l d j. FLOOKUP m' k = SOME (l, d, j) ⇒
             ∃l' d'. FLOOKUP m k = SOME (l', d', j)`
    by (rpt strip_tac >>
        qpat_x_assum `∀k. OPTREL _ _ _` (qspec_then `k` mp_tac) >>
        Cases_on `FLOOKUP m k` >> gvs[optionTheory.OPTREL_def] >>
        rename1 `FLOOKUP m k = SOME q` >> PairCases_on `q` >> gvs[]) >>
  qpat_x_assum `∀k. OPTREL _ _ _` (qspec_then `off` mp_tac) >>
  simp[mem_label_at_def] >>
  Cases_on `FLOOKUP m off` >> Cases_on `FLOOKUP m' off` >>
  simp[optionTheory.OPTREL_def] >>
  rename1 `FLOOKUP m off = SOME e` >> rename1 `FLOOKUP m' off = SOME e'` >>
  PairCases_on `e` >> PairCases_on `e'` >> simp[] >> strip_tac >> gvs[] >>
  simp[EVERY_MEM, rich_listTheory.MEM_COUNT_LIST] >>
  `e'2 = 0 ⇒
   ((∀i. i < 32 ⇒ FLOOKUP m (i + off) = SOME (e0, e1, i)) ⇔
    (∀i. i < 32 ⇒ FLOOKUP m' (i + off) = SOME (e'0, e'1, i)))`
    by (strip_tac >> gvs[] >> eq_tac >> strip_tac
        >- (qspecl_then [`m`, `m'`, `off`, `e0`, `e1`, `e'0`, `e'1`]
              mp_tac block_follow >>
            impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[])
        >- (qspecl_then [`m'`, `m`, `off`, `e'0`, `e'1`, `e0`, `e1`]
              mp_tac block_follow >>
            impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[])) >>
  qabbrev_tac `A = ∀i. i < 32 ⇒ FLOOKUP m (i + off) = SOME (e0, e1, i)` >>
  qabbrev_tac `B = ∀i. i < 32 ⇒ FLOOKUP m' (i + off) = SOME (e'0, e'1, i)` >>
  Cases_on `e'2 = 0` >> Cases_on `A` >> Cases_on `B` >>
  gvs[optionTheory.OPTREL_def, EXISTS_MEM, rich_listTheory.MEM_COUNT_LIST] >>
  metis_tac[]
QED

(* ===== One step ===== *)

Theorem set_stack_rel[local]:
  rn_rel x y ss ss' ∧ LIST_REL (sv_rel x y) stk stk' ⇒
  res_rel x y (sym_set_stack stk ss) (sym_set_stack stk' ss')
Proof
  rw[sym_set_stack_def, res_rel_def, rn_rel_def, asm_next_def]
QED

Theorem push_lab_rel[local]:
  rn_rel x y ss ss' ∧ LIST_REL (sv_rel x y) stk stk' ⇒
  res_rel x y (sym_push_lab l d stk ss) (sym_push_lab l d stk' ss')
Proof
  rw[sym_push_lab_def, res_rel_def] >> irule set_stack_rel >> simp[]
QED

Theorem lift_rel[local]:
  rn_rel x y ss ss' ∧ ml_rel x y labs labs' ∧
  mem_blocks_ok labs ∧ mem_blocks_ok labs' ⇒
  res_rel x y (sym_lift k labs ss r) (sym_lift k labs' ss' r)
Proof
  Cases_on `r` >> rw[sym_lift_def, res_rel_def, rn_rel_def] >>
  irule LIST_REL_APPEND_suff >> simp[rich_listTheory.EVERY2_DROP]
QED

Theorem sval_val_rel[local]:
  ∀l l' a. LIST_REL (sv_rel x y) l l' ∧ OPT_MMAP sval_val l = SOME a ⇒
           l' = l
Proof
  Induct >> simp[] >> Cases >> simp[sval_val_def, sv_rel_val] >>
  rw[] >> gvs[] >> metis_tac[]
QED

Theorem concrete_rel[local]:
  rn_rel x y ss ss' ⇒
  res_rel x y (sym_step_concrete name ss) (sym_step_concrete name ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss'.sym_base = ss.sym_base ∧
   FDOM ss'.sym_mem_labels = FDOM ss.sym_mem_labels`
    by (gvs[rn_rel_def] >> metis_tac[ml_rel_fdom]) >>
  imp_res_tac LIST_REL_LENGTH >>
  simp[sym_step_concrete_def] >> rw[res_rel_def] >>
  Cases_on `OPT_MMAP sval_val (TAKE (asm_op_arity name) ss.sym_stack)` >>
  simp[res_rel_def] >>
  `TAKE (asm_op_arity name) ss'.sym_stack =
   TAKE (asm_op_arity name) ss.sym_stack`
    by (irule sval_val_rel >> simp[] >> metis_tac[EVERY2_TAKE]) >>
  simp[mem_labels_hit_def] >> rw[res_rel_def] >>
  irule lift_rel >> gvs[rn_rel_def] >>
  simp[ml_rel_clear, blocks_clear]
QED

Theorem add_rel[local]:
  rn_rel x y ss ss' ∧ ¬sym_data_label p env x ⇒
  res_rel x y (sym_add p env ss) (sym_add p env ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack` by fs[rn_rel_def] >>
  simp[sym_add_def] >>
  Cases_on `ss.sym_stack` >> Cases_on `ss'.sym_stack` >> gvs[concrete_rel] >>
  rename1 `sv_rel x y v1 v1'` >> rename1 `LIST_REL _ t1 t1'` >>
  Cases_on `t1` >> Cases_on `t1'` >> gvs[]
  >- (Cases_on `v1` >> gvs[sv_rel_def, concrete_rel]) >>
  rename1 `sv_rel x y v2 v2'` >>
  Cases_on `v1` >> Cases_on `v2` >> gvs[sv_rel_def, concrete_rel] >>
  rw[res_rel_def] >> gvs[push_lab_rel]
QED

Theorem mstore_rel[local]:
  rn_rel x y ss ss' ⇒ res_rel x y (sym_mstore ss) (sym_mstore ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  simp[sym_mstore_def, Excl "GENLIST_NUMERALS"] >>
  Cases_on `ss.sym_stack` >> Cases_on `ss'.sym_stack` >>
  gvs[concrete_rel, Excl "GENLIST_NUMERALS"] >>
  rename1 `sv_rel x y v1 v1'` >> rename1 `LIST_REL _ t1 t1'` >>
  Cases_on `t1` >> Cases_on `t1'` >> gvs[Excl "GENLIST_NUMERALS"]
  >- (Cases_on `v1` >> gvs[sv_rel_def, concrete_rel]) >>
  rename1 `sv_rel x y v2 v2'` >>
  Cases_on `v1` >> gvs[sv_rel_def, concrete_rel, Excl "GENLIST_NUMERALS"] >>
  TRY (Cases_on `v2`) >> gvs[concrete_rel, Excl "GENLIST_NUMERALS"] >>
  irule lift_rel >> rpt conj_tac >>
  TRY (irule ml_rel_store_comm) >> TRY (irule blocks_store_comm) >>
  fs[rn_rel_def, sv_rel_def]
QED

Theorem mload_rel[local]:
  rn_rel x y ss ss' ⇒ res_rel x y (sym_mload ss) (sym_mload ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack` by fs[rn_rel_def] >>
  simp[sym_mload_def] >>
  Cases_on `ss.sym_stack` >> Cases_on `ss'.sym_stack` >> gvs[concrete_rel] >>
  rename1 `sv_rel x y v1 v1'` >>
  Cases_on `v1` >> gvs[sv_rel_def, concrete_rel] >>
  rename1 `w2n off` >>
  `OPTREL (λ(l, d) (l', d'). sv_rel x y (Lab l d) (Lab l' d'))
     (mem_label_at ss.sym_mem_labels (w2n off))
     (mem_label_at ss'.sym_mem_labels (w2n off))`
    by (irule mem_label_at_rel >> fs[rn_rel_def]) >>
  Cases_on `mem_label_at ss.sym_mem_labels (w2n off)` >>
  Cases_on `mem_label_at ss'.sym_mem_labels (w2n off)` >>
  gvs[optionTheory.OPTREL_def, concrete_rel] >>
  rename1 `mem_label_at ss.sym_mem_labels _ = SOME q` >>
  rename1 `mem_label_at ss'.sym_mem_labels _ = SOME q'` >>
  PairCases_on `q` >> PairCases_on `q'` >> gvs[] >>
  gvs[res_rel_def, rn_rel_def, asm_next_def]
QED

Theorem codecopy_rel[local]:
  rn_rel x y ss ss' ∧ ¬sym_data_label p env x ⇒
  res_rel x y (sym_codecopy p env ss) (sym_codecopy p env ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  Cases_on `∃dst l d sz stk.
              ss.sym_stack = Val dst :: Lab l d :: Val sz :: stk`
  >- (gvs[] >> gvs[LIST_REL_CONS1, sv_rel_val] >>
      simp[sym_codecopy_def] >>
      gvs[sv_rel_def] >> rw[res_rel_def] >> gvs[] >>
      irule lift_rel >> fs[rn_rel_def] >>
      simp[ml_rel_clear, blocks_clear]) >>
  Cases_on `∃dst src sz stk.
              ss.sym_stack = Val dst :: Val src :: Val sz :: stk`
  >- (gvs[] >> gvs[LIST_REL_CONS1, sv_rel_val] >>
      simp[sym_codecopy_def] >>
      `ss'.sym_own_code = ss.sym_own_code` by fs[rn_rel_def] >>
      simp[] >> irule lift_rel >> fs[rn_rel_def] >>
      simp[ml_rel_clear, blocks_clear]) >>
  `∃e. sym_codecopy p env ss = SymError e ∨ sym_codecopy p env ss = SymBad e`
    by (simp[sym_codecopy_def] >>
        Cases_on `ss.sym_stack` >> simp[] >>
        rename1 `ss.sym_stack = v1 :: t1` >> Cases_on `t1` >> simp[] >>
        rename1 `ss.sym_stack = v1 :: v2 :: t2` >>
        Cases_on `t2` >> Cases_on `v1` >> Cases_on `v2` >> simp[] >>
        rename1 `ss.sym_stack = _ :: _ :: v3 :: _` >>
        Cases_on `v3` >> gvs[]) >>
  gvs[res_rel_def]
QED

Theorem dup_swap_rel[local]:
  rn_rel x y ss ss' ⇒
  res_rel x y (sym_dup n ss) (sym_dup n ss') ∧
  res_rel x y (sym_swap n ss) (sym_swap n ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack` by fs[rn_rel_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  rw[sym_dup_def, sym_swap_def, res_rel_def] >>
  irule set_stack_rel >> gvs[LIST_REL_EL_EQN] >>
  Cases_on `ss.sym_stack` >> Cases_on `ss'.sym_stack` >> gvs[] >>
  rw[EL_LUPDATE] >>
  TRY (first_x_assum (qspec_then `0` mp_tac) >> simp[] >> NO_TAC) >>
  first_x_assum irule >> simp[]
QED

Theorem step_op_rel[local]:
  rn_rel x y ss ss' ∧ ¬sym_data_label p env x ∧
  name ≠ "JUMP" ∧ name ≠ "JUMPI" ⇒
  res_rel x y (sym_step_op p env name ss) (sym_step_op p env name ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack` by fs[rn_rel_def] >>
  simp[sym_step_op_def] >>
  rw[add_rel, mstore_rel, mload_rel, codecopy_rel, res_rel_def]
  >- (Cases_on `ss.sym_stack` >> Cases_on `ss'.sym_stack` >>
      gvs[res_rel_def] >> irule set_stack_rel >> simp[])
  >- (`ss'.sym_own_code = ss.sym_own_code` by fs[rn_rel_def] >>
      irule set_stack_rel >> simp[sv_rel_def]) >>
  rpt CASE_TAC >> gvs[dup_swap_rel, concrete_rel]
QED

Theorem step_rel[local]:
  rn_rel x y ss ss' ∧ ¬sym_data_label p env x ∧
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ⇒
  res_rel x y (sym_step p env inst ss)
              (sym_step p env (rename_push_label x y inst) ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  Cases_on `inst` >> simp[sym_step_def, rename_push_label_def] >>
  TRY (irule step_op_rel >> simp[] >> strip_tac >> gvs[] >> NO_TAC) >>
  TRY (irule push_lab_rel >> simp[] >> NO_TAC) >>
  TRY (rw[] >> irule set_stack_rel >> simp[sv_rel_def] >> NO_TAC) >>
  irule lift_rel >> fs[rn_rel_def]
QED

Theorem sym_jump_dest_rename[local]:
  sym_jump_dest (MAP (rename_push_label x y) p) v = sym_jump_dest p v
Proof
  Cases_on `v` >> rw[sym_jump_dest_def, index_of_label_rename]
QED

Theorem jump_rel[local]:
  rn_rel x y ss ss' ∧ (name = "JUMP" ∨ name = "JUMPI") ∧
  sym_step_op p env name ss = SymOK t ⇒
  (∃t'. sym_step_op (MAP (rename_push_label x y) p) env name ss' = SymOK t' ∧
        rn_rel x y t t') ∨
  (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc ∧
   ∀j. INDEX_OF (AsmLabel y) p = SOME j ⇒
       ∃t'. sym_step_op (MAP (rename_push_label x y) p) env name ss' =
              SymOK t' ∧
            rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  gvs[sym_step_op_def, sym_jump_def, sym_jumpi_def, sym_set_stack_def,
      AllCaseEqs()] >>
  gvs[LIST_REL_CONS1, sv_rel_val, sym_jump_dest_rename] >>
  gvs[sv_rel_def, sym_jump_dest_rename, sym_jump_dest_def,
      index_of_label_rename] >>
  gvs[rn_rel_def, asm_next_def]
QED

Theorem sym_step_jump_ok[local]:
  (name = "JUMP" ∨ name = "JUMPI") ⇒
  (∃t. sym_step_op p env name ss = SymOK t) ∨
  (∃e. sym_step_op p env name ss = SymError e) ∨
  (∃e. sym_step_op p env name ss = SymBad e)
Proof
  rw[sym_step_op_def, sym_jump_def, sym_jumpi_def, sym_set_stack_def] >>
  rpt CASE_TAC >> simp[]
QED

Theorem rename_step[local]:
  rn_rel x y ss ss' ∧ ¬sym_data_label p env x ⇒
  case sym_step p env inst ss of
    SymOK t =>
      (∃t'. sym_step (MAP (rename_push_label x y) p) env
              (rename_push_label x y inst) ss' = SymOK t' ∧
            rn_rel x y t t') ∨
      (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc ∧
       ∀j. INDEX_OF (AsmLabel y) p = SOME j ⇒
         ∃t'. sym_step (MAP (rename_push_label x y) p) env
                (rename_push_label x y inst) ss' = SymOK t' ∧
              rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t')
  | r => res_rel x y r (sym_step (MAP (rename_push_label x y) p) env
                         (rename_push_label x y inst) ss')
Proof
  strip_tac >>
  Cases_on `inst = AsmOp "JUMP" ∨ inst = AsmOp "JUMPI"`
  >- (`∃name. inst = AsmOp name ∧ (name = "JUMP" ∨ name = "JUMPI")`
        by metis_tac[] >>
      `(∃t. sym_step_op p env name ss = SymOK t) ∨
       (∃e. sym_step_op p env name ss = SymError e) ∨
       (∃e. sym_step_op p env name ss = SymBad e)`
        by metis_tac[sym_step_jump_ok] >>
      qpat_x_assum `inst = _` SUBST_ALL_TAC >>
      simp[rename_push_label_def, sym_step_def] >>
      gvs[res_rel_def] >> metis_tac[jump_rel]) >>
  `sym_step (MAP (rename_push_label x y) p) env
     (rename_push_label x y inst) ss' =
   sym_step p env (rename_push_label x y inst) ss'`
    by (irule (GSYM sym_step_prog_cong) >> simp[mem_rename] >>
        Cases_on `inst` >> rw[rename_push_label_def] >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI"` by fs[] >>
  drule_all step_rel >>
  Cases_on `sym_step p env inst ss` >> simp[res_rel_def]
QED

(* ===== Jumping to x gets to y ===== *)

Theorem sym_step_label_skip[local]:
  ss.sym_base.as_stack = [] ⇒
  sym_step p env (AsmLabel l) ss =
  SymOK (ss with sym_base := ss.sym_base with
                   as_pc := ss.sym_base.as_pc + 1)
Proof
  rw[sym_step_def, asm_step_def, sym_lift_def, asm_next_def] >>
  simp[sym_state_component_equality, asmSemTheory.asm_state_component_equality]
QED

Theorem rename_skip[local]:
  p = pre ++ AsmLabel x :: next :: sfx ∧ asm_labels_unique p ∧
  (next = AsmLabel y ∧ y ≠ x ∨
   next = AsmPushLabel y ∧ ∃more. sfx = AsmOp "JUMP" :: more) ∧
  t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ∧
  sym_terminal (sym_run p env fuel t) ⇒
  ∃j fuel2. INDEX_OF (AsmLabel y) p = SOME j ∧ fuel2 < fuel ∧
    sym_run p env fuel t =
    sym_run p env fuel2 (t with sym_base := t.sym_base with as_pc := j)
Proof
  strip_tac >> qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `next = _` SUBST_ALL_TAC
  >- (
    `¬MEM (AsmLabel y) pre`
      by (irule asm_labels_unique_append_not_mem >>
          qexists_tac `AsmLabel x :: AsmLabel y :: sfx` >> fs[]) >>
    `INDEX_OF (AsmLabel y) (pre ++ AsmLabel x :: AsmLabel y :: sfx) =
     SOME (LENGTH pre + 1)`
      by simp[INDEX_OF_APPEND, INDEX_OF_CONS] >>
    `sym_steps (pre ++ AsmLabel x :: AsmLabel y :: sfx) env 1 t =
     SymOK (t with sym_base := t.sym_base with as_pc := LENGTH pre + 1)`
      by simp[sym_steps_pos, EL_APPEND_EQN, sym_step_label_skip,
              sym_steps_def] >>
    drule_then (qspec_then `1` mp_tac) sym_run_terminal_steps >>
    simp[] >> strip_tac >> qexists_tac `fuel - 1` >> simp[]) >>
  qpat_x_assum `sfx = _` SUBST_ALL_TAC >>
  qabbrev_tac `p = pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more` >>
  qabbrev_tac `t1 = t with sym_base := t.sym_base with
                      as_pc := LENGTH pre + 1` >>
  qabbrev_tac `t2 = t1 with <| sym_base := asm_next t1.sym_base;
                               sym_stack := Lab y 0 :: t.sym_stack |>` >>
  `LENGTH pre < LENGTH p ∧ EL (LENGTH pre) p = AsmLabel x ∧
   LENGTH pre + 1 < LENGTH p ∧ EL (LENGTH pre + 1) p = AsmPushLabel y ∧
   LENGTH pre + 2 < LENGTH p ∧ EL (LENGTH pre + 2) p = AsmOp "JUMP"`
    by simp[Abbr `p`, EL_APPEND_EQN] >>
  `sym_step p env (AsmLabel x) t = SymOK t1`
    by simp[Abbr `t1`, sym_step_label_skip] >>
  `sym_step p env (AsmPushLabel y) t1 = SymOK t2`
    by (simp[Abbr `t2`, sym_step_push_label] >> simp[Abbr `t1`]) >>
  `t1.sym_base.as_pc = LENGTH pre + 1 ∧ t2.sym_base.as_pc = LENGTH pre + 2 ∧
   t2.sym_stack = Lab y 0 :: t.sym_stack`
    by simp[Abbr `t1`, Abbr `t2`, asm_next_def] >>
  Cases_on `INDEX_OF (AsmLabel y) p`
  >- (
    `sym_steps p env 3 t = SymBad "jump target"`
      by (simp[sym_steps_pos] >>
          simp[sym_step_def, sym_step_op_def, sym_jump_def,
               sym_jump_dest_def]) >>
    drule_then (qspec_then `3` mp_tac) sym_run_terminal_steps >>
    simp[] >> strip_tac >> gvs[sym_terminal_def]) >>
  rename1 `SOME j` >>
  `sym_steps p env 3 t =
   SymOK (t with sym_base := t.sym_base with as_pc := j)`
    by (simp[sym_steps_pos] >>
        simp[sym_step_def, sym_step_op_def, sym_jump_def,
             sym_jump_dest_def, sym_steps_def] >>
        simp[Abbr `t2`, Abbr `t1`, asm_next_def,
             sym_state_component_equality,
             asmSemTheory.asm_state_component_equality]) >>
  drule_then (qspec_then `3` mp_tac) sym_run_terminal_steps >>
  simp[] >> strip_tac >> qexists_tac `fuel - 3` >> simp[]
QED

(* ===== Runs ===== *)

Theorem rename_run[local]:
  ∀p i x y env.
  asm_static_wf p ∧ INDEX_OF (AsmLabel x) p = SOME i ∧
  (∀t fuel. t.sym_base.as_pc = i ∧ t.sym_base.as_stack = [] ∧
            sym_terminal (sym_run p env fuel t) ⇒
            ∃j fuel2. INDEX_OF (AsmLabel y) p = SOME j ∧ fuel2 < fuel ∧
              sym_run p env fuel t =
              sym_run p env fuel2
                (t with sym_base := t.sym_base with as_pc := j)) ⇒
  ∀fuel ss ss'.
    rn_rel x y ss ss' ∧ sym_terminal (sym_run p env fuel ss) ⇒
    ∃fuel'. sym_result_rel (sym_run p env fuel ss)
              (sym_run (MAP (rename_push_label x y) p) env fuel' ss')
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (AsmLabel x) p`
    by metis_tac[INDEX_OF_eq_NONE, optionTheory.NOT_SOME_NONE] >>
  `¬sym_data_label p env x`
    by (fs[asm_static_wf_def, sym_data_label_def] >> metis_tac[]) >>
  completeInduct_on `fuel` >> rpt strip_tac >>
  `fuel ≠ 0 ∧ ss.sym_base.as_pc < LENGTH p`
    by (spose_not_then strip_assume_tac >>
        qpat_x_assum `sym_terminal _` mp_tac >>
        rw[Once sym_run_def, sym_terminal_def] >> gvs[]) >>
  `ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  `∀f. sym_run (MAP (rename_push_label x y) p) env (SUC f) ss' =
       case sym_step (MAP (rename_push_label x y) p) env
              (rename_push_label x y (EL ss.sym_base.as_pc p)) ss' of
         SymOK t' => sym_run (MAP (rename_push_label x y) p) env f t'
       | r => r` by simp[Once sym_run_def, EL_MAP] >>
  qpat_x_assum `sym_terminal _` mp_tac >>
  simp[Once sym_run_def] >>
  mp_tac (Q.INST [`inst` |-> `EL ss.sym_base.as_pc p`] rename_step) >>
  simp[] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >>
  simp[res_rel_def, sym_terminal_def] >> rpt (disch_then assume_tac)
  >- (
    rename1 `sym_step p env _ ss = SymOK t` >>
    `sym_run p env fuel ss = sym_run p env (fuel - 1) t`
      by simp[Once sym_run_def] >>
    pop_assum SUBST1_TAC >>
    `t.sym_base.as_stack = []`
      by (irule sym_step_base_stack >> fs[rn_rel_def] >> metis_tac[]) >>
    qpat_x_assum `(∃t'. _) ∨ _` strip_assume_tac
    >- (qpat_x_assum `∀m. m < fuel ⇒ _` (qspec_then `fuel - 1` mp_tac) >>
        simp[] >> disch_then drule_all >> strip_tac >>
        qexists_tac `SUC fuel'` >> simp[]) >>
    gvs[] >>
    qpat_x_assum `∀t fuel. _ ⇒ ∃j fuel2. _`
      (qspecl_then [`t`, `fuel - 1`] mp_tac) >>
    simp[] >> strip_tac >>
    qpat_x_assum `∀j. _ ⇒ ∃t'. _` drule >> strip_tac >>
    qpat_x_assum `sym_run p env (fuel - 1) t = _` (fn th => fs[th]) >>
    qpat_x_assum `∀m. m < fuel ⇒ _` (qspec_then `fuel2` mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac >>
    qexists_tac `SUC fuel'` >> simp[]) >>
  `sym_run p env fuel ss = sym_step p env (EL ss.sym_base.as_pc p) ss`
    by simp[Once sym_run_def] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `∀f. _` (qspec_then `0` assume_tac) >>
  qexists_tac `SUC 0` >> gvs[sym_result_rel_def, sym_obs_def]
QED

(* ===== One rename ===== *)

Theorem rename_refines[local]:
  (next = AsmLabel y ∧ y ≠ x ∨ next = AsmPushLabel y ∧ third = AsmOp "JUMP") ⇒
  asm_refines (pre ++ AsmLabel x :: next :: third :: more)
    (MAP (rename_push_label x y) (pre ++ AsmLabel x :: next :: third :: more))
Proof
  strip_tac >>
  qabbrev_tac `P = pre ++ AsmLabel x :: next :: third :: more` >>
  simp[asm_refines_def, rename_filter_data] >>
  strip_tac >>
  `asm_static_wf (MAP (rename_push_label x y) P)`
    by (irule rename_static_wf >>
        simp[Abbr `P`, asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        metis_tac[MEM, MEM_APPEND]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  rpt strip_tac >>
  `asm_labels_unique P` by fs[asm_static_wf_def] >>
  `INDEX_OF (AsmLabel x) P = SOME (LENGTH pre)`
    by (`¬MEM (AsmLabel x) pre`
          by (irule asm_labels_unique_append_not_mem >>
              qexists_tac `AsmLabel x :: next :: third :: more` >>
              fs[Abbr `P`]) >>
        simp[Abbr `P`, INDEX_OF_APPEND, INDEX_OF_CONS]) >>
  `∀t fuel. t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ∧
            sym_terminal (sym_run P env fuel t) ⇒
            ∃j fuel2. INDEX_OF (AsmLabel y) P = SOME j ∧ fuel2 < fuel ∧
              sym_run P env fuel t =
              sym_run P env fuel2
                (t with sym_base := t.sym_base with as_pc := j)`
    by (qx_genl_tac [`t`, `f`] >> strip_tac >>
        mp_tac (Q.INST [`p` |-> `P`, `sfx` |-> `third :: more`,
                        `fuel` |-> `f`] rename_skip) >>
        fs[Abbr `P`]) >>
  `∀fuel ss ss'.
     rn_rel x y ss ss' ∧ sym_terminal (sym_run P env fuel ss) ⇒
     ∃fuel'. sym_result_rel (sym_run P env fuel ss)
               (sym_run (MAP (rename_push_label x y) P) env fuel' ss')`
    by (qspecl_then [`P`, `LENGTH pre`, `x`, `y`, `env`] mp_tac rename_run >>
        impl_tac >- simp[] >>
        disch_then ACCEPT_TAC) >>
  first_x_assum irule >>
  simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def]
QED

(* ===== The walk ===== *)

Theorem merge_jumpdests_walk_refines[local]:
  ∀n done rest changed.
    LENGTH rest = n ⇒
    asm_refines (REVERSE done ++ rest)
      (FST (merge_jumpdests_walk done rest changed))
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `∀d r c. LENGTH r < LENGTH rest ⇒
           asm_refines (REVERSE d ++ r) (FST (merge_jumpdests_walk d r c))`
    by metis_tac[] >>
  qpat_x_assum `∀m. m < n ⇒ _` kall_tac >>
  Cases_on `rest`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_refl] >>
  rename1 `h :: t` >> Cases_on `t`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_refl] >>
  rename1 `h :: next :: t` >> Cases_on `t`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_refl] >>
  rename1 `h :: next :: third :: more` >>
  qpat_x_assum `LENGTH _ = n` kall_tac >>
  Cases_on `∃x. h = AsmLabel x`
  >- (
    pop_assum (qx_choose_then `x` SUBST_ALL_TAC) >>
    Cases_on `∃y. next = AsmLabel y ∧ y ≠ x ∨
                  next = AsmPushLabel y ∧ third = AsmOp "JUMP"`
    >- (
      pop_assum (qx_choose_then `y` assume_tac) >>
      `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
       merge_jumpdests_walk
         (AsmLabel x :: MAP (rename_push_label x y) done)
         (MAP (rename_push_label x y) (next :: third :: more))
         (changed ∨
          push_label_used x (REVERSE done ++ AsmLabel x :: next :: third :: more))`
        by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
            qpat_x_assum `_ ∨ _` strip_assume_tac >>
            gvs[LET_THM, rename_push_label_other]) >>
      pop_assum SUBST1_TAC >>
      irule asm_refines_trans >>
      qexists_tac `MAP (rename_push_label x y)
                     (REVERSE done ++ AsmLabel x :: next :: third :: more)` >>
      conj_tac
      >- (irule rename_refines >> metis_tac[]) >>
      qmatch_goalsub_abbrev_tac `merge_jumpdests_walk _ _ cc` >>
      qpat_x_assum `∀d r c. _`
        (qspecl_then [`AsmLabel x :: MAP (rename_push_label x y) done`,
                      `MAP (rename_push_label x y) (next :: third :: more)`,
                      `cc`] mp_tac) >>
      simp[MAP_REVERSE, rename_push_label_other] >>
      REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]) >>
    `merge_jumpdests_walk done (AsmLabel x :: next :: third :: more) changed =
     merge_jumpdests_walk (AsmLabel x :: done) (next :: third :: more) changed`
      by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
          Cases_on `next` >> gvs[LET_THM] >> rw[] >> gvs[]) >>
    pop_assum SUBST1_TAC >>
    qpat_x_assum `∀d r c. _`
      (qspecl_then [`AsmLabel x :: done`, `next :: third :: more`,
                    `changed`] mp_tac) >>
    simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]) >>
  `merge_jumpdests_walk done (h :: next :: third :: more) changed =
   merge_jumpdests_walk (h :: done) (next :: third :: more) changed`
    by (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [merge_jumpdests_walk_def])) >>
        Cases_on `h` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `∀d r c. _`
    (qspecl_then [`h :: done`, `next :: third :: more`, `changed`] mp_tac) >>
  simp[] >> REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
QED

Theorem merge_jumpdests_refines:
  ∀p. asm_refines p (FST (merge_jumpdests p))
Proof
  simp[merge_jumpdests_def] >> rpt gen_tac >>
  qspecl_then [`LENGTH p`, `[]`, `p`, `F`] mp_tac merge_jumpdests_walk_refines >>
  simp[]
QED

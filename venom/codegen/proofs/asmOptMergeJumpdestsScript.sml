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
Ancestors bool[qualified,ignore_grammar] arithmetic[qualified,ignore_grammar]
  asmSpliceWithin asmRefinesWithin asmSymSemWithin
  asmSplice asmSymPc asmSymBridge finalizerContract asmSymSem asmOptimizer
  asmWf asmSem symbolResolve list rich_list finite_map

(* ===== The renamed program's static facts ===== *)

Theorem rename_push_label_facts:
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

Theorem rename_filter_data:
  FILTER is_data_inst (MAP (rename_push_label x y) p) = FILTER is_data_inst p
Proof
  Induct_on `p` >> rw[rename_push_label_facts] >>
  Cases_on `h` >> gvs[is_data_inst_def, rename_push_label_def]
QED

Theorem mem_rename:
  (MEM (AsmLabel l) (MAP (rename_push_label x y) p) ⇔ MEM (AsmLabel l) p) ∧
  (MEM (AsmDataHeader l) (MAP (rename_push_label x y) p) ⇔
   MEM (AsmDataHeader l) p) ∧
  (MEM (AsmDataLabel l) (MAP (rename_push_label x y) p) ⇔
   MEM (AsmDataLabel l) p)
Proof
  simp[MEM_MAP, rename_push_label_facts]
QED

Theorem index_of_label_rename:
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

Theorem rename_static_wf:
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

Theorem sv_rel_refl[simp]:
  sv_rel x y v v
Proof
  simp[sv_rel_def]
QED

Theorem sv_rel_val:
  (sv_rel x y (Val w) v' ⇔ v' = Val w) ∧
  (sv_rel x y v (Val w) ⇔ v = Val w)
Proof
  Cases_on `v` >> rw[sv_rel_def] >> metis_tac[]
QED

Theorem list_rel_sv_refl[simp]:
  LIST_REL (sv_rel x y) l l
Proof
  simp[LIST_REL_EL_EQN]
QED

(* ===== The memory label map ===== *)

Theorem ml_rel_fdom:
  ml_rel x y m m' ⇒ FDOM m' = FDOM m
Proof
  rw[ml_rel_def, pred_setTheory.EXTENSION, FLOOKUP_DEF] >>
  first_x_assum (qspec_then `x'` mp_tac) >> rw[] >> gvs[]
QED

Theorem ml_rel_clear:
  ml_rel x y m m' ⇒
  ml_rel x y (mem_labels_clear m P) (mem_labels_clear m' P)
Proof
  rw[ml_rel_def, mem_labels_clear_def, FLOOKUP_DRESTRICT] >> rw[]
QED

Theorem blocks_clear:
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
  simp[mem_blocks_ok_def, mstore_labels_lookup] >> strip_tac >>
  `∀k l d j. FLOOKUP m k = SOME (l, d, j) ⇒ j < 32` by metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `a ≤ k1 ∧ k1 < a + 32` >> Cases_on `a ≤ k2 ∧ k2 < a + 32` >|
  [qpat_x_assum `∀k1 k2 l1 d1 j1 l2 d2 j2. _` kall_tac >> gvs[],
   qpat_x_assum `∀k1 k2 l1 d1 j1 l2 d2 j2. _` kall_tac >> gvs[] >>
   rpt strip_tac >> res_tac >> gvs[],
   qpat_x_assum `∀k1 k2 l1 d1 j1 l2 d2 j2. _` kall_tac >> gvs[] >>
   rpt strip_tac >> res_tac >> gvs[],
   qpat_x_assum `∀k1 k2 l1 d1 j1 l2 d2 j2. _` irule >> gvs[]]
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

Theorem set_stack_rel:
  rn_rel x y ss ss' ∧ LIST_REL (sv_rel x y) stk stk' ⇒
  res_rel x y (sym_set_stack stk ss) (sym_set_stack stk' ss')
Proof
  rw[sym_set_stack_def, res_rel_def, rn_rel_def, asm_next_def]
QED

Theorem push_lab_rel:
  rn_rel x y ss ss' ∧ LIST_REL (sv_rel x y) stk stk' ⇒
  res_rel x y (sym_push_lab l d stk ss) (sym_push_lab l d stk' ss')
Proof
  rw[sym_push_lab_def, res_rel_def] >> irule set_stack_rel >> simp[]
QED

Theorem lift_rel:
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

Theorem concrete_rel:
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

Theorem add_rel:
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

Theorem mstore_rel:
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

Theorem mload_rel:
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

Theorem dup_swap_rel:
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
      gvs[res_rel_def] >> irule set_stack_rel >> simp[]) >>
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

Theorem sym_jump_dest_rename:
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

Theorem sym_step_label_skip:
  ss.sym_base.as_stack = [] ⇒
  sym_step p env (AsmLabel l) ss =
  SymOK (ss with sym_base := ss.sym_base with
                   as_pc := ss.sym_base.as_pc + 1)
Proof
  rw[sym_step_def, asm_step_def, sym_lift_def, asm_next_def] >>
  simp[sym_state_component_equality, asmSemTheory.asm_state_component_equality]
QED

Theorem rename_adjacent_label_steps:
  p = pre ++ AsmLabel x :: AsmLabel y :: sfx ∧
  asm_labels_unique p ∧ y ≠ x ∧
  t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ⇒
  INDEX_OF (AsmLabel y) p = SOME (LENGTH pre + 1) ∧
  ∀n. sym_steps p env (SUC n) t =
    sym_steps p env n
      (t with sym_base := t.sym_base with as_pc := LENGTH pre + 1)
Proof
  strip_tac >> qpat_x_assum `p = _` SUBST_ALL_TAC >>
  `¬MEM (AsmLabel y) pre`
    by (irule asm_labels_unique_append_not_mem >>
        qexists_tac `AsmLabel x :: AsmLabel y :: sfx` >> fs[]) >>
  simp[INDEX_OF_APPEND, INDEX_OF_CONS, sym_steps_def,
       EL_APPEND_EQN, sym_step_label_skip]
QED

Theorem rename_jump_steps:
  p = pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more ∧
  t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ⇒
  (∀n. sym_steps p env (SUC (SUC (SUC n))) t =
    case INDEX_OF (AsmLabel y) p of
      NONE => SymBad "jump target"
    | SOME j => sym_steps p env n
        (t with sym_base := t.sym_base with as_pc := j)) ∧
  (∀Q. (∀i. asm_plain_inst i ⇒ ¬Q i) ⇒
    sym_steps_ok (λi stk. T) Q p env 3 t)
Proof
  strip_tac >>
  qabbrev_tac `t1 = t with sym_base := t.sym_base with
                      as_pc := LENGTH pre + 1` >>
  qabbrev_tac `t2 = t1 with <| sym_base := asm_next t1.sym_base;
                               sym_stack := Lab y 0 :: t.sym_stack |>` >>
  `LENGTH pre < LENGTH p ∧ EL (LENGTH pre) p = AsmLabel x ∧
   LENGTH pre + 1 < LENGTH p ∧ EL (LENGTH pre + 1) p = AsmPushLabel y ∧
   LENGTH pre + 2 < LENGTH p ∧ EL (LENGTH pre + 2) p = AsmOp "JUMP"`
    by (qpat_x_assum `p = _` SUBST1_TAC >> simp[EL_APPEND_EQN]) >>
  `sym_step p env (AsmLabel x) t = SymOK t1`
    by simp[Abbr `t1`, sym_step_label_skip] >>
  `sym_step p env (AsmPushLabel y) t1 = SymOK t2`
    by (simp[Abbr `t2`, sym_step_push_label] >> simp[Abbr `t1`]) >>
  `t1.sym_base.as_pc = LENGTH pre + 1 ∧ t2.sym_base.as_pc = LENGTH pre + 2 ∧
   t2.sym_stack = Lab y 0 :: t.sym_stack`
    by simp[Abbr `t1`, Abbr `t2`, asm_next_def] >>
  qpat_x_assum `p = _` kall_tac >>
  conj_tac
  >- (gen_tac >> simp[sym_steps_def] >>
      simp[sym_step_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def] >>
      Cases_on `INDEX_OF (AsmLabel y) p` >>
      simp[Abbr `t2`, Abbr `t1`, asm_next_def,
           sym_state_component_equality,
           asmSemTheory.asm_state_component_equality]) >>
  rpt strip_tac >>
  simp[sym_steps_ok_pos, sym_steps_ok_def, asm_plain_inst_def, is_data_inst_def] >>
  Cases_on `sym_step p env (AsmOp "JUMP") t2` >> simp[]
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
  >- (mp_tac (Q.INST [`p` |-> `pre ++ AsmLabel x :: AsmLabel y :: sfx`]
        rename_adjacent_label_steps) >>
      simp[] >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD1]))) >>
      drule_then (qspec_then `1` mp_tac) sym_run_terminal_steps >>
      fs[sym_steps_def] >> strip_tac >> qexists_tac `fuel - 1` >> simp[]) >>
  qpat_x_assum `sfx = _` SUBST_ALL_TAC >>
  qabbrev_tac `p = pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more` >>
  mp_tac (Q.INST [`p` |-> `p`] rename_jump_steps) >>
  (impl_tac >- simp[Abbr `p`]) >>
  disch_then (CONJUNCTS_THEN2 (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD1])) (K all_tac)) >>
  Cases_on `INDEX_OF (AsmLabel y) p` >>
  drule_then (qspec_then `3` mp_tac) sym_run_terminal_steps >>
  fs[sym_steps_def] >> strip_tac
  >- gvs[sym_terminal_def] >>
  qexists_tac `fuel - 3` >> simp[]
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
  qpat_x_assum `∀f. _` (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD1])) >>
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



Theorem sv_rel_list_vals:
  !l l'. LIST_REL (sv_rel x y) l l' ==> MAP sval_val l' = MAP sval_val l
Proof
  Induct >> simp[LIST_REL_CONS1, PULL_EXISTS] >> rpt strip_tac >> res_tac >>
  gvs[sv_rel_def, sval_val_def]
QED

Theorem within_ok_rename[local]:
  sym_within_ok R Q ∧ LIST_REL (sv_rel x y) stk stk' ⇒
  (Q (rename_push_label x y i) ⇔ Q i) ∧
  (R (rename_push_label x y i) stk' ⇔ R i stk)
Proof
  strip_tac >> drule sv_rel_list_vals >> strip_tac >>
  Cases_on `i = AsmPushLabel x`
  >- (`asm_plain_inst (AsmPushLabel x) ∧ asm_plain_inst (AsmPushLabel y)`
        by simp[asm_plain_inst_def, is_data_inst_def] >>
      gvs[rename_push_label_def, sym_within_ok_def]) >>
  simp[rename_push_label_other] >> gvs[sym_within_ok_def] >> metis_tac[]
QED

Theorem within_skip[local]:
  p = pre ++ AsmLabel x :: next :: sfx ∧ asm_labels_unique p ∧
  (next = AsmLabel y ∧ y ≠ x ∨
   next = AsmPushLabel y ∧ ∃more. sfx = AsmOp "JUMP" :: more) ∧
  t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ∧
  sym_within_ok R Q ∧ sym_run_within R Q p env k t ⇒
  ∃j k2. INDEX_OF (AsmLabel y) p = SOME j ∧ k2 < k ∧
    sym_run_within R Q p env k2
      (t with sym_base := t.sym_base with as_pc := j)
Proof
  strip_tac >>
  `0 < k` by (Cases_on `k` >> gvs[sym_run_within_def]) >>
  `∀i. asm_plain_inst i ⇒ ¬Q i` by fs[sym_within_ok_def] >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `next = _` SUBST_ALL_TAC
  >- (mp_tac (Q.INST [`p` |-> `pre ++ AsmLabel x :: AsmLabel y :: sfx`]
        rename_adjacent_label_steps) >>
      simp[] >>
      disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD1]))) >>
      fs[sym_steps_def] >>
      `sym_steps_ok (λi stk. T) Q (pre ++ AsmLabel x :: AsmLabel y :: sfx)
         env 1 t`
        by simp[sym_steps_ok_one, EL_APPEND_EQN, asm_plain_inst_def,
                is_data_inst_def] >>
      drule_all sym_run_within_steps >> strip_tac >>
      qexists_tac `k - 1` >> simp[]) >>
  qpat_x_assum `sfx = _` SUBST_ALL_TAC >>
  qabbrev_tac `p = pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more` >>
  mp_tac (Q.INST [`p` |-> `p`] rename_jump_steps) >>
  (impl_tac >- simp[Abbr `p`]) >>
  disch_then (CONJUNCTS_THEN2 (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD1])) (qspec_then `Q` mp_tac)) >>
  simp[] >> strip_tac >>
  Cases_on `INDEX_OF (AsmLabel y) p` >> fs[sym_steps_def]
  >- (drule_all sym_run_within_steps_error >> simp[]) >>
  drule_all sym_run_within_steps >> strip_tac >>
  qexists_tac `k - 3` >> simp[]
QED

(* Redirects pass only labels, a label push and a jump. The bounded runs
   can skip them using the same short prefix equations in either mode. *)
Theorem within_skip_for:
  p = pre ++ AsmLabel x :: next :: sfx ∧ asm_labels_unique p ∧
  (next = AsmLabel y ∧ y ≠ x ∨
   next = AsmPushLabel y ∧ ∃more. sfx = AsmOp "JUMP" :: more) ∧
  t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ∧
  sym_prefix_driver stepf runf p ∧
  (∀n. n ≤ (if next = AsmLabel y then 1 else 3) ⇒
       runf n t = sym_steps p env n t) ∧
  sym_within_ok R Q ∧ sym_run_within_for stepf R Q p k t ⇒
  ∃j k2. INDEX_OF (AsmLabel y) p = SOME j ∧ k2 < k ∧
    sym_run_within_for stepf R Q p k2
      (t with sym_base := t.sym_base with as_pc := j)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `∀i. asm_plain_inst i ⇒ ¬Q i` by fs[sym_within_ok_def] >>
  `0 < k` by (Cases_on `k` >> gvs[sym_run_within_for_def]) >>
  qpat_x_assum `next = _ ∧ _ ∨ _` strip_assume_tac
  >- suspend "adjacent" >> suspend "jump"
QED

Resume within_skip_for[adjacent]:
  qpat_x_assum `next = AsmLabel y` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`p` |-> `p`] rename_adjacent_label_steps) >>
  (impl_tac >- simp[]) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (assume_tac o PURE_REWRITE_RULE [GSYM arithmeticTheory.ONE] o
     CONV_RULE (RAND_CONV (REWRITE_CONV [sym_steps_def])) o Q.SPEC `0`)) >>
  `runf 1 t = SymOK (t with sym_base := t.sym_base with as_pc := LENGTH pre + 1)` by
    (qpat_assum `!n. _ ==> runf n t = sym_steps p env n t`
       (qspec_then `1` mp_tac) >> simp[]) >>
  `sym_prefix_all runf (λi stk. T) Q p 1 t` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >> `m = 0` by decide_tac >>
     gvs[sym_steps_def, EL_APPEND_EQN, asm_plain_inst_def, is_data_inst_def]) >>
  mp_tac (Q.INST [`P` |-> `R`, `Q` |-> `Q`, `p` |-> `p`]
      (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_split_within)) >>
  (impl_tac >- fs[]) >>
  disch_then (qspecl_then [`1`, `t`,
    `t with sym_base := t.sym_base with as_pc := LENGTH pre + 1`, `k`] mp_tac) >>
  (impl_tac >- fs[EL_APPEND_EQN, asm_plain_inst_def, is_data_inst_def]) >> strip_tac >>
  qexistsl_tac [`LENGTH pre + 1`, `k - 1`] >> simp[]
QED

Resume within_skip_for[jump]:
  qpat_x_assum `next = AsmPushLabel y` SUBST_ALL_TAC >>
  qpat_x_assum `sfx = _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`p` |-> `p`] rename_jump_steps) >>
  (impl_tac >- simp[]) >>
  disch_then (CONJUNCTS_THEN2
    (assume_tac o SIMP_RULE (srw_ss()) [arithmeticTheory.ADD1] o
     CONV_RULE (RAND_CONV (REWRITE_CONV [sym_steps_def])) o Q.SPEC `0`)
    (qspec_then `Q` mp_tac)) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `!n. n <= 3 ==> runf n t = sym_steps p env n t` by fs[] >>
  `sym_prefix_all runf (λi stk. T) Q p 3 t` by
    (mp_tac (Q.INST [`runf'` |-> `sym_steps p env`, `n` |-> `3`, `ss` |-> `t`,
       `P` |-> `λi stk. T`, `Q` |-> `Q`, `p` |-> `p`]
       (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_cong)) >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac)) >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
     rewrite_tac[GSYM sym_steps_ok_as_prefix_all] >> first_assum ACCEPT_TAC) >>
  `runf 3 t = case INDEX_OF (AsmLabel y) p of
       NONE => SymBad "jump target"
     | SOME j => SymOK (t with sym_base := t.sym_base with as_pc := j)` by
    metis_tac[DECIDE ``3 <= (3:num)``] >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  Cases_on `INDEX_OF (AsmLabel y) (pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more)` >> fs[]
  >- (mp_tac (Q.INST [`P` |-> `R`, `Q` |-> `Q`, `p` |-> `pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more`]
       (INST_TYPE [alpha |-> ``:asm_inst``] sym_run_within_for_no_error)) >>
      (impl_tac >- fs[]) >>
      disch_then (qspecl_then [`3`, `t`, `k`] mp_tac) >> simp[] >>
      first_assum ACCEPT_TAC) >>
  rename1 `INDEX_OF _ _ = SOME j` >>
  mp_tac (Q.INST [`P` |-> `R`, `Q` |-> `Q`, `p` |-> `pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more`]
      (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_split_within)) >>
  (impl_tac >- fs[]) >>
  disch_then (qspecl_then [`3`, `t`,
    `t with sym_base := t.sym_base with as_pc := j`, `k`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `k - 3` >> simp[]
QED

Finalise within_skip_for

(* The label walk shares its bound argument between the ordinary and
   fixed-code steps. The step relation supplies only its rename cases. *)
Theorem rename_run_within_for:
  ∀p i x y env R Q source_step target_step.
  asm_static_wf p ∧ INDEX_OF (AsmLabel x) p = SOME i ∧ sym_within_ok R Q ∧
  (∀ss inst t. ss.sym_base.as_stack = [] ∧ source_step inst ss = SymOK t ⇒
               t.sym_base.as_stack = []) ∧
  (∀ss ss' inst. rn_rel x y ss ss' ∧ ¬sym_data_label p env x ⇒
    case source_step inst ss of
      SymOK t =>
        (∃t'. target_step (rename_push_label x y inst) ss' = SymOK t' ∧
              rn_rel x y t t') ∨
        (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc ∧
         ∀j. INDEX_OF (AsmLabel y) p = SOME j ⇒
           ∃t'. target_step (rename_push_label x y inst) ss' = SymOK t' ∧
                rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t')
    | r => res_rel x y r (target_step (rename_push_label x y inst) ss')) ∧
  (∀t k. t.sym_base.as_pc = i ∧ t.sym_base.as_stack = [] ∧
         sym_run_within_for source_step R Q p k t ⇒
         ∃j k2. INDEX_OF (AsmLabel y) p = SOME j ∧ k2 < k ∧
           sym_run_within_for source_step R Q p k2
             (t with sym_base := t.sym_base with as_pc := j)) ⇒
  ∀k ss ss'.
    rn_rel x y ss ss' ∧ sym_run_within_for source_step R Q p k ss ⇒
    sym_run_within_for target_step R Q (MAP (rename_push_label x y) p) k ss'
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (AsmLabel x) p`
    by metis_tac[INDEX_OF_eq_NONE, optionTheory.NOT_SOME_NONE] >>
  `¬sym_data_label p env x`
    by (fs[asm_static_wf_def, sym_data_label_def] >> metis_tac[]) >>
  completeInduct_on `k` >> rpt strip_tac >>
  `ss'.sym_base = ss.sym_base ∧
   LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss.sym_base.as_stack = []` by fs[rn_rel_def] >>
  Cases_on `k` >- gvs[sym_run_within_for_def] >>
  rename1 `SUC k0` >>
  qpat_x_assum `sym_run_within_for _ _ _ _ (SUC _) _` mp_tac >>
  simp[sym_run_within_for_def] >> strip_tac >>
  drule_all within_ok_rename >>
  disch_then (qspec_then `EL ss.sym_base.as_pc p` strip_assume_tac) >>
  simp[EL_MAP] >>
  Cases_on `Q (EL ss.sym_base.as_pc p)` >> gvs[] >>
  qpat_x_assum `!ss ss' inst. rn_rel x y ss ss' ⇒ _`
    (qspecl_then [`ss`, `ss'`, `EL ss.sym_base.as_pc p`] mp_tac) >>
  simp[] >>
  Cases_on `source_step (EL ss.sym_base.as_pc p) ss` >>
  gvs[res_rel_def] >> strip_tac >> gvs[] >>
  rename1 `source_step _ ss = SymOK t` >>
  `t.sym_base.as_stack = []` by metis_tac[]
  >- (qpat_x_assum `!m. m < SUC k0 ==> _` (qspec_then `k0` mp_tac) >> simp[] >>
      disch_then irule >> qexists_tac `t` >> simp[]) >>
  qpat_x_assum `!t k. _ ==> ?j k2. _` (qspecl_then [`t`, `k0`] mp_tac) >> simp[] >>
  strip_tac >>
  qpat_x_assum `∀j. _ ⇒ ∃t'. _` drule >> strip_tac >> simp[] >>
  irule sym_run_within_for_mono >> qexists_tac `k2` >> simp[] >>
  qpat_x_assum `!m. m < SUC k0 ==> _` (qspec_then `k2` mp_tac) >> simp[] >>
  disch_then irule >>
  qexists_tac `t with sym_base := t.sym_base with as_pc := j` >> simp[]
QED

Theorem rename_run_within[local]:
  ∀p i x y env R Q.
  asm_static_wf p ∧ INDEX_OF (AsmLabel x) p = SOME i ∧ sym_within_ok R Q ∧
  (∀t k. t.sym_base.as_pc = i ∧ t.sym_base.as_stack = [] ∧
         sym_run_within R Q p env k t ⇒
         ∃j k2. INDEX_OF (AsmLabel y) p = SOME j ∧ k2 < k ∧
           sym_run_within R Q p env k2
             (t with sym_base := t.sym_base with as_pc := j)) ⇒
  ∀k ss ss'.
    rn_rel x y ss ss' ∧ sym_run_within R Q p env k ss ⇒
    sym_run_within R Q (MAP (rename_push_label x y) p) env k ss'
Proof
  rewrite_tac[sym_run_within_for_sym_step] >>
  rpt gen_tac >> strip_tac >>
  qspecl_then [`p`, `i`, `x`, `y`, `env`, `R`, `Q`, `sym_step p env`,
    `sym_step (MAP (rename_push_label x y) p) env`] mp_tac rename_run_within_for >>
  (impl_tac >-
    (simp[] >> conj_tac >- metis_tac[sym_step_base_stack] >>
     rpt gen_tac >>
     mp_tac (Q.INST [`ss` |-> `ss`, `ss'` |-> `ss'`, `inst` |-> `inst`] rename_step) >>
     simp[])) >> simp[]
QED

Theorem rename_refines_both[local]:
  (next = AsmLabel y ∧ y ≠ x ∨ next = AsmPushLabel y ∧ third = AsmOp "JUMP") ⇒
  asm_refines_both (pre ++ AsmLabel x :: next :: third :: more)
    (MAP (rename_push_label x y) (pre ++ AsmLabel x :: next :: third :: more))
Proof
  disch_tac >> PURE_REWRITE_TAC[relationTheory.RINTER] >>
  conj_tac >- (irule rename_refines >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `P = pre ++ AsmLabel x :: next :: third :: more` >>
  simp[asm_refines_within_def] >> strip_tac >>
  `asm_labels_unique P` by fs[asm_static_wf_def] >>
  `INDEX_OF (AsmLabel x) P = SOME (LENGTH pre)`
    by (`¬MEM (AsmLabel x) pre`
          by (irule asm_labels_unique_append_not_mem >>
              qexists_tac `AsmLabel x :: next :: third :: more` >>
              fs[Abbr `P`]) >>
        simp[Abbr `P`, INDEX_OF_APPEND, INDEX_OF_CONS]) >>
  qexists_tac `1` >> qx_genl_tac [`R`, `Q`, `env`, `s`, `k`] >>
  strip_tac >> simp[] >>
  `∀t k1. t.sym_base.as_pc = LENGTH pre ∧ t.sym_base.as_stack = [] ∧
          sym_run_within R Q P env k1 t ⇒
          ∃j k2. INDEX_OF (AsmLabel y) P = SOME j ∧ k2 < k1 ∧
            sym_run_within R Q P env k2
              (t with sym_base := t.sym_base with as_pc := j)`
    by (rpt strip_tac >>
        mp_tac (Q.INST [`p` |-> `P`, `sfx` |-> `third :: more`,
                        `k` |-> `k1`] within_skip) >>
        fs[Abbr `P`]) >>
  qspecl_then [`P`, `LENGTH pre`, `x`, `y`, `env`, `R`, `Q`] mp_tac
    rename_run_within >>
  impl_tac >- simp[] >>
  disch_then irule >> qexists_tac `sym_init s` >> simp[] >>
  simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def,
       listTheory.LIST_REL_EL_EQN, sv_rel_def]
QED

Theorem merge_jumpdests_walk_refines_both[local]:
  ∀n done rest changed.
    LENGTH rest = n ⇒
    asm_refines_both (REVERSE done ++ rest)
      (FST (merge_jumpdests_walk done rest changed))
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `∀d r c. LENGTH r < LENGTH rest ⇒
           asm_refines_both (REVERSE d ++ r) (FST (merge_jumpdests_walk d r c))`
    by metis_tac[] >>
  qpat_x_assum `∀m. m < n ⇒ _` kall_tac >>
  Cases_on `rest`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_both_refl] >>
  rename1 `h :: t` >> Cases_on `t`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_both_refl] >>
  rename1 `h :: next :: t` >> Cases_on `t`
  >- simp[Once merge_jumpdests_walk_def, asm_refines_both_refl] >>
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
      irule asm_refines_both_trans >>
      qexists_tac `MAP (rename_push_label x y)
                     (REVERSE done ++ AsmLabel x :: next :: third :: more)` >>
      conj_tac
      >- (irule rename_refines_both >> metis_tac[]) >>
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

Theorem merge_jumpdests_walk_refines[local]:
  ∀n done rest changed.
    LENGTH rest = n ⇒
    asm_refines (REVERSE done ++ rest)
      (FST (merge_jumpdests_walk done rest changed))
Proof
  metis_tac[merge_jumpdests_walk_refines_both, relationTheory.RINTER]
QED

Theorem merge_jumpdests_refines:
  ∀p. asm_refines p (FST (merge_jumpdests p))
Proof
  simp[merge_jumpdests_def] >> rpt gen_tac >>
  qspecl_then [`LENGTH p`, `[]`, `p`, `F`] mp_tac merge_jumpdests_walk_refines >>
  simp[]
QED

Theorem merge_jumpdests_refines_both:
  ∀p. asm_refines_both p (FST (merge_jumpdests p))
Proof
  simp[merge_jumpdests_def] >> rpt gen_tac >>
  qspecl_then [`LENGTH p`, `[]`, `p`, `F`] mp_tac merge_jumpdests_walk_refines_both >>
  simp[]
QED

(* A successful prefix either stops inside the redirect, or has reached
   the destination with at most three additional source instructions. *)
Theorem rename_prefix_skip[local]:
  !pre x y next third more env t n a.
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_labels_unique (pre ++ AsmLabel x::next::third::more) /\
    t.sym_base.as_pc = LENGTH pre /\ t.sym_base.as_stack = [] /\
    sym_steps (pre ++ AsmLabel x::next::third::more) env n t = SymOK a ==>
    (n <= 2 /\ a.sym_base.as_pc < LENGTH (pre ++ AsmLabel x::next::third::more) /\
      !op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} ==>
        EL a.sym_base.as_pc (pre ++ AsmLabel x::next::third::more) <> AsmOp op) \/
    (?k j. 0 < k /\ k <= 3 /\ k <= n /\
      INDEX_OF (AsmLabel y) (pre ++ AsmLabel x::next::third::more) = SOME j /\
      sym_steps (pre ++ AsmLabel x::next::third::more) env (n-k)
        (t with sym_base := t.sym_base with as_pc := j) = SymOK a)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 mp_tac strip_assume_tac) >> disch_tac >>
  Cases_on `n` >- gvs[sym_steps_def, EL_APPEND_EQN] >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (gvs[] >>
      mp_tac (Q.INST [`p` |-> `pre ++ AsmLabel x :: AsmLabel y :: third :: more`,
                      `sfx` |-> `third :: more`] rename_adjacent_label_steps) >>
      simp[] >> strip_tac >>
      disj2_tac >> qexists_tac `1` >> gvs[]) >>
  gvs[] >> Cases_on `n'`
  >- (disj1_tac >>
      gvs[sym_steps_def, EL_APPEND_EQN, sym_step_label_skip]) >>
  Cases_on `n`
  >- (disj1_tac >>
      gvs[sym_steps_def, EL_APPEND_EQN, sym_step_label_skip,
          sym_step_push_label, asm_next_def]) >>
  mp_tac (Q.INST [`p` |-> `pre ++ AsmLabel x :: AsmPushLabel y :: AsmOp "JUMP" :: more`]
    rename_jump_steps) >>
  simp[] >> strip_tac >>
  qpat_x_assum `sym_steps _ _ _ _ = _` mp_tac >>
  simp[] >> Cases_on `INDEX_OF (AsmLabel y)
    (pre ++ AsmLabel x::AsmPushLabel y::AsmOp "JUMP"::more)` >> simp[] >>
  strip_tac >> qexists_tac `3` >> simp[arithmeticTheory.ADD1]
QED

Theorem rename_prefix_one_step[local]:
  !p x y env n ss ss' a.
    asm_static_wf p /\ MEM (AsmLabel x) p /\ 0 < n /\
    rn_rel x y ss ss' /\ sym_steps p env n ss = SymOK a ==>
      ?t. t.sym_base.as_stack = [] /\ sym_steps p env (n-1) t = SymOK a /\
        ((?t'. sym_steps (MAP (rename_push_label x y) p) env 1 ss' = SymOK t' /\
             rn_rel x y t t') \/
         (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc /\
          !j. INDEX_OF (AsmLabel y) p = SOME j ==>
            ?t'. sym_steps (MAP (rename_push_label x y) p) env 1 ss' = SymOK t' /\
                 rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t'))
Proof
  rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc < LENGTH p`
    by (spose_not_then assume_tac >>
        qpat_x_assum `sym_steps _ _ _ _ = _` mp_tac >>
        Cases_on `n` >- gvs[] >> simp[Once sym_steps_def]) >>
  `~sym_data_label p env x`
    by metis_tac[asm_static_wf_def, sym_data_label_def] >>
  `ss'.sym_base = ss.sym_base` by metis_tac[rn_rel_def] >>
  qpat_x_assum `sym_steps _ _ _ _ = _` mp_tac >>
  simp[sym_steps_pos] >>
  Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[] >>
  rename1 `sym_step p env _ ss = SymOK t` >> disch_tac >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule sym_step_base_stack >> metis_tac[rn_rel_def]) >>
  mp_tac (Q.INST [`inst` |-> `EL ss.sym_base.as_pc p`] rename_step) >>
  simp[] >> disch_tac >>
  qpat_x_assum `(?t'. _) \/ _` strip_assume_tac
  >- (disj1_tac >> qexists_tac `t'` >> simp[arithmeticTheory.ONE, sym_steps_def, EL_MAP]) >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `t'` >> simp[arithmeticTheory.ONE, sym_steps_def, EL_MAP]
QED

Theorem rename_prefix_boundaries_by_steps:
  !p pre x y next third more (srcSteps:num -> sym_state -> sym_result) dstSteps.
    p = pre ++ AsmLabel x::next::third::more /\
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_static_wf p /\
    (!ss. srcSteps 0 ss = SymOK ss) /\
    (!ss. dstSteps 0 ss = SymOK ss) /\
    (!ss t m b. dstSteps 1 ss = SymOK t /\ dstSteps m t = SymOK b ==>
      dstSteps (SUC m) ss = SymOK b) /\
    (!n ss ss' a. 0 < n /\ rn_rel x y ss ss' /\ srcSteps n ss = SymOK a ==>
      ?t. t.sym_base.as_stack = [] /\ srcSteps (n-1) t = SymOK a /\
        ((?t'. dstSteps 1 ss' = SymOK t' /\ rn_rel x y t t') \/
         (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc /\
          !j. INDEX_OF (AsmLabel y) p = SOME j ==>
            ?t'. dstSteps 1 ss' = SymOK t' /\
                 rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t'))) /\
    (!t n a. t.sym_base.as_pc = LENGTH pre /\ t.sym_base.as_stack = [] /\
      srcSteps n t = SymOK a ==>
      (n <= 2 /\ a.sym_base.as_pc < LENGTH p /\
       !op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} ==>
        EL a.sym_base.as_pc p <> AsmOp op) \/
      (?k j. 0 < k /\ k <= 3 /\ k <= n /\ INDEX_OF (AsmLabel y) p = SOME j /\
        srcSteps (n-k) (t with sym_base := t.sym_base with as_pc := j) = SymOK a)) ==>
    !n ss ss' a.
      rn_rel x y ss ss' /\ srcSteps n ss = SymOK a ==>
      (?m b. dstSteps m ss' = SymOK b /\
        n <= 4 * (m+1)) /\
      (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} /\
         a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
       ?m b. dstSteps m ss' = SymOK b /\
         b.sym_base.as_pc < LENGTH p /\
         EL b.sym_base.as_pc (MAP (rename_push_label x y) p) = AsmOp op /\
         rn_rel x y a b)
Proof
  rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_labels_unique p` by metis_tac[asm_static_wf_def] >>
  `INDEX_OF (AsmLabel x) p = SOME (LENGTH pre)`
    by (`~MEM (AsmLabel x) pre`
          by (irule asm_labels_unique_append_not_mem >>
              qexists_tac `AsmLabel x::next::third::more` >>
              conj_tac >- metis_tac[] >> simp[]) >>
        simp[INDEX_OF_APPEND, INDEX_OF_CONS]) >>
  qpat_x_assum `p = _` (mk_asm "program") >>
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `ss'.sym_base = ss.sym_base` by metis_tac[rn_rel_def] >>
  Cases_on `n = 0`
  >- (qpat_x_assum `n = 0` SUBST_ALL_TAC >>
      qpat_x_assum `srcSteps 0 _ = _` mp_tac >>
      simp[] >> disch_then SUBST_ALL_TAC >> conj_tac
      >- (qexistsl_tac [`0`, `ss'`] >> simp[]) >>
      rpt strip_tac >> qexistsl_tac [`0`, `ss'`] >>
      simp[EL_MAP, rename_push_label_facts]) >>
  qpat_x_assum `!n ss ss' a. 0 < n /\ _ ==> _`
    (qspecl_then [`n`,`ss`,`ss'`,`a`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `( ?t'. _) \/ _` strip_assume_tac
  >- (qpat_x_assum `!m. m < n ==> _` (qspec_then `n-1` mp_tac) >>
      simp[] >> disch_then drule_all >> strip_tac >> conj_tac
      >- (qexistsl_tac [`SUC m`, `b`] >>
          conj_tac >- metis_tac[] >> decide_tac) >>
      gen_tac >> disch_tac >>
      qpat_x_assum `!op. _ ==> ?m b. _` (qspec_then `op` mp_tac) >>
      (impl_tac >- fs[]) >>
      disch_then (qx_choosel_then [`m2`, `b2`] strip_assume_tac) >>
      qexistsl_tac [`SUC m2`, `b2`] >>
      metis_tac[]) >>
  `t.sym_base.as_pc = LENGTH pre` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `!t n a. t.sym_base.as_pc = LENGTH pre /\ _ ==> _`
    (qspecl_then [`t`, `n-1`, `a`] mp_tac) >> simp[] >> strip_tac
  >- (conj_tac
      >- (qexistsl_tac [`0`, `ss'`] >> simp[] >> decide_tac) >>
      metis_tac[]) >>
  qpat_x_assum `!j. _ ==> ?t'. _` drule >> strip_tac >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `n-1-k` mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  conj_tac
  >- (qexistsl_tac [`SUC m`, `b`] >>
      conj_tac >- metis_tac[] >> decide_tac) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!op. _ ==> ?m b. _` (qspec_then `op` mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (qx_choosel_then [`m2`, `b2`] strip_assume_tac) >>
  qexistsl_tac [`SUC m2`, `b2`] >> metis_tac[]
QED

Theorem rename_steps_extend[local]:
  sym_steps p env 1 ss = SymOK t /\ sym_steps p env m t = SymOK b ==>
  sym_steps p env (SUC m) ss = SymOK b
Proof
  Cases_on `ss.sym_base.as_pc < LENGTH p`
  >- (asm_simp_tac (srw_ss()) [sym_steps_pos, sym_steps_def] >>
      Cases_on `sym_step p env (EL ss.sym_base.as_pc p) ss` >> simp[] >>
      metis_tac[]) >>
  rewrite_tac [Once arithmeticTheory.ONE] >>
  rewrite_tac [sym_steps_def] >>
  `ss.sym_base.as_pc >= LENGTH p` by decide_tac >>
  simp[]
QED

Theorem rename_prefix_boundaries[local]:
  !p pre x y next third more env.
    p = pre ++ AsmLabel x::next::third::more /\
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_static_wf p ==>
    !n ss ss' a.
      rn_rel x y ss ss' /\ sym_steps p env n ss = SymOK a ==>
      (?m b. sym_steps (MAP (rename_push_label x y) p) env m ss' = SymOK b /\
        n <= 4 * (m+1)) /\
      (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} /\
         a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
       ?m b. sym_steps (MAP (rename_push_label x y) p) env m ss' = SymOK b /\
         b.sym_base.as_pc < LENGTH p /\
         EL b.sym_base.as_pc (MAP (rename_push_label x y) p) = AsmOp op /\
         rn_rel x y a b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`p`, `pre`, `x`, `y`, `next`, `third`, `more`,
    `sym_steps p env`, `sym_steps (MAP (rename_push_label x y) p) env`]
    rename_prefix_boundaries_by_steps) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp_tac bool_ss [sym_steps_def] >> NO_TAC)
    >- (rpt gen_tac >> MATCH_ACCEPT_TAC rename_steps_extend)
    >- (rpt gen_tac >> strip_tac >> irule rename_prefix_one_step >>
        simp[] >> metis_tac[MEM_APPEND, MEM]) >>
    qpat_x_assum `p = _` SUBST_ALL_TAC >>
    rpt gen_tac >> strip_tac >>
    `asm_labels_unique (pre ++ AsmLabel x::next::third::more)`
      by metis_tac[asm_static_wf_def] >>
    mp_tac (Q.SPECL [`pre`,`x`,`y`,`next`,`third`,`more`,`env`,`t`,`n`,`a`]
      rename_prefix_skip) >> simp[])) >>
  simp[]
QED

Theorem rename_site_prefix_transport:
  !pre x y next third more.
    (next = AsmLabel y /\ y <> x \/
     next = AsmPushLabel y /\ third = AsmOp "JUMP") /\
    asm_static_wf (pre ++ AsmLabel x::next::third::more) ==>
    ?K. 0 < K /\ !env s n a.
      s.as_pc = 0 /\
      sym_steps (pre ++ AsmLabel x::next::third::more) env n (sym_init s) = SymOK a ==>
      (?m b. sym_steps (MAP (rename_push_label x y)
        (pre ++ AsmLabel x::next::third::more)) env m (sym_init s) = SymOK b /\
        n <= K * (m+1)) /\
      (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} /\
         a.sym_base.as_pc < LENGTH (pre ++ AsmLabel x::next::third::more) /\
         EL a.sym_base.as_pc (pre ++ AsmLabel x::next::third::more) = AsmOp op ==>
       ?m b. sym_steps (MAP (rename_push_label x y)
         (pre ++ AsmLabel x::next::third::more)) env m (sym_init s) = SymOK b /\
         b.sym_base.as_pc < LENGTH (MAP (rename_push_label x y)
           (pre ++ AsmLabel x::next::third::more)) /\
         EL b.sym_base.as_pc (MAP (rename_push_label x y)
           (pre ++ AsmLabel x::next::third::more)) = AsmOp op /\
         (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
         MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
         FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)
Proof
  rpt gen_tac >> disch_tac >> qexists_tac `4` >>
  conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[LENGTH_MAP] >>
  qspecl_then [`pre ++ AsmLabel x::next::third::more`, `pre`, `x`, `y`, `next`,
    `third`, `more`, `env`] mp_tac rename_prefix_boundaries >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspecl_then [`n`, `sym_init s`, `sym_init s`, `a`] mp_tac) >>
  (impl_tac >- simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def]) >>
  strip_tac >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> first_x_assum drule_all >>
  disch_then (qx_choosel_then [`m2`, `b2`] strip_assume_tac) >>
  qexistsl_tac [`m2`, `b2`] >> fs[rn_rel_def] >>
  metis_tac[sv_rel_list_vals, ml_rel_fdom]
QED

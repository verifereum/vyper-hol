(*
 * Function Inliner — Label Freshness Infrastructure
 *
 * Proves that inline_one_site preserves ALL_DISTINCT (fn_labels fn)
 * under a freshness condition on labels.
 *
 * Key results:
 *   inline_prefix_prefix_free    — different counters produce non-conflicting prefixes
 *   inline_call_site_fn_labels   — fn_labels structure after inline_call_site
 *   inline_one_site_all_distinct — ALL_DISTINCT preserved by inline_one_site
 *)

Theory functionInlinerFresh
Ancestors
  functionInlinerDefs functionInlinerRenumber venomInst cfgTransform

open stringTheory ASCIInumbersTheory rich_listTheory listTheory pred_setTheory
     pairTheory BasicProvers

(* ===== Core prefix-free property ===== *)

(* inline_prefix m cannot be a prefix of inline_prefix n ++ l when m ≠ n.
   Proof uses EL at the boundary between digit-string and underscore:
   at position min(|digits(m)|, |digits(n)|), one side has underscore
   and the other has a digit — contradiction. *)
Theorem inline_prefix_prefix_free:
  !m n l. isPREFIX (inline_prefix m) (STRCAT (inline_prefix n) l) ==>
          m = n
Proof
  rpt strip_tac >>
  gvs[inline_prefix_def, isPREFIX_STRCAT] >>
  rename1 `STRCAT _ l0 = STRCAT _ s3` >>
  (* Hypothesis (after isPREFIX_STRCAT expansion):
     STRCAT (STRCAT "inl" (STRCAT (toString n) "_")) l0 =
     STRCAT (STRCAT "inl" (STRCAT (toString m) "_")) s3
     Cancel common "inl" prefix, then use digit/underscore argument *)
  qabbrev_tac `sm = toString m` >>
  qabbrev_tac `sn = toString n` >>
  `STRCAT sn (STRCAT "_" l0) = STRCAT sm (STRCAT "_" s3)` by
    (qpat_x_assum `STRCAT _ _ = STRCAT _ _` mp_tac >>
     simp_tac (srw_ss()) [STRCAT_ASSOC, STRCAT_11]) >>
  Cases_on `STRLEN sm = STRLEN sn`
  >- (
    `sn = sm /\ STRCAT "_" l0 = STRCAT "_" s3` by
      (irule (iffLR (cj 1 listTheory.APPEND_11_LENGTH)) >>
       simp[]) >>
    gvs[Abbr `sm`, Abbr `sn`, toString_inj]
  )
  >> Cases_on `STRLEN sm < STRLEN sn`
  >- (
    `EL (STRLEN sm) (STRCAT sm (STRCAT "_" s3)) = #"_"` by
      (PURE_REWRITE_TAC [STRCAT_EQNS, EL_LENGTH_APPEND_0] >> simp[]) >>
    `EL (STRLEN sm) (STRCAT sn (STRCAT "_" l0)) =
     EL (STRLEN sm) sn` by
      (irule EL_APPEND1 >> simp[]) >>
    `isDigit (EL (STRLEN sm) sn)` by
      (qunabbrev_tac `sn` >>
       irule (iffLR listTheory.EVERY_EL) >> simp[EVERY_isDigit_num_to_dec_string]) >>
    metis_tac[EVAL ``isDigit #"_"``]
  )
  >> (
    `STRLEN sn < STRLEN sm` by simp[] >>
    `EL (STRLEN sn) (STRCAT sn (STRCAT "_" l0)) = #"_"` by
      (PURE_REWRITE_TAC [STRCAT_EQNS, EL_LENGTH_APPEND_0] >> simp[]) >>
    `EL (STRLEN sn) (STRCAT sm (STRCAT "_" s3)) =
     EL (STRLEN sn) sm` by
      (irule EL_APPEND1 >> simp[]) >>
    `isDigit (EL (STRLEN sn) sm)` by
      (qunabbrev_tac `sm` >>
       irule (iffLR listTheory.EVERY_EL) >> simp[EVERY_isDigit_num_to_dec_string]) >>
    metis_tac[EVAL ``isDigit #"_"``]
  )
QED

Theorem inline_prefix_inj:
  !m n. inline_prefix m = inline_prefix n <=> m = n
Proof
  rw[EQ_IMP_THM] >>
  `isPREFIX (inline_prefix m) (STRCAT (inline_prefix n) "")` by
    simp[isPREFIX_STRCAT] >>
  metis_tac[inline_prefix_prefix_free]
QED

Theorem prefixed_label_fresh:
  !n lbl k. k <> n ==>
    ~isPREFIX (inline_prefix k) (STRCAT (inline_prefix n) lbl)
Proof
  metis_tac[inline_prefix_prefix_free]
QED

(* ===== Block label helpers ===== *)

Triviality lookup_block_label_fresh:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >>
  rw[lookup_block_def, listTheory.FIND_thm] >>
  Cases_on `h.bb_label = lbl` >> gvs[]
QED

Theorem find_invoke_site_label_mem:
  !callee_name bbs lbl idx.
    find_invoke_site callee_name bbs = SOME (lbl, idx) ==>
    MEM lbl (MAP (\b. b.bb_label) bbs)
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >>
  simp[] >> metis_tac[]
QED

Triviality find_invoke_site_lookup:
  !callee_name bbs lbl idx.
    find_invoke_site callee_name bbs = SOME (lbl, idx) /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    ?bb. lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >> simp[]
  >| [
    strip_tac >> gvs[] >>
    first_x_assum drule >> strip_tac >>
    qexists_tac `bb` >>
    simp[lookup_block_def, listTheory.FIND_thm] >>
    drule lookup_block_label_fresh >>
    drule find_invoke_site_label_mem >> strip_tac >>
    strip_tac >>
    Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def] >>
    gvs[listTheory.MEM_MAP],
    strip_tac >> gvs[] >>
    qexists_tac `h` >> simp[lookup_block_def, listTheory.FIND_thm]
  ]
QED

(* ===== fn_labels structure ===== *)

Theorem fn_labels_replace_block:
  !lbl bb' bbs.
    bb'.bb_label = lbl ==>
    MAP (\bb. bb.bb_label) (replace_block lbl bb' bbs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  rw[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem fn_labels_fix_inline_phis:
  !orig new_lbl ret_bb fn.
    fn_labels (fix_inline_phis orig new_lbl ret_bb fn) = fn_labels fn
Proof
  simp[fix_inline_phis_def, fn_labels_def, LET_THM, MAP_MAP_o,
       combinTheory.o_DEF] >>
  rpt strip_tac >>
  irule listTheory.MAP_CONG >> simp[] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem rewrite_inline_blocks_labels:
  !ops outs ret_lbl bbs pi bbs' pi'.
    rewrite_inline_blocks ops outs ret_lbl bbs pi = (bbs', pi') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `bbs` >> simp[rewrite_inline_blocks_def] >>
  rpt strip_tac >> gvs[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  conj_tac
  >- (gvs[rewrite_inline_block_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]))
  >> first_x_assum drule >> simp[]
QED

Theorem inline_call_site_fn_labels:
  !prefix ret_lbl fn callee bb_lbl idx call_bb.
    lookup_block bb_lbl fn.fn_blocks = SOME call_bb ==>
    fn_labels (inline_call_site prefix ret_lbl fn callee bb_lbl idx) =
      fn_labels fn ++ [ret_lbl] ++
      MAP (STRCAT prefix) (fn_labels callee)
Proof
  rw[inline_call_site_def, fn_labels_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MAP_APPEND] >>
  imp_res_tac lookup_block_label_fresh >>
  (* replace_block preserves labels when replacement has same label *)
  qmatch_goalsub_abbrev_tac `replace_block bb_lbl trunc_bb _` >>
  `trunc_bb.bb_label = bb_lbl` by simp[Abbr `trunc_bb`] >>
  drule fn_labels_replace_block >>
  disch_then (fn th => simp[th]) >>
  qunabbrev_tac `trunc_bb` >>
  imp_res_tac rewrite_inline_blocks_labels >>
  simp[clone_function_def, LET_THM, MAP_MAP_o, combinTheory.o_DEF,
       clone_basic_block_def]
QED

(* ===== Opaque no-inl predicate (prevents isPREFIX expansion in srw_ss) ===== *)

Definition labels_no_inl_def:
  labels_no_inl fn <=> EVERY (\l. ~isPREFIX "inl" l) (fn_labels fn)
End

(* ===== Freshness predicates ===== *)

Definition labels_fresh_above_def:
  labels_fresh_above n fn <=>
    EVERY (\l. !k. k >= n ==> ~isPREFIX (inline_prefix k) l) (fn_labels fn)
End

Theorem labels_no_inl_fresh_above_0:
  !fn. labels_no_inl fn ==>
       labels_fresh_above 0 fn
Proof
  PURE_REWRITE_TAC[labels_no_inl_def] >>
  PURE_REWRITE_TAC [labels_fresh_above_def] >>
  rpt strip_tac >>
  fs[listTheory.EVERY_MEM] >>
  spose_not_then strip_assume_tac >>
  first_x_assum drule >> strip_tac >>
  `isPREFIX "inl" (inline_prefix k)` by
    (PURE_REWRITE_TAC [inline_prefix_def, isPREFIX_STRCAT] >>
     qexists_tac `STRCAT (toString k) "_"` >>
     PURE_REWRITE_TAC [STRCAT_ASSOC] >> simp[]) >>
  `isPREFIX "inl" l` by metis_tac[listTheory.isPREFIX_TRANS] >>
  gvs[]
QED

(* Weaker than labels_no_inl: no label starts with "inline_return".
   This IS preserved through inlining rounds (new labels start with
   inline_prefix k = "inl" ++ digits ++ "_", which doesn't start with
   "inline_return" because digit ≠ 'i' at position 4). *)
Definition labels_no_inline_return_def:
  labels_no_inline_return fn <=>
    EVERY (\l. ~isPREFIX "inline_return" l) (fn_labels fn)
End

Theorem labels_no_inl_no_inline_return:
  !fn. labels_no_inl fn ==> labels_no_inline_return fn
Proof
  rw[labels_no_inl_def, labels_no_inline_return_def, EVERY_MEM] >>
  rpt strip_tac >>
  spose_not_then assume_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `isPREFIX "inl" "inline_return"` by EVAL_TAC >>
  imp_res_tac isPREFIX_TRANS >> gvs[]
QED

(* Core string lemma: nothing starting with inline_prefix k can start with
   "inline_return", because the 4th char is a digit (from toString) vs 'i'.
   This is the ONE lemma; inline_prefix_not_inline_return and
   return_block_label_no_inline_return are corollaries. *)
Theorem strcat_inline_prefix_no_inline_return:
  !k l. ~isPREFIX "inline_return" (STRCAT (inline_prefix k) l)
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC[inline_prefix_def, STRCAT_ASSOC] >>
  PURE_REWRITE_TAC[STRCAT_def, isPREFIX_THM, CHAR_EQ_THM] >>
  simp[] >>
  `toString k <> ""` by simp[num_to_dec_string_nil] >>
  `EVERY isDigit (toString k)` by simp[EVERY_isDigit_num_to_dec_string] >>
  Cases_on `toString k` >> gvs[] >>
  PURE_REWRITE_TAC[STRCAT_def, isPREFIX_THM, CHAR_EQ_THM] >>
  gvs[isDigit_def]
QED

Theorem inline_prefix_not_inline_return:
  !k. ~isPREFIX "inline_return" (inline_prefix k)
Proof
  gen_tac >>
  mp_tac (Q.SPECL [`k`, `""`] strcat_inline_prefix_no_inline_return) >>
  simp[]
QED

Theorem labels_fresh_above_mono:
  !m n fn. labels_fresh_above m fn /\ m <= n ==>
           labels_fresh_above n fn
Proof
  rw[labels_fresh_above_def, listTheory.EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* ===== ALL_DISTINCT preservation ===== *)

Triviality strcat_prefix_inj:
  !prefix a b. STRCAT prefix a = STRCAT prefix b <=> a = b
Proof
  Induct >> simp[]
QED

Theorem all_distinct_map_strcat:
  !prefix ls. ALL_DISTINCT (MAP (STRCAT prefix) ls) <=> ALL_DISTINCT ls
Proof
  strip_tac >> Induct >> simp[MEM_MAP, strcat_prefix_inj]
QED

Theorem inline_one_site_fn_labels:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) ==>
    fn_labels fn' =
      fn_labels fn ++
      [return_block_label (inline_prefix ist.is_inline_count)
                          ist.is_label_counter] ++
      MAP (STRCAT (inline_prefix ist.is_inline_count)) (fn_labels callee)
Proof
  rw[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name fn.fn_blocks` >> gvs[] >>
  PairCases_on `x` >> gvs[LET_THM, renumber_fn_inst_ids_fn_labels] >>
  rename1 `find_invoke_site _ _ = SOME (bb_lbl, idx)` >>
  CASE_TAC >> gvs[fn_labels_fix_inline_phis] >>
  TRY (PairCases_on `x` >> gvs[fn_labels_fix_inline_phis]) >>
  `?call_bb. lookup_block bb_lbl fn.fn_blocks = SOME call_bb` by
    (irule find_invoke_site_lookup >> gvs[fn_labels_def] >>
     metis_tac[]) >>
  drule inline_call_site_fn_labels >> simp[]
QED

Theorem inline_one_site_all_distinct:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_fresh_above ist.is_inline_count fn /\
    ~MEM (return_block_label (inline_prefix ist.is_inline_count)
                             ist.is_label_counter)
         (MAP (STRCAT (inline_prefix ist.is_inline_count))
              (fn_labels callee)) ==>
    ALL_DISTINCT (fn_labels fn')
Proof
  rpt strip_tac >>
  drule_all inline_one_site_fn_labels >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  rpt conj_tac
  >> TRY (
    SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
    gvs[labels_fresh_above_def, EVERY_MEM] >>
    first_x_assum drule >>
    disch_then (qspec_then `ist.is_inline_count` mp_tac) >>
    simp[return_block_label_def, inline_prefix_def, isPREFIX_STRCAT] >>
    qexists_tac
      `STRCAT "inline_return" (toString ist.is_label_counter)` >>
    simp[] >> NO_TAC)
  >> TRY (simp[all_distinct_map_strcat] >> NO_TAC)
  >> (
    rpt strip_tac >> gvs[MEM_MAP] >>
    gvs[labels_fresh_above_def, EVERY_MEM] >>
    first_x_assum drule >>
    disch_then (qspec_then `ist.is_inline_count` mp_tac) >>
    simp[isPREFIX_STRCAT]
  )
QED

Theorem labels_fresh_above_inline_one_site:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    labels_fresh_above ist.is_inline_count fn ==>
    labels_fresh_above (ist.is_inline_count + 1) fn'
Proof
  rpt strip_tac >>
  drule_all inline_one_site_fn_labels >> strip_tac >>
  simp[labels_fresh_above_def, EVERY_APPEND,
       EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  TRY (
    gvs[labels_fresh_above_def, EVERY_MEM] >>
    res_tac >> gvs[] >> NO_TAC) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE[return_block_label_def,
                                     GSYM STRCAT_ASSOC]) >>
  drule inline_prefix_prefix_free >> simp[]
QED

(* ===== Inline variable set ===== *)

Definition is_inline_var_def:
  is_inline_var (v:string) = isPREFIX "inl" v
End

Definition inline_vars_def:
  inline_vars = { v | is_inline_var v }
End

Triviality inline_prefix_has_inl_prefix:
  !n. isPREFIX "inl" (inline_prefix n)
Proof
  simp[inline_prefix_def, isPREFIX_STRCAT] >>
  qexists_tac `STRCAT (toString n) "_"` >> simp[]
QED

Theorem inline_prefix_vars_subset_inline_vars:
  !n. { v | isPREFIX (inline_prefix n) v } SUBSET inline_vars
Proof
  PURE_REWRITE_TAC[SUBSET_DEF, inline_vars_def, is_inline_var_def,
                   IN_GSPEC_IFF] >>
  rpt strip_tac >>
  irule isPREFIX_TRANS >> qexists_tac `inline_prefix n` >>
  simp[inline_prefix_has_inl_prefix]
QED

(* ===== Variable freshness above a counter ===== *)

(* All variable operands in fn have no inline_prefix k for k ≥ n.
   Parallel to labels_fresh_above but for variable operands. *)
Definition vars_fresh_above_def:
  vars_fresh_above n fn <=>
    EVERY (\bb.
      EVERY (\inst.
        EVERY (\op. case op of
          Var v => !k. k >= n ==> ~isPREFIX (inline_prefix k) v
        | _ => T) inst.inst_operands /\
        EVERY (\v. !k. k >= n ==> ~isPREFIX (inline_prefix k) v)
          inst.inst_outputs)
      bb.bb_instructions)
    fn.fn_blocks
End

Theorem vars_fresh_above_mono:
  !m n fn. vars_fresh_above m fn /\ m <= n ==>
           vars_fresh_above n fn
Proof
  rw[vars_fresh_above_def, EVERY_MEM] >>
  rpt strip_tac >> res_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  TRY (Cases_on `op` >> gvs[] >> rpt strip_tac >> res_tac >> gvs[] >> NO_TAC) >>
  first_x_assum match_mp_tac >> simp[]
QED

(* vars_fresh_above is equivalent to a flat EVERY over all instructions *)
Triviality vars_fresh_above_flat:
  !n fn.
    vars_fresh_above n fn <=>
    EVERY (\inst.
      EVERY (\op. case op of
        Var v => !k. k >= n ==> ~isPREFIX (inline_prefix k) v
      | _ => T) inst.inst_operands /\
      EVERY (\v. !k. k >= n ==> ~isPREFIX (inline_prefix k) v)
        inst.inst_outputs)
    (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks))
Proof
  rw[vars_fresh_above_def, EVERY_FLAT, EVERY_MAP]
QED

(* Inner FOLDL: renumbering instructions preserves EVERY P *)
Triviality foldl_renumber_inst_every:
  !insts n acc P.
    (!x y:instruction. x.inst_operands = y.inst_operands /\
                        x.inst_outputs = y.inst_outputs ==> (P x <=> P y)) ==>
    (EVERY P (SND (FOLDL (\(id,acc') inst. (id + 1, acc' ++ [inst with inst_id := id]))
                         (n, acc) insts)) <=>
     EVERY P acc /\ EVERY P insts)
Proof
  Induct >> rw[EVERY_APPEND] >>
  first_x_assum (qspecl_then [`n + 1`,
    `acc ++ [h with inst_id := n]`, `P`] mp_tac) >>
  impl_tac >- simp[] >>
  rw[EVERY_APPEND] >>
  `P (h with inst_id := n) <=> P h` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED

(* Block-level FOLDL: renumber preserves EVERY on block instructions *)
Triviality foldl_fn_renumber_every:
  !bbs n acc P.
    (!x y:instruction. x.inst_operands = y.inst_operands /\
                        x.inst_outputs = y.inst_outputs ==> (P x <=> P y)) ==>
    (EVERY (\bb. EVERY P bb.bb_instructions)
       (SND (FOLDL (\(n,acc) bb. (\(n',bb'). (n', acc ++ [bb']))
                                    (renumber_block_inst_ids n bb))
                    (n, acc) bbs)) <=>
     EVERY (\bb. EVERY P bb.bb_instructions) acc /\
     EVERY (\bb. EVERY P bb.bb_instructions) bbs)
Proof
  Induct >> rw[EVERY_APPEND] >>
  pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`, `P`] mp_tac) >>
  impl_tac >- simp[] >>
  rw[EVERY_APPEND] >>
  gvs[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`h.bb_instructions`, `n`, `[]`, `P`] mp_tac foldl_renumber_inst_every >>
  impl_tac >- simp[] >>
  rw[] >> metis_tac[]
QED

(* renumber_fn_inst_ids doesn't change operands or outputs *)
Theorem vars_fresh_above_renumber:
  !n fn. vars_fresh_above n (renumber_fn_inst_ids fn) <=> vars_fresh_above n fn
Proof
  rw[vars_fresh_above_def, renumber_fn_inst_ids_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`fn.fn_blocks`, `0`, `[]`] foldl_fn_renumber_every) >>
  simp[] >>
  disch_then (fn th => simp[th])
QED

(* subst_label_op preserves the Var/non-Var structure *)
Triviality subst_label_op_var_case:
  !old new op P.
    (case op of Var v => P v | _ => T) ==>
    (case subst_label_op old new op of Var v => P v | _ => T)
Proof
  Cases_on `op` >> simp[subst_label_op_def] >>
  rw[]
QED

(* fix_inline_phis only changes Label operands in PHI, not Var operands.
   Proof: fix_inline_phis maps blocks. For successor blocks, it maps
   instructions: non-PHI unchanged, PHI gets subst_label_inst which
   only changes Label operands (subst_label_op Var = Var). *)
Theorem vars_fresh_above_fix_inline_phis:
  !n orig new_lbl ret_bb fn.
    vars_fresh_above n fn ==> vars_fresh_above n (fix_inline_phis orig new_lbl ret_bb fn)
Proof
  rw[vars_fresh_above_def, fix_inline_phis_def, LET_THM, EVERY_MAP] >>
  irule MONO_EVERY >> goal_assum (first_assum o mp_then Any mp_tac) >>
  rw[] >> Cases_on `MEM x.bb_label (bb_succs ret_bb)` >> fs[]
  (* MEM case: instructions go through MAP *)
  >> rw[EVERY_MAP] >> irule MONO_EVERY >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  rw[] >> Cases_on `x'.inst_opcode <> PHI` >> fs[]
  (* PHI case: subst_label_inst only changes operands *)
  >> fs[subst_label_inst_def, EVERY_MAP] >>
  irule MONO_EVERY >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  rw[] >> Cases_on `x''` >> fs[subst_label_op_def] >> rw[]
QED

(* Key bridge: a variable prefixed with inline_prefix n is fresh above n+1 *)
Triviality prefixed_var_fresh_SUC:
  !n v s. v = STRCAT (inline_prefix n) s ==>
          !k. k >= n + 1 ==> ~isPREFIX (inline_prefix k) v
Proof
  rpt strip_tac >> gvs[] >>
  `k = n` by metis_tac[inline_prefix_prefix_free] >> gvs[]
QED

(* clone_operand preserves Var-freshness: the result is either not a Var,
   or is Var (STRCAT prefix v) *)
Triviality clone_operand_var_prefixed:
  !prefix labels op.
    case clone_operand prefix labels op of
      Var v => isPREFIX prefix v
    | _ => T
Proof
  Cases_on `op` >> simp[clone_operand_def, isPREFIX_STRCAT] >> rw[]
QED

(* clone_instruction: all Var operands are prefixed, all outputs are prefixed *)
Triviality clone_instruction_vars_prefixed:
  !prefix labels inst.
    EVERY (\op. case op of Var v => isPREFIX prefix v | _ => T)
      (clone_instruction prefix labels inst).inst_operands /\
    EVERY (\v. isPREFIX prefix v)
      (clone_instruction prefix labels inst).inst_outputs
Proof
  rw[clone_instruction_def, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP, isPREFIX_STRCAT] >>
  qspecl_then [`prefix`, `labels`, `y`] strip_assume_tac clone_operand_var_prefixed >>
  Cases_on `clone_operand prefix labels y` >> gvs[isPREFIX_STRCAT]
QED

(* Bridge: instruction with all vars prefixed by inline_prefix n
   satisfies the freshness predicate at n+1 *)
Triviality prefixed_inst_fresh_SUC:
  !n inst.
    EVERY (\op. case op of Var v => isPREFIX (inline_prefix n) v | _ => T)
      inst.inst_operands /\
    EVERY (\v. isPREFIX (inline_prefix n) v) inst.inst_outputs ==>
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T)
      inst.inst_operands /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) inst.inst_outputs
Proof
  rpt strip_tac >>
  irule MONO_EVERY >> goal_assum (first_assum o mp_then Any mp_tac) >>
  rw[] >>
  TRY (Cases_on `x` >> simp[] >> rpt strip_tac) >>
  CCONTR_TAC >> gvs[] >>
  `k = n` by metis_tac[inline_prefix_prefix_free, isPREFIX_STRCAT] >>
  gvs[]
QED

(* Helper: operand freshness for a single operand that's prefixed with
   inline_prefix n — it's fresh above n+1. Avoids case-expression issues. *)
Triviality op_prefixed_n_fresh_SUC:
  !n op.
    (case op of Var v => isPREFIX (inline_prefix n) v | _ => T) ==>
    (case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T)
Proof
  rpt strip_tac >>
  Cases_on `op` >> gvs[]
  \\ CCONTR_TAC >> gvs[] >>
  `k = n` by metis_tac[inline_prefix_prefix_free, isPREFIX_STRCAT] >> gvs[]
QED

(* A single rewrite_inline_inst: if clone instruction vars are prefixed with
   inline_prefix n, and invoke_ops/invoke_outs are fresh above n+1,
   then all output instructions are fresh above n+1 *)
Theorem rewrite_inline_inst_fresh:
  !invoke_ops invoke_outs ret_lbl inst pidx insts pidx' n.
    rewrite_inline_inst invoke_ops invoke_outs ret_lbl inst pidx = (insts, pidx') /\
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) invoke_ops /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) invoke_outs /\
    EVERY (\op. case op of Var v => isPREFIX (inline_prefix n) v | _ => T) inst.inst_operands /\
    EVERY (\v. isPREFIX (inline_prefix n) v) inst.inst_outputs /\
    (inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= LENGTH invoke_outs) ==>
    EVERY (\i.
      EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) i.inst_operands /\
      EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) i.inst_outputs) insts
Proof
  rpt gen_tac >> strip_tac
  \\ fs[rewrite_inline_inst_def]
  \\ Cases_on `inst.inst_opcode = PARAM` >> gvs[]
  >- (Cases_on `pidx < LENGTH invoke_ops` >> gvs[]
      >- suspend "param_inrange"
      \\ irule prefixed_inst_fresh_SUC >> simp[])
  \\ Cases_on `inst.inst_opcode = RET` >> gvs[]
  >- suspend "ret"
  \\ irule prefixed_inst_fresh_SUC >> simp[]
QED

Resume rewrite_inline_inst_fresh[param_inrange]:
  conj_tac
  (* operand: substituted from invoke_ops *)
  >- (Cases_on `is_label_op (EL pidx invoke_ops)` >> gvs[] >>
      fs[EVERY_EL] >>
      first_x_assum (qspec_then `pidx` mp_tac) >> simp[] >>
      Cases_on `EL pidx invoke_ops` >> gvs[is_label_op_def])
  (* outputs: prefixed n => fresh above n+1 *)
  \\ fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  CCONTR_TAC >> gvs[] >>
  `k = n` by metis_tac[inline_prefix_prefix_free, isPREFIX_STRCAT] >> gvs[]
QED

Resume rewrite_inline_inst_fresh[ret]:
  simp[EVERY_EL, indexedListsTheory.LENGTH_MAPi, indexedListsTheory.EL_MAPi] >>
  rpt gen_tac >> strip_tac >> conj_tac
  (* operand: EL n' inst.inst_operands -- use op_prefixed_n_fresh_SUC *)
  >- (mp_tac op_prefixed_n_fresh_SUC >>
      disch_then (qspecl_then [`n`, `EL n' inst.inst_operands`] mp_tac) >>
      fs[EVERY_EL] >>
      first_x_assum (qspec_then `n'` mp_tac) >> simp[])
  (* output: invoke_outs[n'] -- from EVERY on invoke_outs *)
  \\ fs[EVERY_EL]
QED

Finalise rewrite_inline_inst_fresh

(* Abbreviation: instruction-level freshness predicate *)
Definition inst_fresh_above_def:
  inst_fresh_above n inst <=>
    EVERY (\op. case op of Var v => !k. k >= n ==> ~isPREFIX (inline_prefix k) v
                         | _ => T) inst.inst_operands /\
    EVERY (\v. !k. k >= n ==> ~isPREFIX (inline_prefix k) v) inst.inst_outputs
End

(* vars_fresh_above in terms of inst_fresh_above *)
Triviality vars_fresh_above_inst_fresh:
  !n f. vars_fresh_above n f <=>
    EVERY (\bb. EVERY (inst_fresh_above n) bb.bb_instructions) f.fn_blocks
Proof
  simp[vars_fresh_above_def, inst_fresh_above_def, EVERY_MEM] >>
  metis_tac[]
QED

(* Lift rewrite_inline_inst_fresh to instruction lists — raw form *)
Triviality rewrite_inline_insts_fresh_raw:
  !invoke_ops invoke_outs ret_lbl insts pidx insts' pidx' n.
    rewrite_inline_insts invoke_ops invoke_outs ret_lbl insts pidx = (insts', pidx') /\
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) invoke_ops /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) invoke_outs /\
    EVERY (\inst.
      EVERY (\op. case op of Var v => isPREFIX (inline_prefix n) v | _ => T) inst.inst_operands /\
      EVERY (\v. isPREFIX (inline_prefix n) v) inst.inst_outputs /\
      (inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= LENGTH invoke_outs)) insts ==>
    EVERY (\i.
      EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) i.inst_operands /\
      EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) i.inst_outputs) insts'
Proof
  Induct_on `insts` >>
  simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `rewrite_inline_inst invoke_ops invoke_outs ret_lbl h pidx` >>
  Cases_on `rewrite_inline_insts invoke_ops invoke_outs ret_lbl insts r` >>
  gvs[LET_THM] >>
  simp[EVERY_APPEND] >> conj_tac
  >- (mp_tac (Q.SPECL [`invoke_ops`, `invoke_outs`, `ret_lbl`, `h`, `pidx`,
                        `q`, `r`, `n`] rewrite_inline_inst_fresh) >> simp[])
  \\ first_x_assum (qspecl_then [`invoke_ops`, `invoke_outs`, `ret_lbl`,
                                  `r`, `q'`, `pidx'`, `n`] mp_tac) >> simp[]
QED

(* Wrap in inst_fresh_above *)
Triviality rewrite_inline_insts_fresh:
  !invoke_ops invoke_outs ret_lbl insts pidx insts' pidx' n.
    rewrite_inline_insts invoke_ops invoke_outs ret_lbl insts pidx = (insts', pidx') /\
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) invoke_ops /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) invoke_outs /\
    EVERY (\inst.
      EVERY (\op. case op of Var v => isPREFIX (inline_prefix n) v | _ => T) inst.inst_operands /\
      EVERY (\v. isPREFIX (inline_prefix n) v) inst.inst_outputs /\
      (inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= LENGTH invoke_outs)) insts ==>
    EVERY (inst_fresh_above (n + 1)) insts'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`invoke_ops`, `invoke_outs`, `ret_lbl`, `insts`, `pidx`,
                    `insts'`, `pidx'`, `n`] rewrite_inline_insts_fresh_raw) >>
  simp[EVERY_MEM, inst_fresh_above_def] >> metis_tac[]
QED

(* Lift to block level — drop pidx' from statement to avoid matching issues *)
Triviality rewrite_inline_block_fresh:
  !invoke_ops invoke_outs ret_lbl bb pidx bb' pidx' n.
    rewrite_inline_block invoke_ops invoke_outs ret_lbl bb pidx = (bb', pidx') /\
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) invoke_ops /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) invoke_outs /\
    EVERY (\inst.
      EVERY (\op. case op of Var v => isPREFIX (inline_prefix n) v | _ => T) inst.inst_operands /\
      EVERY (\v. isPREFIX (inline_prefix n) v) inst.inst_outputs /\
      (inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= LENGTH invoke_outs)) bb.bb_instructions ==>
    EVERY (inst_fresh_above (n + 1)) bb'.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  fs[rewrite_inline_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`invoke_ops`, `invoke_outs`, `ret_lbl`,
                    `bb.bb_instructions`, `pidx`, `insts`, `pi'`, `n`]
          rewrite_inline_insts_fresh) >> simp[]
QED

(* Lift to block-list level *)
Triviality rewrite_inline_blocks_fresh:
  !invoke_ops invoke_outs ret_lbl bbs pidx bbs' pidx' n.
    rewrite_inline_blocks invoke_ops invoke_outs ret_lbl bbs pidx = (bbs', pidx') /\
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) invoke_ops /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) invoke_outs /\
    EVERY (\bb. EVERY (\inst.
      EVERY (\op. case op of Var v => isPREFIX (inline_prefix n) v | _ => T) inst.inst_operands /\
      EVERY (\v. isPREFIX (inline_prefix n) v) inst.inst_outputs /\
      (inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= LENGTH invoke_outs)) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (inst_fresh_above (n + 1)) bb.bb_instructions) bbs'
Proof
  Induct_on `bbs` >>
  simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  conj_tac
  >- (mp_tac (Q.SPECL [`invoke_ops`, `invoke_outs`, `ret_lbl`, `h`, `pidx`,
                        `bb'`, `pi'`, `n`] rewrite_inline_block_fresh) >> simp[])
  \\ first_x_assum (qspecl_then [`invoke_ops`, `invoke_outs`, `ret_lbl`,
                                  `pi'`, `rest'`, `pi''`, `n`] mp_tac) >> simp[]
QED

(* clone_function: all blocks have prefixed vars *)
Triviality clone_function_vars_prefixed:
  !prefix func bb.
    MEM bb (clone_function prefix func).fn_blocks ==>
    EVERY (\inst.
      EVERY (\op. case op of Var v => isPREFIX prefix v | _ => T) inst.inst_operands /\
      EVERY (\v. isPREFIX prefix v) inst.inst_outputs) bb.bb_instructions
Proof
  rw[clone_function_def, LET_THM, MEM_MAP] >>
  gvs[clone_basic_block_def] >>
  simp[EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `fn_labels func`, `x`] clone_instruction_vars_prefixed) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

(* clone_instruction preserves opcode *)
Triviality clone_instruction_opcode:
  !prefix labels inst.
    (clone_instruction prefix labels inst).inst_opcode = inst.inst_opcode
Proof
  simp[clone_instruction_def]
QED

(* clone_instruction preserves operand count *)
Triviality clone_instruction_length_operands:
  !prefix labels inst.
    LENGTH (clone_instruction prefix labels inst).inst_operands = LENGTH inst.inst_operands
Proof
  simp[clone_instruction_def]
QED

(* inst_fresh_above monotonicity *)
Triviality inst_fresh_above_mono:
  !m n inst. inst_fresh_above m inst /\ m <= n ==> inst_fresh_above n inst
Proof
  simp[inst_fresh_above_def, EVERY_MEM] >> rpt strip_tac >> res_tac >>
  Cases_on `op` >> gvs[] >> rpt strip_tac >> gvs[]
QED

(* An instruction with no inline-prefixed vars is fresh above any n *)
Triviality inst_fresh_above_no_vars:
  !n inst.
    EVERY (\op. case op of Var v => F | _ => T) inst.inst_operands /\
    inst.inst_outputs = [] ==>
    inst_fresh_above n inst
Proof
  rw[inst_fresh_above_def, EVERY_MEM] >> res_tac >> Cases_on `op` >> gvs[]
QED

(* The JMP instruction generated by inline_call_site is fresh above any n *)
Triviality jmp_inst_fresh_above:
  !n lbl.
    inst_fresh_above n <| inst_id := 0; inst_opcode := JMP;
                          inst_operands := [Label lbl]; inst_outputs := [] |>
Proof
  rw[inst_fresh_above_def]
QED

(* Helper: original caller instructions are fresh above n+1 if fresh above n *)
Triviality caller_insts_fresh_suc:
  !n bbs.
    EVERY (\bb. EVERY (inst_fresh_above n) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (inst_fresh_above (n + 1)) bb.bb_instructions) bbs
Proof
  rw[EVERY_MEM] >> rpt strip_tac >> res_tac >>
  irule inst_fresh_above_mono >> qexists_tac `n` >> simp[]
QED

(* Helper: TAKE/DROP preserve inst_fresh_above *)
Triviality every_take_fresh:
  !n m l. EVERY (inst_fresh_above n) l ==> EVERY (inst_fresh_above n) (TAKE m l)
Proof
  metis_tac[EVERY_TAKE]
QED

Triviality every_drop_fresh:
  !n m l. EVERY (inst_fresh_above n) l ==> EVERY (inst_fresh_above n) (DROP m l)
Proof
  metis_tac[EVERY_DROP]
QED

(* Callee RET arity condition: every RET in the callee has at most k operands.
   This is needed because the rewrite produces assigns that index into invoke_outs. *)
Definition callee_ret_arity_le_def:
  callee_ret_arity_le k func <=>
    EVERY (\bb. EVERY (\inst.
      inst.inst_opcode = RET ==> LENGTH inst.inst_operands <= k)
      bb.bb_instructions) func.fn_blocks
End

(* clone_instruction preserves the RET arity condition *)
Triviality clone_callee_ret_arity_le:
  !prefix func k.
    callee_ret_arity_le k func ==>
    callee_ret_arity_le k (clone_function prefix func)
Proof
  rw[callee_ret_arity_le_def, clone_function_def, LET_THM, EVERY_MAP,
     clone_basic_block_def, clone_instruction_def]
QED

(* replace_block preserves EVERY when replacement satisfies P *)
Triviality every_replace_block:
  !P lbl bb' bbs.
    EVERY (\bb. P bb.bb_instructions) bbs /\
    P bb'.bb_instructions ==>
    EVERY (\bb. P bb.bb_instructions) (replace_block lbl bb' bbs)
Proof
  simp[replace_block_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >> res_tac
QED

(* clone_function + rewrite_inline_blocks bridge: clone blocks are prefixed,
   and with the RET arity condition, rewritten blocks are fresh above n+1 *)
Triviality clone_rewrite_blocks_fresh:
  !prefix invoke_ops invoke_outs ret_lbl callee rewritten_blocks pidx' n.
    rewrite_inline_blocks invoke_ops invoke_outs ret_lbl
      (clone_function prefix callee).fn_blocks 0 = (rewritten_blocks, pidx') /\
    prefix = inline_prefix n /\
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T) invoke_ops /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) invoke_outs /\
    callee_ret_arity_le (LENGTH invoke_outs) callee ==>
    EVERY (\bb. EVERY (inst_fresh_above (n + 1)) bb.bb_instructions) rewritten_blocks
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`invoke_ops`, `invoke_outs`, `ret_lbl`,
    `(clone_function (inline_prefix n) callee).fn_blocks`,
    `0`, `rewritten_blocks`, `pidx'`, `n`] rewrite_inline_blocks_fresh) >>
  simp[] >> disch_then match_mp_tac >>
  simp[EVERY_MEM] >> rpt strip_tac
  (* subgoal 1: operands prefixed *)
  >- (drule clone_function_vars_prefixed >> simp[EVERY_MEM] >>
      disch_then drule >> simp[EVERY_MEM] >> disch_then drule >> simp[])
  (* subgoal 2: outputs prefixed *)
  >- (drule clone_function_vars_prefixed >> simp[EVERY_MEM] >>
      disch_then drule >> simp[EVERY_MEM] >> disch_then drule >> simp[])
  (* subgoal 3: RET arity *)
  \\ fs[callee_ret_arity_le_def, clone_function_def, LET_THM, EVERY_MAP,
        clone_basic_block_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  gvs[MEM_MAP] >>
  first_x_assum drule >> simp[EVERY_MEM] >>
  disch_then drule >>
  (impl_tac >- gvs[clone_instruction_def]) >> simp[clone_instruction_def]
QED

(* rotate_invoke_ops preserves EVERY *)
Triviality every_rotate_invoke_ops:
  !P l. EVERY P (rotate_invoke_ops l) <=> EVERY P l
Proof
  Cases_on `l` >> simp[rotate_invoke_ops_def, EVERY_APPEND] >> metis_tac[]
QED

(* inst_fresh_above monotonicity for operand/output predicates *)
Triviality inst_fresh_above_weaken:
  !n inst.
    inst_fresh_above n inst ==>
    EVERY (\op. case op of Var v => !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v | _ => T)
      inst.inst_operands /\
    EVERY (\v. !k. k >= n+1 ==> ~isPREFIX (inline_prefix k) v) inst.inst_outputs
Proof
  simp[inst_fresh_above_def, EVERY_MEM] >> rpt strip_tac >> res_tac >>
  Cases_on `op` >> gvs[] >> rpt strip_tac >> gvs[]
QED

(* find_invoke_idx returns a valid index *)
Theorem find_invoke_idx_bound:
  !callee_name insts n idx.
    find_invoke_idx callee_name insts n = SOME idx ==>
    n <= idx /\ idx < n + LENGTH insts
Proof
  Induct_on `insts` >> simp[find_invoke_idx_def] >>
  rpt gen_tac >> IF_CASES_TAC >> gvs[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

(* find_invoke_idx returns an INVOKE instruction *)
Theorem find_invoke_idx_opcode:
  !callee_name insts n idx.
    find_invoke_idx callee_name insts n = SOME idx ==>
    (EL (idx - n) insts).inst_opcode = INVOKE
Proof
  Induct_on `insts` >> simp[find_invoke_idx_def] >>
  rpt gen_tac >> IF_CASES_TAC >> gvs[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `idx - n = SUC (idx - (n + 1))` by
    (imp_res_tac find_invoke_idx_bound >> simp[]) >>
  pop_assum (fn h => rewrite_tac[h]) >> simp[EL]
QED

(* find_invoke_site returns a valid index for lookup_block result *)
Theorem find_invoke_site_idx_bound:
  !callee_name bbs lbl idx bb.
    find_invoke_site callee_name bbs = SOME (lbl, idx) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block lbl bbs = SOME bb ==>
    idx < LENGTH bb.bb_instructions
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >> simp[] >>
  strip_tac >> gvs[]
  >- (
    `lookup_block lbl bbs = SOME bb` by
      (fs[lookup_block_def, FIND_thm] >>
       Cases_on `h.bb_label = lbl` >> gvs[] >>
       imp_res_tac find_invoke_site_label_mem >> gvs[]) >>
    res_tac
  )
  \\ `bb = h` by (fs[lookup_block_def, FIND_thm]) >>
  gvs[] >> drule find_invoke_idx_bound >> simp[]
QED

(* find_invoke_site returns an INVOKE opcode *)
Theorem find_invoke_site_opcode:
  !callee_name bbs lbl idx bb.
    find_invoke_site callee_name bbs = SOME (lbl, idx) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block lbl bbs = SOME bb ==>
    (EL idx bb.bb_instructions).inst_opcode = INVOKE
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >> simp[] >>
  strip_tac >> gvs[]
  >- (
    `lookup_block lbl bbs = SOME bb` by
      (fs[lookup_block_def, FIND_thm] >>
       Cases_on `h.bb_label = lbl` >> gvs[] >>
       imp_res_tac find_invoke_site_label_mem >> gvs[]) >>
    res_tac
  )
  \\ `bb = h` by (fs[lookup_block_def, FIND_thm]) >>
  gvs[] >> drule find_invoke_idx_opcode >> simp[]
QED



(* Core lemma: inline_call_site preserves vars_fresh_above *)
Triviality vars_fresh_above_inline_call_site:
  !n ret_lbl func callee bb_lbl idx call_bb.
    vars_fresh_above n func /\
    lookup_block bb_lbl func.fn_blocks = SOME call_bb /\
    idx < LENGTH call_bb.bb_instructions /\
    callee_ret_arity_le (LENGTH (EL idx call_bb.bb_instructions).inst_outputs) callee ==>
    vars_fresh_above (n + 1)
      (inline_call_site (inline_prefix n) ret_lbl func callee bb_lbl idx)
Proof
  rpt strip_tac >>
  simp[vars_fresh_above_inst_fresh, inline_call_site_def] >>
  (* lookup_block succeeds *)
  `lookup_block bb_lbl func.fn_blocks = SOME call_bb` by simp[] >>
  simp[] >>
  (* Abbreviate call instruction *)
  qabbrev_tac `call_inst = EL idx call_bb.bb_instructions` >>
  qabbrev_tac `invoke_ops = rotate_invoke_ops call_inst.inst_operands` >>
  qabbrev_tac `invoke_outs = call_inst.inst_outputs` >>
  (* Get freshness of call_bb instructions *)
  `EVERY (inst_fresh_above n) call_bb.bb_instructions`
    by (fs[vars_fresh_above_inst_fresh, EVERY_MEM] >>
        drule lookup_block_MEM >> strip_tac >> res_tac) >>
  (* Establish caller blocks and call_bb instructions fresh n+1 *)
  `EVERY (\bb. EVERY (inst_fresh_above (n + 1)) bb.bb_instructions) func.fn_blocks`
    by (fs[vars_fresh_above_inst_fresh, EVERY_MEM] >> rpt strip_tac >>
        res_tac >> irule inst_fresh_above_mono >> qexists_tac `n` >> simp[]) >>
  `EVERY (inst_fresh_above (n + 1)) call_bb.bb_instructions`
    by (fs[EVERY_MEM] >> rpt strip_tac >>
        res_tac >> irule inst_fresh_above_mono >> qexists_tac `n` >> simp[]) >>
  Cases_on `(clone_function (inline_prefix n) callee).fn_blocks` >> simp[]
  >- (
    (* clone has no blocks: rewrite_inline_blocks of [] = ([], 0) *)
    simp[rewrite_inline_blocks_def, EVERY_APPEND] >>
    conj_tac
    >- (irule every_replace_block >> simp[EVERY_APPEND, EVERY_TAKE, jmp_inst_fresh_above])
    \\ metis_tac[EVERY_DROP])
  \\ (* clone has blocks *)
  pairarg_tac >> gvs[] >> rename1 `(rewritten_blocks, pidx')` >>
  simp[EVERY_APPEND] >>
  rpt conj_tac
  >- (irule every_replace_block >> simp[EVERY_APPEND, EVERY_TAKE, jmp_inst_fresh_above])
  >- metis_tac[EVERY_DROP]
  (* Part 3: rewritten_blocks *)
  \\ mp_tac (Q.SPECL [`inline_prefix n`, `invoke_ops`, `invoke_outs`,
      `ret_lbl`, `callee`, `rewritten_blocks`, `pidx'`, `n`]
      clone_rewrite_blocks_fresh) >>
  simp[] >> disch_then match_mp_tac >>
  `inst_fresh_above n call_inst`
    by (fs[EVERY_EL, Abbr `call_inst`]) >>
  drule inst_fresh_above_weaken >> strip_tac >>
  simp[Abbr `invoke_ops`, every_rotate_invoke_ops, Abbr `invoke_outs`]
QED

Theorem vars_fresh_above_inline_one_site:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    vars_fresh_above ist.is_inline_count fn /\
    (!bb_lbl idx call_bb.
       find_invoke_site callee.fn_name fn.fn_blocks = SOME (bb_lbl, idx) /\
       lookup_block bb_lbl fn.fn_blocks = SOME call_bb ==>
       callee_ret_arity_le
         (LENGTH (EL idx call_bb.bb_instructions).inst_outputs) callee) ==>
    vars_fresh_above (ist.is_inline_count + 1) fn'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `n = ist.is_inline_count` >>
  fs[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name fn.fn_blocks` >> gvs[] >>
  rename1 `find_invoke_site _ _ = SOME site` >>
  PairCases_on `site` >> gvs[] >>
  simp[vars_fresh_above_renumber] >>
  (* Bridge fn_labels early *)
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by fs[fn_labels_def] >>
  (* Get call_bb *)
  drule_all find_invoke_site_lookup >> strip_tac >>
  rename1 `lookup_block site0 _ = SOME cbb` >>
  (* Get idx bound *)
  `site1 < LENGTH cbb.bb_instructions` by (
    mp_tac (Q.SPECL [`callee.fn_name`, `fn.fn_blocks`, `site0`, `site1`, `cbb`]
          find_invoke_site_idx_bound) >> simp[]) >>
  (* Get arity condition via res_tac *)
  `callee_ret_arity_le (LENGTH (EL site1 cbb.bb_instructions).inst_outputs) callee`
    by (first_x_assum (qspec_then `cbb` mp_tac) >> simp[]) >>
  (* Now case split on whether ret_bb exists *)
  Cases_on `lookup_block (return_block_label (inline_prefix n)
              ist.is_label_counter)
              (inline_call_site (inline_prefix n)
                (return_block_label (inline_prefix n) ist.is_label_counter)
                fn callee site0 site1).fn_blocks` >> gvs[]
  >- (irule vars_fresh_above_inline_call_site >> simp[] >>
      qexists_tac `cbb` >> simp[])
  \\ irule vars_fresh_above_fix_inline_phis >>
  irule vars_fresh_above_inline_call_site >> simp[] >>
  qexists_tac `cbb` >> simp[]
QED

(* ret_lbl can't collide with mapped callee labels if callee has no "inl" prefix *)
Theorem ret_lbl_not_in_mapped_callee:
  !n lc callee.
    labels_no_inl callee ==>
    ~MEM (return_block_label (inline_prefix n) lc)
         (MAP (STRCAT (inline_prefix n)) (fn_labels callee))
Proof
  PURE_REWRITE_TAC[labels_no_inl_def] >>
  rpt strip_tac >>
  gvs[MEM_MAP, return_block_label_def, strcat_prefix_inj] >>
  gvs[EVERY_MEM] >> res_tac >> gvs[]
QED

(* ===== labels_no_inline_return preservation ===== *)

(* Weaker version of ret_lbl_not_in_mapped_callee using labels_no_inline_return.
   After stripping shared prefix, "inline_return" ++ K must be in fn_labels callee.
   But labels_no_inline_return says no label starts with "inline_return". *)
Theorem ret_lbl_not_in_mapped_callee_weak:
  !n lc callee.
    labels_no_inline_return callee ==>
    ~MEM (return_block_label (inline_prefix n) lc)
         (MAP (STRCAT (inline_prefix n)) (fn_labels callee))
Proof
  PURE_REWRITE_TAC[labels_no_inline_return_def] >>
  rpt strip_tac >>
  gvs[MEM_MAP, return_block_label_def, strcat_prefix_inj] >>
  gvs[EVERY_MEM] >> res_tac >>
  gvs[isPREFIX_STRCAT]
QED

(* return_block_label with any inline_prefix does NOT start with "inline_return"
   because inline_prefix k starts with "inl" ++ digit, not "inline_return". *)
Theorem return_block_label_no_inline_return:
  !k lc. ~isPREFIX "inline_return" (return_block_label (inline_prefix k) lc)
Proof
  PURE_REWRITE_TAC[return_block_label_def] >>
  simp[strcat_inline_prefix_no_inline_return]
QED



(* labels_no_inline_return is preserved by inline_one_site on the CALLER. *)
Theorem labels_no_inline_return_inline_one_site:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    labels_no_inline_return fn ==>
    labels_no_inline_return fn'
Proof
  rpt strip_tac >>
  drule_all inline_one_site_fn_labels >> strip_tac >>
  PURE_REWRITE_TAC[labels_no_inline_return_def] >>
  qpat_x_assum `fn_labels fn' = _` (fn th => PURE_REWRITE_TAC[th]) >>
  PURE_REWRITE_TAC[EVERY_APPEND, EVERY_DEF, CONJ_ASSOC] >>
  BETA_TAC >>
  rpt conj_tac
  >- (gvs[GSYM labels_no_inline_return_def])
  >- (rewrite_tac[return_block_label_no_inline_return])
  >- ACCEPT_TAC TRUTH
  >- (PURE_REWRITE_TAC[EVERY_MAP] >> BETA_TAC >>
      rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
      rewrite_tac[strcat_inline_prefix_no_inline_return])
QED

val _ = export_theory();

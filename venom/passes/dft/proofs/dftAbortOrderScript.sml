(*
 * DFT keeps instructions that abort differently in their order (piece of
 * o1ContractDft).
 *
 * dft_block orders each aborting instruction after the whole previous run
 * of aborting instructions of another kind (dft_abort_kind, as
 * vyperlang/vyper#5336 does), so any two that are not
 * dft_abort_compatible stay in their original order.
 *
 * The proof: the abort-run edges of dft_eda reach from the later of two
 * incompatible aborting instructions to the earlier one (abort_run_inv is
 * the fold's invariant), the schedule emits every dft_eda dependency first
 * (dft_block_suffix_dft_eda), and dft_fn's loop only composes dft_block
 * steps.
 *)
Theory dftAbortOrder
Ancestors
  dftScheduleOrder dftCorrectness dftStructural dftTopoSort dftDefs
  venomWf venomInst passSharedDefs relation list rich_list sorting finite_map
Libs
  dep_rewrite

(* ===== Abort-run reachability in the EDA ===== *)

Definition abort_edge_def:
  abort_edge eda u v <=> ?ds. FLOOKUP eda u.inst_id = SOME ds /\ MEM v ds
End

(* The fold's invariant after the instructions pre: every aborting one is
   in the current run, or reachable from each member of it; and, if it is
   not in the previous run either, from each member of that. *)
Definition abort_run_inv_def:
  abort_run_inv pre acc (prev, cur) <=>
    EVERY (\r. MEM r pre /\ dft_abort_kind r.inst_opcode <> NoFail)
      (prev ++ cur) /\
    (!r. MEM r cur ==>
         dft_abort_kind r.inst_opcode = dft_abort_kind (HD cur).inst_opcode) /\
    (!x. MEM x pre /\ dft_abort_kind x.inst_opcode <> NoFail ==>
         cur <> [] /\
         (~MEM x cur ==> !r. MEM r cur ==> TC (abort_edge acc) r x) /\
         (~MEM x cur /\ ~MEM x prev ==>
            prev <> [] /\ !p. MEM p prev ==> TC (abort_edge acc) p x))
End

Theorem abort_edge_fold_mono:
  abort_edge acc u v ==>
  abort_edge (FST (FOLDL abort_run_dep_step (acc, runs) l)) u v
Proof
  rw[abort_edge_def] >> metis_tac[abort_run_fold_mono]
QED

Theorem abort_tc_fold_mono:
  TC (abort_edge acc) u v ==>
  TC (abort_edge (FST (FOLDL abort_run_dep_step (acc, runs) l))) u v
Proof
  strip_tac >> irule TC_MONOTONE >> qexists `abort_edge acc` >>
  simp[abort_edge_fold_mono]
QED

Theorem dft_abort_compatible_same_kind:
  dft_abort_kind op1 = dft_abort_kind op2 /\
  dft_abort_kind op1 <> AnyFail ==> dft_abort_compatible op1 op2
Proof
  simp[dft_abort_compatible_def]
QED

Theorem abort_run_inv_step:
  abort_run_inv pre acc (prev, cur) ==>
  abort_run_inv (pre ++ [h]) (FST (abort_run_dep_step (acc, (prev, cur)) h))
    (SND (abort_run_dep_step (acc, (prev, cur)) h)) /\
  (dft_abort_kind h.inst_opcode <> NoFail ==>
   !x. MEM x pre /\ dft_abort_kind x.inst_opcode <> NoFail /\
       ~dft_abort_compatible x.inst_opcode h.inst_opcode ==>
       TC (abort_edge (FST (abort_run_dep_step (acc, (prev, cur)) h))) h x)
Proof
  strip_tac >>
  qabbrev_tac `acc' = FST (abort_run_dep_step (acc, (prev, cur)) h)` >>
  `!u v. TC (abort_edge acc) u v ==> TC (abort_edge acc') u v` by
    (rpt strip_tac >>
     drule (Q.GENL [`l`, `runs`] abort_tc_fold_mono) >>
     disch_then (qspecl_then [`[h]`, `(prev, cur)`] mp_tac) >>
     simp[Abbr `acc'`]) >>
  Cases_on `dft_abort_kind h.inst_opcode = NoFail`
  >- (`acc' = acc` by simp[Abbr `acc'`, abort_run_dep_step_def] >>
      simp[abort_run_dep_step_def] >>
      gvs[abort_run_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `!p. MEM p (FST (abort_run_step (prev, cur) h)) ==> abort_edge acc' h p` by
    simp[Abbr `acc'`, abort_run_dep_step_def, LET_THM, abort_edge_def,
         FLOOKUP_UPDATE] >>
  `SND (abort_run_dep_step (acc, (prev, cur)) h) = abort_run_step (prev, cur) h`
    by simp[abort_run_dep_step_def, LET_THM] >>
  simp[] >>
  Cases_on `cur = [] \/ dft_abort_kind h.inst_opcode = AnyFail \/
            dft_abort_kind h.inst_opcode <> dft_abort_kind (HD cur).inst_opcode`
  >- (`abort_run_step (prev, cur) h = (cur, [h])` by
        (simp[abort_run_step_def] >> metis_tac[]) >>
      gvs[] >>
      `!x. MEM x pre /\ dft_abort_kind x.inst_opcode <> NoFail ==>
           TC (abort_edge acc') h x` by
        (rpt strip_tac >> gvs[abort_run_inv_def] >>
         Cases_on `MEM x cur` >- metis_tac[TC_SUBSET] >>
         `cur <> []` by metis_tac[] >>
         `MEM (HD cur) cur` by
           (qpat_x_assum `cur <> []` mp_tac >> Cases_on `cur` >> simp[]) >>
         metis_tac[TC_RULES]) >>
      gvs[abort_run_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `abort_run_step (prev, cur) h = (prev, cur ++ [h])` by
    gvs[abort_run_step_def] >>
  gvs[] >>
  `!x. MEM x pre /\ dft_abort_kind x.inst_opcode <> NoFail /\ ~MEM x cur ==>
       TC (abort_edge acc') h x` by
    (rpt strip_tac >> gvs[abort_run_inv_def] >>
     Cases_on `MEM x prev` >- metis_tac[TC_SUBSET] >>
     `prev <> []` by metis_tac[] >>
     `MEM (HD prev) prev` by
       (qpat_x_assum `prev <> []` mp_tac >> Cases_on `prev` >> simp[]) >>
     metis_tac[TC_RULES]) >>
  `HD (cur ++ [h]) = HD cur` by (Cases_on `cur` >> gvs[]) >>
  gvs[abort_run_inv_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >>
  metis_tac[dft_abort_compatible_same_kind]
QED

Theorem abort_run_fold_reach:
  !l pre acc prev cur x y p s.
    abort_run_inv pre acc (prev, cur) /\ l = p ++ [y] ++ s /\
    (MEM x pre \/ MEM x p) /\ dft_abort_kind x.inst_opcode <> NoFail /\
    dft_abort_kind y.inst_opcode <> NoFail /\
    ~dft_abort_compatible x.inst_opcode y.inst_opcode ==>
    TC (abort_edge (FST (FOLDL abort_run_dep_step (acc, (prev, cur)) l))) y x
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `?acc' prev' cur'.
     abort_run_dep_step (acc, (prev, cur)) h = (acc', (prev', cur'))` by
    metis_tac[pairTheory.PAIR] >>
  drule abort_run_inv_step >> disch_then (qspec_then `h` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `p` >> gvs[]
  >- (irule abort_tc_fold_mono >> first_x_assum irule >> simp[]) >>
  first_x_assum irule >> simp[] >> qexists `pre ++ [h]` >> simp[]
QED

Theorem dft_eda_abort_reach:
  FILTER (\i. ~is_pseudo i.inst_opcode) bi = p ++ [y] ++ s /\ MEM x p /\
  dft_abort_kind x.inst_opcode <> NoFail /\
  dft_abort_kind y.inst_opcode <> NoFail /\
  ~dft_abort_compatible x.inst_opcode y.inst_opcode ==>
  TC (abort_edge (dft_eda bi)) y x
Proof
  strip_tac >> simp[dft_eda_def, add_abort_run_deps_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `[]`, `build_eda bi`,
               `[]`, `[]`, `x`, `y`, `p`, `s`] mp_tac abort_run_fold_reach >>
  impl_tac >- fs[abort_run_inv_def] >> simp[]
QED

(* ===== The schedule follows reachability ===== *)

Theorem tc_abort_edge_output_order:
  !u v. TC (abort_edge eda) u v ==>
    eda_wf eda bi /\ output_eda_before eda out /\
    ALL_DISTINCT (MAP (\i. i.inst_id) out) /\
    MEM u.inst_id (MAP (\i. i.inst_id) out) ==>
    id_before (MAP (\i. i.inst_id) out) v.inst_id u.inst_id
Proof
  ho_match_mp_tac TC_INDUCT >> conj_tac
  >- (rpt strip_tac >> gvs[abort_edge_def] >>
      `?k. k < LENGTH out /\ (EL k out).inst_id = u.inst_id` by
        (gvs[MEM_MAP, MEM_EL] >> metis_tac[]) >>
      `~is_pseudo v.inst_opcode` by metis_tac[eda_wf_def] >>
      gvs[output_eda_before_def] >>
      first_x_assum (qspecl_then [`k`, `v`] mp_tac) >> simp[] >>
      strip_tac >> simp[id_before_def] >>
      qexistsl [`m`, `k`] >> simp[EL_MAP]) >>
  rpt strip_tac >>
  `id_before (MAP (\i. i.inst_id) out) u'.inst_id u.inst_id` by metis_tac[] >>
  `MEM u'.inst_id (MAP (\i. i.inst_id) out)` by metis_tac[id_before_mem] >>
  metis_tac[id_before_trans]
QED

Theorem dft_abort_kind_not_pseudo:
  dft_abort_kind op <> NoFail ==> ~is_pseudo op
Proof
  Cases_on `op` >> simp[dft_abort_kind_def, is_pseudo_def]
QED

Theorem dft_abort_kind_flip_operands:
  dft_abort_kind (flip_operands i).inst_opcode = dft_abort_kind i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_comparator_def, flip_comparison_opcode_def, dft_abort_kind_def]
QED

Theorem dft_block_abort_order:
  bb_well_formed bb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
  ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
  id_before (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions)
    x.inst_id y.inst_id
Proof
  strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `nps = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  `dft_abort_kind x.inst_opcode <> NoFail /\
   dft_abort_kind y.inst_opcode <> NoFail` by
    gvs[dft_abort_compatible_def] >>
  `~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode` by
    metis_tac[dft_abort_kind_not_pseudo] >>
  `!z. MEM z bi /\ (z.inst_id = x.inst_id \/ z.inst_id = y.inst_id) ==>
       ~is_pseudo z.inst_opcode` by
    (rpt strip_tac >>
     metis_tac[Q.ISPEC `\i:instruction. i.inst_id` all_distinct_map_mem_inj]) >>
  `id_before (MAP (\i. i.inst_id) nps) x.inst_id y.inst_id` by
    (simp[Abbr `nps`] >> DEP_REWRITE_TAC[id_before_map_filter] >>
     simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) nps)` by
    simp[Abbr `nps`, all_distinct_map_filter] >>
  `!z. MEM z nps ==> MEM z bi` by simp[Abbr `nps`, MEM_FILTER] >>
  `MEM x nps /\ MEM y nps` by simp[Abbr `nps`, MEM_FILTER] >>
  `?i j. i < j /\ j < LENGTH nps /\ EL i nps = x /\ EL j nps = y` by
    (qpat_x_assum `id_before (MAP _ nps) _ _` mp_tac >>
     simp[id_before_def, EL_MAP] >> strip_tac >>
     qexistsl [`i`, `j`] >> simp[] >>
     `MEM (EL i nps) nps /\ MEM (EL j nps) nps` by
       (conj_tac >> irule EL_MEM >> decide_tac) >>
     `i < LENGTH nps` by decide_tac >> gvs[EL_MAP] >>
     metis_tac[Q.ISPEC `\i:instruction. i.inst_id` all_distinct_map_mem_inj]) >>
  `nps = TAKE j nps ++ [y] ++ DROP (SUC j) nps` by
    (`DROP j nps = EL j nps :: DROP (SUC j) nps` by
       (REWRITE_TAC[arithmeticTheory.ADD1] >> irule DROP_EL_CONS >> decide_tac) >>
     qpat_x_assum `EL j nps = y` (SUBST1_TAC o SYM) >>
     pop_assum (fn th =>
       REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, GSYM th, TAKE_DROP])) >>
  `MEM x (TAKE j nps)` by
    (simp[MEM_EL, LENGTH_TAKE] >> qexists `i` >> simp[EL_TAKE]) >>
  `TC (abort_edge (dft_eda bi)) y x` by
    (irule dft_eda_abort_reach >> metis_tac[]) >>
  qabbrev_tac `sched = FILTER (\i. ~is_pseudo i.inst_opcode)
                         (dft_block order bb).bb_instructions` >>
  `output_eda_before (dft_eda bi) sched` by
    (simp[Abbr `sched`, Abbr `bi`] >> irule dft_block_suffix_dft_eda >>
     simp[]) >>
  `PERM (MAP (\i. i.inst_id) sched) (MAP (\i. i.inst_id) nps)` by
    (simp[Abbr `sched`, Abbr `nps`, Abbr `bi`] >>
     metis_tac[dft_block_suffix_structure]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) sched)` by
    metis_tac[ALL_DISTINCT_PERM] >>
  `MEM y.inst_id (MAP (\i. i.inst_id) sched)` by
    (drule PERM_MEM_EQ >> simp[] >> disch_then kall_tac >>
     simp[MEM_MAP] >> metis_tac[MEM_EL]) >>
  `id_before (MAP (\i. i.inst_id) sched) x.inst_id y.inst_id` by
    (irule tc_abort_edge_output_order >> simp[] >>
     qexistsl [`bi`, `dft_eda bi`] >> simp[dft_eda_wf]) >>
  qspecl_then [`order`, `bb`] mp_tac dft_block_suffix_decomposition >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  simp[MAP_APPEND] >>
  DEP_REWRITE_TAC[id_before_append_suffix] >>
  simp[Abbr `sched`, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ===== Through dft_fn's loop ===== *)

Definition block_abort_kept_def:
  block_abort_kept bb bb' <=>
    !x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
          ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
          id_before (MAP (\i. i.inst_id) bb.bb_instructions)
            x.inst_id y.inst_id ==>
          id_before (MAP (\i. i.inst_id) bb'.bb_instructions)
            x.inst_id y.inst_id
End

Theorem dft_fallible_order_kept_blocks:
  dft_fallible_order_kept fn fn' <=>
  LIST_REL block_abort_kept fn.fn_blocks fn'.fn_blocks
Proof
  simp[dft_fallible_order_kept_def, LIST_REL_EL_EQN, block_abort_kept_def]
QED

Theorem block_abort_kept_refl:
  block_abort_kept bb bb
Proof
  simp[block_abort_kept_def]
QED

Theorem block_abort_kept_trans:
  ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions) /\
  dft_block_rel a b /\ block_abort_kept a b /\ block_abort_kept b c ==>
  block_abort_kept a c
Proof
  rw[block_abort_kept_def] >>
  `dft_abort_kind x.inst_opcode <> NoFail /\
   dft_abort_kind y.inst_opcode <> NoFail` by
    gvs[dft_abort_compatible_def] >>
  `~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode` by
    metis_tac[dft_abort_kind_not_pseudo] >>
  `?u. MEM u b.bb_instructions /\ from_block a.bb_instructions u /\
       u.inst_id = x.inst_id` by metis_tac[dft_block_rel_representative] >>
  `?v. MEM v b.bb_instructions /\ from_block a.bb_instructions v /\
       v.inst_id = y.inst_id` by metis_tac[dft_block_rel_representative] >>
  `dft_abort_kind u.inst_opcode = dft_abort_kind x.inst_opcode /\
   dft_abort_kind v.inst_opcode = dft_abort_kind y.inst_opcode` by
    metis_tac[from_block_id_cases, dft_abort_kind_flip_operands] >>
  `~dft_abort_compatible u.inst_opcode v.inst_opcode` by
    gvs[dft_abort_compatible_def] >>
  metis_tac[]
QED

Theorem block_abort_kept_replace:
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  LIST_REL dft_block_rel orig curr /\
  LIST_REL block_abort_kept orig curr /\
  ALL_DISTINCT (MAP (\b. b.bb_label) curr) /\ MEM bb curr /\
  dft_block_rel bb bb' /\ block_abort_kept bb bb' ==>
  LIST_REL block_abort_kept orig
    (MAP (\b. if b.bb_label = bb.bb_label then bb' else b) curr)
Proof
  strip_tac >> simp[LIST_REL_EL_EQN] >>
  `LENGTH orig = LENGTH curr` by gvs[LIST_REL_EL_EQN] >> simp[] >>
  rpt strip_tac >> simp[EL_MAP] >>
  Cases_on `(EL n curr).bb_label = bb.bb_label`
  >- (`EL n curr = bb` by
        (irule (Q.ISPEC `\b. b.bb_label` all_distinct_map_mem_inj) >>
         simp[] >> qexists `curr` >> simp[MEM_EL] >> metis_tac[]) >>
      simp[] >> irule block_abort_kept_trans >>
      gvs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  gvs[LIST_REL_EL_EQN]
QED

Theorem dft_process_one_abort_kept:
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  LIST_REL dft_block_rel orig st.dls_blocks /\
  LIST_REL block_abort_kept orig st.dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) st.dls_blocks) /\ dft_inv st.dls_blocks ==>
  LIST_REL block_abort_kept orig
    (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  `MEM bb st.dls_blocks /\ bb.bb_label = lbl` by
    (gvs[lookup_block_def] >> drule venomExecPropsTheory.FIND_P >>
     simp[] >> metis_tac[venomExecPropsTheory.FIND_MEM]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST1_TAC o SYM) >>
  `bb_well_formed bb /\ ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
   non_pseudo_defs_before_uses bb.bb_instructions /\
   ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    gvs[dft_inv_def, EVERY_MEM] >>
  `dft_block_rel bb (dft_block (REVERSE order) bb)` by
    (irule dft_block_rel_step >> simp[]) >>
  `block_abort_kept bb (dft_block (REVERSE order) bb)` by
    (simp[block_abort_kept_def] >> rpt strip_tac >>
     irule dft_block_abort_order >> simp[]) >>
  irule block_abort_kept_replace >> simp[]
QED

Theorem dft_loop_step_abort_kept:
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  LIST_REL dft_block_rel orig (FST trip).dls_blocks /\
  LIST_REL block_abort_kept orig (FST trip).dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) (FST trip).dls_blocks) /\
  dft_inv (FST trip).dls_blocks ==>
  LIST_REL block_abort_kept orig
    (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  PairCases_on `trip` >> simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> Cases_on `trip1` >> simp[] >> strip_tac >>
  `LIST_REL block_abort_kept orig
    (FST (dft_process_one cfg lr fn trip0 h)).dls_blocks` by
    (irule dft_process_one_abort_kept >> simp[]) >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> gvs[]
QED

Theorem funpow_dft_loop_abort_kept:
  !n trip.
  EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions)) orig /\
  ALL_DISTINCT (MAP (\b. b.bb_label) orig) /\
  LIST_REL dft_block_rel orig (FST trip).dls_blocks /\
  LIST_REL block_abort_kept orig (FST trip).dls_blocks /\
  dft_inv (FST trip).dls_blocks ==>
  LIST_REL block_abort_kept orig
    (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_SUC] >> rpt strip_tac >>
  qabbrev_tac `st = FUNPOW (dft_loop_step cfg lr fn) n trip` >>
  `LIST_REL dft_block_rel orig (FST st).dls_blocks` by
    (simp[Abbr `st`] >> irule funpow_dft_loop_block_rel >> simp[]) >>
  `LIST_REL block_abort_kept orig (FST st).dls_blocks` by
    (simp[Abbr `st`] >> first_x_assum irule >> simp[]) >>
  `dft_inv (FST st).dls_blocks` by
    (simp[Abbr `st`] >> irule funpow_dft_loop_preserves_inv >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) (FST st).dls_blocks)` by
    metis_tac[dft_block_rel_labels] >>
  irule dft_loop_step_abort_kept >> simp[]
QED

Theorem dft_fn_fallible_order_kept:
  wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\ fn_inst_wf fn ==>
  dft_fallible_order_kept fn (dft_fn fn)
Proof
  strip_tac >> simp[dft_fallible_order_kept_blocks] >>
  `dft_inv fn.fn_blocks` by (irule wf_fn_initial_dft_inv >> simp[]) >>
  `EVERY (\a. ALL_DISTINCT (MAP (\i. i.inst_id) a.bb_instructions))
     fn.fn_blocks` by gvs[dft_inv_def, EVERY_MEM] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `LIST_REL dft_block_rel fn.fn_blocks fn.fn_blocks` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule dft_block_rel_refl >>
     gvs[EVERY_EL, fn_pseudos_prefix_def] >> metis_tac[MEM_EL]) >>
  `LIST_REL block_abort_kept fn.fn_blocks fn.fn_blocks` by
    simp[LIST_REL_EL_EQN, block_abort_kept_refl] >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp[] >>
  irule funpow_dft_loop_abort_kept >> simp[]
QED

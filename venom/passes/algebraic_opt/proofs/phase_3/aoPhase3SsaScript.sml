(* Phase 3 SSA: output distinctness and fresh-name avoidance for
 * ao_transform_block.
 *
 * TOP-LEVEL:
 *   ao_phase3_preserves_ssa — ssa_form preserved by the phase-3 rewrite,
 *     given the original outputs avoid the fresh-var namespace
 *     (ao_fn_fresh_vars), the original instruction ids are distinct, and
 *     mid bounds them.
 *   ao_phase3_outputs_fresh / ao_phase3_operands_fresh — the rewritten
 *     function's outputs (operands) avoid its own fresh namespace, so the
 *     names phase 4 draws above its maximum id are fresh.
 *   ao_fn_iszero_targets_clean — iszero-chain entries come from the source.
 *
 * SSA strategy (mirrors phase-3 id distinctness): every transformed
 * instruction keeps its original outputs exactly once (these avoid
 * ao_fn_fresh_vars); helper instructions get fresh outputs
 * ao_fresh_var (ao_fresh_id mid id k) s, injective in (id, k, s). Split the
 * flattened output list into the part inside ao_fn_fresh_vars (fresh,
 * distinct via id distinctness) and the part outside (the original SSA
 * outputs, distinct via ssa_form).
 *)

Theory aoPhase3Ssa
Ancestors
  algebraicOptDefs aoPhase3Wf aoPhase3Ids aoWf venomInst venomWf
  passSimulationDefs passSimulationProps passSharedDefs indexedLists rich_list
  string ASCIInumbers
Libs
  pairLib BasicProvers

(* ===== fresh-var injectivity ===== *)

Triviality ao_fresh_var_full_inj[local]:
  !id1 s1 id2 s2.
    (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
    (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
    ao_fresh_var id1 s1 = ao_fresh_var id2 s2 ==>
    id1 = id2 /\ s1 = s2
Proof
  rpt strip_tac >> gvs[] >>
  fs[ao_fresh_var_def, stringTheory.STRCAT_11,
     ASCIInumbersTheory.toString_inj]
QED

(* ===== fresh-var membership in ao_fn_fresh_vars ===== *)

(* every helper name drawn above g's maximum id is in g's fresh namespace *)
Theorem ao_fresh_id_var_fresh:
  !g mid id k s.
    fn_max_inst_id g <= mid /\ (s = "not" \/ s = "iz" \/ s = "xor") ==>
    ao_fresh_var (ao_fresh_id mid id k) s IN ao_fn_fresh_vars g
Proof
  rpt strip_tac >> simp[ao_fn_fresh_vars_def] >>
  qexistsl_tac [`ao_fresh_id mid id k`, `s`] >> gvs[ao_fresh_id_def]
QED

(* ===== outok: the per-instruction SSA invariant ===== *)

Definition outok_def:
  outok fv mid id origs (outs:string list) <=>
    FILTER (\v. ~(v IN fv)) outs = origs /\
    ALL_DISTINCT (FILTER (\v. v IN fv) outs) /\
    (!x. MEM x outs /\ x IN fv ==>
         ?k s. k < 3 /\ (s = "not" \/ s = "iz" \/ s = "xor") /\
               x = ao_fresh_var (ao_fresh_id mid id k) s)
End

(* clean instruction: no fresh outputs *)
Triviality outok_clean[local]:
  !fv mid id origs.
    EVERY (\v. ~(v IN fv)) origs ==> outok fv mid id origs origs
Proof
  rw[outok_def]
  >- (simp[listTheory.FILTER_EQ_ID] >> fs[listTheory.EVERY_MEM])
  >- (`FILTER (\v. v IN fv) origs = []` suffices_by simp[] >>
      simp[listTheory.FILTER_EQ_NIL] >> fs[listTheory.EVERY_MEM])
  >- (fs[listTheory.EVERY_MEM] >> metis_tac[])
QED

(* single fresh output prepended *)
Triviality outok_one_fresh[local]:
  !g mid id origs k s.
    k < 3 /\ (s = "not" \/ s = "iz" \/ s = "xor") /\
    fn_max_inst_id g <= mid /\
    EVERY (\w. ~(w IN ao_fn_fresh_vars g)) origs ==>
    outok (ao_fn_fresh_vars g) mid id origs
      (ao_fresh_var (ao_fresh_id mid id k) s :: origs)
Proof
  rpt strip_tac >>
  `ao_fresh_var (ao_fresh_id mid id k) s IN ao_fn_fresh_vars g` by
    (irule ao_fresh_id_var_fresh >> fs[]) >>
  `!y. MEM y origs ==> ~(y IN ao_fn_fresh_vars g)` by fs[listTheory.EVERY_MEM] >>
  `FILTER (\v. ~(v IN ao_fn_fresh_vars g)) origs = origs` by
    (simp[listTheory.FILTER_EQ_ID] >> fs[]) >>
  `FILTER (\v. v IN ao_fn_fresh_vars g) origs = []` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[]) >>
  gvs[outok_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* two distinct fresh outputs prepended *)
Triviality outok_two_fresh[local]:
  !g mid id origs k1 k2 s1 s2.
    k1 < 3 /\ k2 < 3 /\ k1 <> k2 /\
    (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
    (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
    fn_max_inst_id g <= mid /\
    EVERY (\w. ~(w IN ao_fn_fresh_vars g)) origs ==>
    outok (ao_fn_fresh_vars g) mid id origs
      (ao_fresh_var (ao_fresh_id mid id k1) s1 ::
       ao_fresh_var (ao_fresh_id mid id k2) s2 :: origs)
Proof
  rpt strip_tac >>
  `ao_fresh_var (ao_fresh_id mid id k1) s1 IN ao_fn_fresh_vars g` by
    (irule ao_fresh_id_var_fresh >> fs[]) >>
  `ao_fresh_var (ao_fresh_id mid id k2) s2 IN ao_fn_fresh_vars g` by
    (irule ao_fresh_id_var_fresh >> fs[]) >>
  `ao_fresh_var (ao_fresh_id mid id k1) s1 <>
   ao_fresh_var (ao_fresh_id mid id k2) s2` by
    metis_tac[ao_fresh_var_full_inj, ao_fresh_id_inj] >>
  `!y. MEM y origs ==> ~(y IN ao_fn_fresh_vars g)` by fs[listTheory.EVERY_MEM] >>
  `FILTER (\v. ~(v IN ao_fn_fresh_vars g)) origs = origs` by
    (simp[listTheory.FILTER_EQ_ID] >> fs[]) >>
  `FILTER (\v. v IN ao_fn_fresh_vars g) origs = []` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[]) >>
  gvs[outok_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* ===== output preservation for resolve / flips ===== *)

Triviality resolve_id[local]:
  !targets inst. (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality resolve_outputs[local]:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality pre_flip_id[local]:
  !inst. (ao_pre_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality pre_flip_outputs[local]:
  !inst. (ao_pre_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_outputs[local]:
  !inst. (ao_post_flip_inst inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_last_outputs[local]:
  !l. FLAT (MAP (\i. i.inst_outputs) (ao_post_flip_last l)) =
      FLAT (MAP (\i. i.inst_outputs) l)
Proof
  ho_match_mp_tac ao_post_flip_last_ind >>
  rw[ao_post_flip_last_def, post_flip_outputs]
QED

(* ===== output lists for each per-opcode helper ===== *)

(* simple opts: single output-preserving instruction *)
Triviality opt_shift_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_shift inst)) = inst.inst_outputs
Proof
  rw[ao_opt_shift_def] >> every_case_tac >> gvs[]
QED

Triviality opt_signextend_outs[local]:
  !ra lbl idx inst.
    FLAT (MAP (\i. i.inst_outputs) (ao_opt_signextend ra lbl idx inst)) =
    inst.inst_outputs
Proof
  rw[ao_opt_signextend_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_exp_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_exp inst)) = inst.inst_outputs
Proof
  rw[ao_opt_exp_def] >> every_case_tac >> gvs[]
QED

Triviality opt_addsub_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_addsub inst)) = inst.inst_outputs
Proof
  rw[ao_opt_addsub_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_and_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_and inst)) = inst.inst_outputs
Proof
  rw[ao_opt_and_def] >> every_case_tac >> gvs[]
QED

Triviality opt_muldiv_outs[local]:
  !inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_muldiv inst)) = inst.inst_outputs
Proof
  rw[ao_opt_muldiv_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality opt_or_outs[local]:
  !dfg inst. FLAT (MAP (\i. i.inst_outputs) (ao_opt_or dfg inst)) =
    inst.inst_outputs
Proof
  rw[ao_opt_or_def] >> every_case_tac >> gvs[]
QED

(* eq: branches that introduce a single fresh helper ("not" or "xor") *)
Triviality opt_eq_outok[local]:
  !g mid dfg inst.
    fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs) (ao_opt_eq mid dfg inst)))
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >> gvs[] >>
  TRY (irule outok_clean >> fs[] >> NO_TAC) >>
  irule outok_one_fresh >> fs[]
QED

(* comparator helpers *)
Triviality cmp_prefer_iz_zero_outok[local]:
  !g mid id op1 inst.
    inst.inst_id = id /\ fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs) (ao_cmp_prefer_iz_zero mid id op1 inst)))
Proof
  rw[ao_cmp_prefer_iz_zero_def] >> irule outok_one_fresh >> fs[]
QED

Triviality cmp_prefer_iz_max_outok[local]:
  !g mid id op1 inst.
    inst.inst_id = id /\ fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs) (ao_cmp_prefer_iz_max mid id op1 inst)))
Proof
  rw[ao_cmp_prefer_iz_max_def] >> irule outok_two_fresh >> fs[]
QED

Triviality cmp_prefer_iz_general_outok[local]:
  !g mid id op1 op2 inst.
    inst.inst_id = id /\ fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_cmp_prefer_iz_general mid id op1 op2 inst)))
Proof
  rw[ao_cmp_prefer_iz_general_def] >> irule outok_two_fresh >> fs[]
QED

Triviality opt_comparator_outok[local]:
  !g mid dfg ra lbl idx inst.
    fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_opt_comparator mid dfg ra lbl idx inst)))
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  TRY (irule outok_clean >> fs[] >> NO_TAC) >>
  FIRST [
    (irule cmp_prefer_iz_zero_outok >> fs[]),
    (irule cmp_prefer_iz_max_outok >> fs[]),
    (irule cmp_prefer_iz_general_outok >> fs[]),
    (irule outok_one_fresh >> fs[])
  ]
QED

(* ===== peephole and transform_inst ===== *)

Triviality peephole_outok[local]:
  !g mid dfg ra lbl idx inst.
    fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_peephole_inst mid dfg ra lbl idx inst)))
Proof
  rpt strip_tac >>
  rw[ao_peephole_inst_def] >>
  simp[opt_shift_outs, opt_signextend_outs, opt_exp_outs, opt_addsub_outs,
       opt_and_outs, opt_muldiv_outs, opt_or_outs] >>
  TRY (irule outok_clean >> fs[] >> NO_TAC) >>
  FIRST [
    (irule opt_eq_outok >> fs[]),
    (irule opt_comparator_outok >> fs[])
  ]
QED

Triviality producer_outs[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r ==>
    FLAT (MAP (\i. i.inst_outputs) r) = inst.inst_outputs
Proof
  rw[ao_opt_producer_def] >> every_case_tac >> gvs[]
QED

Triviality transform_inst_outok[local]:
  !g mid dfg ra lbl idx targets inst.
    fn_max_inst_id g <= mid /\
    EVERY (\v. ~(v IN ao_fn_fresh_vars g)) inst.inst_outputs ==>
    outok (ao_fn_fresh_vars g) mid inst.inst_id inst.inst_outputs
      (FLAT (MAP (\i. i.inst_outputs)
        (ao_transform_inst mid dfg ra lbl idx targets inst)))
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM, post_flip_last_outputs] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >>
       simp[post_flip_last_outputs, resolve_outputs]) >>
  TRY (irule outok_clean >> simp[resolve_outputs] >> fs[] >> NO_TAC) >>
  FIRST [
    (drule producer_outs >> strip_tac >>
     gvs[post_flip_last_outputs, resolve_outputs] >>
     irule outok_clean >> fs[]),
    (qspecl_then [`g`, `mid`, `dfg`, `ra`, `lbl`, `idx`,
       `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`]
       mp_tac peephole_outok >>
     impl_tac
     >- (gvs[pre_flip_id, resolve_id, pre_flip_outputs, resolve_outputs])
     >- simp[pre_flip_id, resolve_id, pre_flip_outputs, resolve_outputs,
             post_flip_last_outputs])
  ]
QED

(* ===== post-flip: ids, outputs and operands ===== *)

Triviality post_flip_id[local]:
  !inst. (ao_post_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[]
QED

Triviality post_flip_operand_mem[local]:
  !x inst. MEM x (ao_post_flip_inst inst).inst_operands ==> MEM x inst.inst_operands
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

(* every member of ao_post_flip_last l is an original element or the
   post-flip of one; either way it has the same id and outputs, and its
   operands are a subset (post_flip only swaps operands) *)
Triviality post_flip_last_mem[local]:
  !l p. MEM p (ao_post_flip_last l) ==>
        ?q. MEM q l /\ p.inst_id = q.inst_id /\
            p.inst_outputs = q.inst_outputs /\
            (!x. MEM x p.inst_operands ==> MEM x q.inst_operands)
Proof
  ho_match_mp_tac ao_post_flip_last_ind >> rpt conj_tac
  >- rw[ao_post_flip_last_def]
  >- (rw[ao_post_flip_last_def] >>
      gvs[post_flip_id, post_flip_outputs] >>
      metis_tac[post_flip_operand_mem])
  >- (rw[ao_post_flip_last_def] >> gvs[]
      >- (qexists_tac `inst` >> simp[])
      >- (first_x_assum drule >> strip_tac >> qexists_tac `q` >> simp[]))
QED

(* ===== pieces: distinctness over a flattened list of transformed insts ===== *)

(* clean part: outputs outside fv recover the original output lists *)
Triviality pieces_clean[local]:
  !fv mid pieces.
    EVERY (\p. outok fv mid (FST p) (FST (SND p)) (SND (SND p))) pieces ==>
    FILTER (\v. ~(v IN fv)) (FLAT (MAP (\p. SND (SND p)) pieces)) =
    FLAT (MAP (\p. FST (SND p)) pieces)
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.FILTER_APPEND_DISTRIB] >>
  fs[outok_def] >> metis_tac[]
QED

(* fresh part: every fresh output is a helper name of some piece id *)
Triviality pieces_fresh_mem[local]:
  !fv mid pieces y.
    EVERY (\p. outok fv mid (FST p) (FST (SND p)) (SND (SND p))) pieces /\
    MEM y (FILTER (\v. v IN fv) (FLAT (MAP (\p. SND (SND p)) pieces))) ==>
    ?b k s. MEM b (MAP FST pieces) /\ k < 3 /\
            (s = "not" \/ s = "iz" \/ s = "xor") /\
            y = ao_fresh_var (ao_fresh_id mid b k) s
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.FILTER_APPEND_DISTRIB, listTheory.MEM_FILTER] >> gvs[]
  >- (fs[outok_def] >> res_tac >> metis_tac[])
  >- (first_x_assum drule >> simp[listTheory.MEM_FILTER] >>
      strip_tac >> metis_tac[])
QED

Triviality pieces_fresh_distinct[local]:
  !fv mid pieces.
    ALL_DISTINCT (MAP FST pieces) /\
    EVERY (\p. outok fv mid (FST p) (FST (SND p)) (SND (SND p))) pieces ==>
    ALL_DISTINCT
      (FILTER (\v. v IN fv) (FLAT (MAP (\p. SND (SND p)) pieces)))
Proof
  Induct_on `pieces` >> simp[] >>
  rpt strip_tac >> PairCases_on `h` >>
  fs[listTheory.MAP, listTheory.FLAT] >>
  PURE_REWRITE_TAC[listTheory.FILTER_APPEND_DISTRIB,
    listTheory.ALL_DISTINCT_APPEND] >>
  rpt conj_tac
  >- fs[outok_def]
  >- (first_x_assum irule >> fs[] >> metis_tac[])
  >- (rpt strip_tac >>
      rename1 `MEM y (FILTER _ h2)` >>
      `MEM y h2 /\ y IN fv` by
        (qpat_x_assum `MEM y (FILTER _ h2)` mp_tac >>
         simp[listTheory.MEM_FILTER]) >>
      `?k1 s1. k1 < 3 /\ (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
               y = ao_fresh_var (ao_fresh_id mid h0 k1) s1` by
        (fs[outok_def] >> metis_tac[]) >>
      `?b k2 s2. MEM b (MAP FST pieces) /\ k2 < 3 /\
                 (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
                 y = ao_fresh_var (ao_fresh_id mid b k2) s2` by
        (irule pieces_fresh_mem >> fs[] >> metis_tac[]) >>
      `ao_fresh_id mid h0 k1 = ao_fresh_id mid b k2` by
        metis_tac[ao_fresh_var_full_inj] >>
      `h0 = b` by metis_tac[ao_fresh_id_inj] >>
      gvs[])
QED

(* ===== MAPi fusion ===== *)

Triviality mapi_no_index[local]:
  !l (f:'a -> 'b). MAPi (\i x. f x) l = MAP f l
Proof
  Induct >> simp[indexedListsTheory.MAPi_def, combinTheory.o_DEF]
QED

Triviality map_mapi[local]:
  !l (h:'b -> 'c) (g:num -> 'a -> 'b).
    MAP h (MAPi g l) = MAPi (\i x. h (g i x)) l
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`h`, `g o SUC`] mp_tac) >>
  simp[combinTheory.o_DEF]
QED

Triviality flat_map_flat_mapi[local]:
  !l (f:'b -> 'c list) (g:num -> 'a -> 'b list).
    FLAT (MAP f (FLAT (MAPi g l))) =
    FLAT (MAPi (\i x. FLAT (MAP f (g i x))) l)
Proof
  Induct >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  simp[listTheory.MAP_FLAT, listTheory.FLAT_APPEND] >>
  first_x_assum (qspecl_then [`f`, `g o SUC`] mp_tac) >>
  simp[combinTheory.o_DEF, listTheory.MAP_FLAT]
QED

(* ===== block / function plumbing ===== *)

Definition block_outpieces_def:
  block_outpieces mid dfg ra targets bb =
    MAPi (\idx inst.
      (inst.inst_id, inst.inst_outputs,
       FLAT (MAP (\i. i.inst_outputs)
         (ao_transform_inst mid dfg ra bb.bb_label idx targets inst))))
      bb.bb_instructions
End

Triviality block_outpieces_fst[local]:
  !mid dfg ra targets bb.
    MAP FST (block_outpieces mid dfg ra targets bb) =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[block_outpieces_def, map_mapi, mapi_no_index] >> simp[ETA_AX]
QED

Triviality block_outpieces_fst_snd[local]:
  !mid dfg ra targets bb.
    MAP (\p. FST (SND p)) (block_outpieces mid dfg ra targets bb) =
    MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  rw[block_outpieces_def, map_mapi, mapi_no_index] >> simp[ETA_AX]
QED

(* ao_resolve_phis_block (the PHI post-pass in ao_transform_block) only
   rewrites PHI operands, so it preserves every instruction's outputs. *)
Triviality ao_resolve_phis_block_outputs[local]:
  MAP (\i. i.inst_outputs) (ao_resolve_phis_block targets bb).bb_instructions =
  MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  simp[ao_resolve_phis_block_def, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> rw[ao_resolve_iszero_inst_def]
QED

Triviality block_outpieces_snd_snd_flat[local]:
  !mid dfg ra targets bb.
    FLAT (MAP (\p. SND (SND p)) (block_outpieces mid dfg ra targets bb)) =
    FLAT (MAP (\i. i.inst_outputs)
      (ao_transform_block mid dfg ra targets bb).bb_instructions)
Proof
  rw[block_outpieces_def, ao_transform_block_def, map_mapi,
     flat_map_flat_mapi, ao_resolve_phis_block_outputs]
QED

Definition all_outpieces_def:
  all_outpieces mid dfg ra targets fn =
    FLAT (MAP (block_outpieces mid dfg ra targets) fn.fn_blocks)
End

Triviality all_outpieces_fst[local]:
  !mid dfg ra targets fn.
    MAP FST (all_outpieces mid dfg ra targets fn) =
    MAP (\i. i.inst_id) (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[all_outpieces_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def, block_outpieces_fst]
QED

Triviality all_outpieces_fst_snd[local]:
  !mid dfg ra targets fn.
    FLAT (MAP (\p. FST (SND p)) (all_outpieces mid dfg ra targets fn)) =
    FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))
Proof
  rpt gen_tac >>
  simp[all_outpieces_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[fn_insts_blocks_def, listTheory.FLAT_APPEND, block_outpieces_fst_snd]
QED

Triviality all_outpieces_snd_snd_flat[local]:
  !mid dfg ra targets fn.
    FLAT (MAP (\p. SND (SND p)) (all_outpieces mid dfg ra targets fn)) =
    FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
      (ao_transform_block mid dfg ra targets bb).bb_instructions))
      fn.fn_blocks)
Proof
  rpt gen_tac >>
  simp[all_outpieces_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[listTheory.FLAT_APPEND, block_outpieces_snd_snd_flat]
QED

Triviality all_outpieces_outok[local]:
  !mid dfg ra targets fn.
    fn_max_inst_id fn <= mid /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    EVERY (\p. outok (ao_fn_fresh_vars fn) mid (FST p) (FST (SND p))
                 (SND (SND p)))
      (all_outpieces mid dfg ra targets fn)
Proof
  rw[all_outpieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_outpieces_def, indexedListsTheory.MEM_MAPi] >>
  qmatch_goalsub_abbrev_tac `ao_transform_inst _ _ _ _ _ _ inst` >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
     qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
     simp[listTheory.MEM_EL, Abbr`inst`] >> metis_tac[]) >>
  irule transform_inst_outok >>
  simp[listTheory.MEM_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> metis_tac[]
QED

(* ===== top-level ===== *)

Triviality map_inst_id_fn_insts[local]:
  !fn. MAP (\i. i.inst_id) (fn_insts fn) =
       FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)
Proof
  gen_tac >> simp[fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >> simp[fn_insts_blocks_def]
QED

Triviality all_distinct_split_fv[local]:
  !(l:string list) fv.
    ALL_DISTINCT (FILTER (\v. v IN fv) l) /\
    ALL_DISTINCT (FILTER (\v. ~(v IN fv)) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h IN fv` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  qexists_tac `fv` >> simp[] >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

Triviality outpieces_all_distinct[local]:
  !fv mid pieces.
    ALL_DISTINCT (MAP FST pieces) /\
    ALL_DISTINCT (FLAT (MAP (\p. FST (SND p)) pieces)) /\
    EVERY (\p. outok fv mid (FST p) (FST (SND p)) (SND (SND p))) pieces ==>
    ALL_DISTINCT (FLAT (MAP (\p. SND (SND p)) pieces))
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FILTER (\v. v IN fv) (FLAT (MAP (\p. SND (SND p)) pieces)))`
    by metis_tac[pieces_fresh_distinct] >>
  `FILTER (\v. ~(v IN fv)) (FLAT (MAP (\p. SND (SND p)) pieces)) =
     FLAT (MAP (\p. FST (SND p)) pieces)`
    by metis_tac[pieces_clean] >>
  metis_tac[all_distinct_split_fv]
QED

Theorem ao_phase3_preserves_ssa:
  !mid dfg ra targets fn.
    ssa_form fn /\ fn_inst_ids_distinct fn /\ fn_max_inst_id fn <= mid /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    ssa_form
      (function_map_transform (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt strip_tac >>
  simp[ssa_form_def] >>
  `FLAT (MAP (\i. i.inst_outputs)
     (fn_insts (function_map_transform
        (ao_transform_block mid dfg ra targets) fn))) =
   FLAT (MAP (\p. SND (SND p)) (all_outpieces mid dfg ra targets fn))` by
    (simp[Once function_map_transform_def] >>
     simp[fn_insts_def, listTheory.MAP_FLAT, listTheory.MAP_MAP_o,
          combinTheory.o_DEF, all_outpieces_snd_snd_flat] >>
     qspec_tac (`fn.fn_blocks`,`bbs`) >>
     Induct >>
     simp[fn_insts_blocks_def, listTheory.FLAT_APPEND, listTheory.MAP_FLAT,
          listTheory.MAP_MAP_o, combinTheory.o_DEF]) >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`ao_fn_fresh_vars fn`, `mid`,
               `all_outpieces mid dfg ra targets fn`]
    mp_tac outpieces_all_distinct >>
  impl_tac
  >- (rpt conj_tac
      >- (simp[all_outpieces_fst, map_inst_id_fn_insts] >>
          fs[fn_inst_ids_distinct_def])
      >- (simp[all_outpieces_fst_snd] >> fs[ssa_form_def])
      >- (irule all_outpieces_outok >> rpt strip_tac >> metis_tac[])) >>
  simp[]
QED

(* ===== freshness carry-over: phase-3 output avoids its own fresh namespace =====
   Every name the pass synthesizes is ao_fresh_var n s where n is the id of the
   helper instruction defining it, and every fresh operand is defined in the
   same expansion.  Since all of fn1's ids are at most fn_max_inst_id fn1, no
   output or operand of fn1 lies in ao_fn_fresh_vars fn1.  This keeps phase
   4's helper names (above fn_max_inst_id fn1) fresh, and lets
   ao_fresh_names_disjoint carry over from one run of the pass to the next. *)

(* selfout: every fresh output of an instruction is named by its own id *)
Definition selfout_def:
  selfout fv (l:instruction list) <=>
    !q x. MEM q l /\ MEM x q.inst_outputs /\ x IN fv ==>
          ?s. (s = "not" \/ s = "iz" \/ s = "xor") /\ x = ao_fresh_var q.inst_id s
End

(* opclosed: every fresh operand is an output of the same expansion *)
Definition opclosed_def:
  opclosed fv (l:instruction list) <=>
    !q w. MEM q l /\ MEM (Var w) q.inst_operands /\ w IN fv ==>
          MEM w (FLAT (MAP (\i. i.inst_outputs) l))
End

Triviality selfout_flat_clean[local]:
  !fv l. EVERY (\v. v NOTIN fv) (FLAT (MAP (\i. i.inst_outputs) l)) ==>
         selfout fv l
Proof
  rw[selfout_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  metis_tac[]
QED

Triviality opclosed_clean[local]:
  !fv l.
    (!q w. MEM q l /\ MEM (Var w) q.inst_operands ==> w NOTIN fv) ==>
    opclosed fv l
Proof
  rw[opclosed_def] >> metis_tac[]
QED

Triviality selfout_flat[local]:
  !fv ls. EVERY (selfout fv) ls ==> selfout fv (FLAT ls)
Proof
  rw[selfout_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT] >> metis_tac[]
QED

Triviality selfout_post_flip_last[local]:
  !fv l. selfout fv l ==> selfout fv (ao_post_flip_last l)
Proof
  rw[selfout_def] >> drule post_flip_last_mem >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Triviality opclosed_post_flip_last[local]:
  !fv l. opclosed fv l ==> opclosed fv (ao_post_flip_last l)
Proof
  rw[opclosed_def, post_flip_last_outputs] >>
  drule post_flip_last_mem >> strip_tac >> metis_tac[]
QED

(* The M2 PHI iszero-resolution post-pass only rewrites PHI operands, so it
   preserves the id and outputs of every instruction. *)
Triviality resolve_phi_inst_id[local]:
  !targets i.
    (if i.inst_opcode = PHI then ao_resolve_iszero_inst targets i else i).inst_id =
    i.inst_id
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality resolve_phi_inst_outputs[local]:
  !targets i.
    (if i.inst_opcode = PHI then ao_resolve_iszero_inst targets i else i).inst_outputs =
    i.inst_outputs
Proof
  rw[ao_resolve_iszero_inst_def]
QED

Triviality map_resolve_phi_outputs[local]:
  !targets l.
    FLAT (MAP (\i. i.inst_outputs)
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)) =
    FLAT (MAP (\i. i.inst_outputs) l)
Proof
  Induct_on `l` >> simp[resolve_phi_inst_outputs]
QED

Triviality selfout_map_resolve[local]:
  !targets fv l.
    selfout fv l ==>
    selfout fv
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)
Proof
  rw[selfout_def, listTheory.MEM_MAP] >>
  gvs[resolve_phi_inst_outputs, resolve_phi_inst_id] >> metis_tac[]
QED

(* resolve substitutes either the original operand or a chain entry. *)
Triviality resolve_op_cases[local]:
  !targets opc op.
    ao_resolve_iszero_op targets opc op = op \/
    ?vv chain. op = Var vv /\ ALOOKUP targets vv = SOME chain /\
               MEM (ao_resolve_iszero_op targets opc op) chain
Proof
  rpt gen_tac >> Cases_on `op` >>
  PURE_REWRITE_TAC[ao_resolve_iszero_op_def] >> simp[] >>
  Cases_on `ALOOKUP targets s` >> simp[] >>
  rename1 `ALOOKUP targets s = SOME chain` >>
  IF_CASES_TAC >> simp[] >>
  simp[LET_THM] >>
  IF_CASES_TAC
  >- (DISJ2_TAC >> irule listTheory.EL_MEM >> fs[]) >>
  simp[]
QED

Triviality resolve_op_clean[local]:
  !targets opc op fv.
    (!w. op = Var w ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    !w. ao_resolve_iszero_op targets opc op = Var w ==> w NOTIN fv
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  qspecl_then [`targets`, `opc`, `op`] strip_assume_tac resolve_op_cases
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `MEM chain (MAP SND targets)` by
    (drule alistTheory.ALOOKUP_MEM >> rw[listTheory.MEM_MAP] >>
     qexists_tac `(vv, chain)` >> simp[]) >>
  metis_tac[]
QED

Triviality resolve_inst_opnds_clean[local]:
  !targets inst fv.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    !w. MEM (Var w) (ao_resolve_iszero_inst targets inst).inst_operands ==>
        w NOTIN fv
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_resolve_iszero_inst_def, listTheory.MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  rename1 `Var w = ao_resolve_iszero_op targets inst.inst_opcode op` >>
  qspecl_then [`targets`, `inst.inst_opcode`, `op`, `fv`] mp_tac
    resolve_op_clean >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> gvs[] >> metis_tac[])
      >- first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

(* The resolution rewrites a PHI operand to an earlier iszero-chain entry.
   Chain entries are clean, so a fresh operand of a resolved instruction must
   have come from the original operand list. *)
Triviality opclosed_map_resolve[local]:
  !targets fv l.
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) /\
    opclosed fv l ==>
    opclosed fv
      (MAP (\inst. if inst.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets inst else inst) l)
Proof
  rw[opclosed_def, map_resolve_phi_outputs, listTheory.MEM_MAP] >>
  rename1 `MEM xx l` >>
  reverse (Cases_on `xx.inst_opcode = PHI`) >> gvs[]
  >- metis_tac[] >>
  qpat_x_assum `MEM (Var w) (ao_resolve_iszero_inst _ _).inst_operands` mp_tac >>
  simp[ao_resolve_iszero_inst_def, listTheory.MEM_MAP] >> rpt strip_tac >>
  qmatch_asmsub_rename_tac `Var w = ao_resolve_iszero_op targets PHI op` >>
  qspecl_then [`targets`, `PHI`, `op`] strip_assume_tac resolve_op_cases
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `?yy. chain = SND yy /\ MEM yy targets` by
    (qexists_tac `(vv, chain)` >> simp[] >> metis_tac[alistTheory.ALOOKUP_MEM]) >>
  `w NOTIN fv` by metis_tac[] >> gvs[]
QED

(* ===== per-opt selfout / opclosed ===== *)

Triviality pre_flip_operand_mem[local]:
  !x inst. MEM x (ao_pre_flip_inst inst).inst_operands ==> MEM x inst.inst_operands
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

(* ===== per-opt operand cleanliness (simple opts) ===== *)

Triviality opt_shift_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_shift inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_shift_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_signextend_opnds_clean[local]:
  !fv ra lbl idx inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_signextend ra lbl idx inst) /\
          MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_signextend_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_exp_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_exp inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_exp_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_addsub_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_addsub inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_addsub_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_and_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_and inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_and_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_muldiv_opnds_clean[local]:
  !fv inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_muldiv inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_muldiv_def, LET_THM] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_or_opnds_clean[local]:
  !fv dfg inst. (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    !q w. MEM q (ao_opt_or dfg inst) /\ MEM (Var w) q.inst_operands ==> w NOTIN fv
Proof
  rw[ao_opt_or_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

(* range comparisons fold only to literals *)

Triviality cmp_range_lit[local]:
  !ra lbl idx inst is_gt signed r.
    ao_opt_cmp_range ra lbl idx inst is_gt signed = SOME r ==> ?w. r = Lit w
Proof
  rw[ao_opt_cmp_range_def, LET_THM] >> every_case_tac >> gvs[]
QED

Triviality producer_opnds[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r ==>
    !q w. MEM q r /\ MEM (Var w) q.inst_operands ==>
          MEM (Var w) inst.inst_operands
Proof
  rw[ao_opt_producer_def] >> every_case_tac >> gvs[] >> metis_tac[]
QED

Triviality opt_eq_selfout[local]:
  !fv mid dfg inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    selfout fv (ao_opt_eq mid dfg inst)
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >>
  rw[selfout_def] >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Triviality opt_eq_opclosed[local]:
  !fv mid dfg inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    opclosed fv (ao_opt_eq mid dfg inst)
Proof
  rw[ao_opt_eq_def, LET_THM] >> every_case_tac >>
  rw[opclosed_def] >> gvs[] >> metis_tac[]
QED

Triviality opt_comparator_selfout[local]:
  !fv mid dfg ra lbl idx inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    selfout fv (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  rw[selfout_def, ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
     ao_cmp_prefer_iz_general_def] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Triviality opt_comparator_opclosed[local]:
  !fv mid dfg ra lbl idx inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    opclosed fv (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC, pairarg_tac] >> simp[]) >>
  TRY (drule cmp_range_lit >> strip_tac >> gvs[]) >>
  rw[opclosed_def, ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
     ao_cmp_prefer_iz_general_def] >>
  gvs[] >> metis_tac[]
QED

Triviality peephole_selfout[local]:
  !fv mid dfg ra lbl idx inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    selfout fv (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >> rw[ao_peephole_inst_def] >>
  FIRST [
    (irule opt_eq_selfout >> fs[]),
    (irule opt_comparator_selfout >> fs[]),
    (irule selfout_flat_clean >>
     simp[opt_shift_outs, opt_signextend_outs, opt_exp_outs, opt_addsub_outs,
          opt_and_outs, opt_muldiv_outs, opt_or_outs] >> fs[])
  ]
QED

Triviality peephole_opclosed[local]:
  !fv mid dfg ra lbl idx inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) ==>
    opclosed fv (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >> rw[ao_peephole_inst_def] >>
  FIRST [
    (irule opt_eq_opclosed >> fs[]),
    (irule opt_comparator_opclosed >> fs[]),
    (irule opclosed_clean >>
     FIRST [match_mp_tac opt_shift_opnds_clean,
            match_mp_tac opt_signextend_opnds_clean,
            match_mp_tac opt_exp_opnds_clean,
            match_mp_tac opt_addsub_opnds_clean,
            match_mp_tac opt_and_opnds_clean,
            match_mp_tac opt_muldiv_opnds_clean,
            match_mp_tac opt_or_opnds_clean] >> fs[]),
    (irule opclosed_clean >> rpt strip_tac >> gvs[] >> metis_tac[])
  ]
QED

Triviality transform_inst_selfout[local]:
  !fv mid dfg ra lbl idx targets inst.
    EVERY (\v. v NOTIN fv) inst.inst_outputs ==>
    selfout fv (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >> simp[]) >>
  TRY (irule selfout_flat_clean >> simp[resolve_outputs] >> fs[] >> NO_TAC) >>
  irule selfout_post_flip_last >>
  FIRST [
    (irule selfout_flat_clean >> drule producer_outs >>
     simp[resolve_outputs] >> fs[]),
    (irule peephole_selfout >> simp[pre_flip_outputs, resolve_outputs] >> fs[])
  ]
QED

Triviality transform_inst_opclosed[local]:
  !fv mid dfg ra lbl idx targets inst.
    (!w. MEM (Var w) inst.inst_operands ==> w NOTIN fv) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==> w NOTIN fv) ==>
    opclosed fv (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  `!w. MEM (Var w) (ao_resolve_iszero_inst targets inst).inst_operands ==>
       w NOTIN fv` by
    (match_mp_tac resolve_inst_opnds_clean >> conj_tac >> metis_tac[]) >>
  simp[ao_transform_inst_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC] >> simp[]) >>
  TRY (irule opclosed_clean >> rpt strip_tac >> gvs[] >> metis_tac[] >> NO_TAC) >>
  irule opclosed_post_flip_last >>
  FIRST [
    (irule opclosed_clean >> rpt strip_tac >>
     drule_all producer_opnds >> metis_tac[]),
    (irule peephole_opclosed >> rpt strip_tac >>
     drule pre_flip_operand_mem >> metis_tac[])
  ]
QED

(* ===== function-level plumbing ===== *)

(* one piece per source instruction: its expansion after PHI resolution *)
Definition block_instpieces_def:
  block_instpieces mid dfg ra targets bb =
    MAPi (\idx inst.
      MAP (\i. if i.inst_opcode = PHI
               then ao_resolve_iszero_inst targets i else i)
        (ao_transform_inst mid dfg ra bb.bb_label idx targets inst))
      bb.bb_instructions
End

Triviality block_instpieces_flat[local]:
  !mid dfg ra targets bb.
    FLAT (block_instpieces mid dfg ra targets bb) =
    (ao_transform_block mid dfg ra targets bb).bb_instructions
Proof
  rw[block_instpieces_def, ao_transform_block_def, ao_resolve_phis_block_def,
     listTheory.MAP_FLAT, map_mapi] >>
  simp[combinTheory.o_DEF]
QED

Definition all_instpieces_def:
  all_instpieces mid dfg ra targets fn =
    FLAT (MAP (block_instpieces mid dfg ra targets) fn.fn_blocks)
End

Triviality all_instpieces_insts[local]:
  !mid dfg ra targets fn.
    fn_insts (function_map_transform (ao_transform_block mid dfg ra targets) fn) =
    FLAT (all_instpieces mid dfg ra targets fn)
Proof
  rpt gen_tac >>
  simp[all_instpieces_def, function_map_transform_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[fn_insts_blocks_def, listTheory.FLAT_APPEND, block_instpieces_flat]
QED

Triviality all_instpieces_every[local]:
  !P mid dfg ra targets fn.
    (!lbl idx inst. MEM inst (fn_insts fn) ==>
       P (MAP (\i. if i.inst_opcode = PHI
                   then ao_resolve_iszero_inst targets i else i)
            (ao_transform_inst mid dfg ra lbl idx targets inst))) ==>
    EVERY P (all_instpieces mid dfg ra targets fn)
Proof
  rw[all_instpieces_def, listTheory.EVERY_MEM, listTheory.MEM_FLAT,
     listTheory.MEM_MAP] >>
  gvs[block_instpieces_def, indexedListsTheory.MEM_MAPi] >>
  first_x_assum irule >>
  simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
  qpat_x_assum `MEM _ fn.fn_blocks` (irule_at Any) >>
  simp[listTheory.MEM_EL] >> metis_tac[]
QED

(* fresh namespaces shrink as the maximum id grows *)
Triviality fresh_vars_mono[local]:
  !g h. fn_max_inst_id g <= fn_max_inst_id h ==>
        ao_fn_fresh_vars h SUBSET ao_fn_fresh_vars g
Proof
  rw[pred_setTheory.SUBSET_DEF, ao_fn_fresh_vars_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Triviality own_id_not_fresh[local]:
  !g n s. n <= fn_max_inst_id g /\ (s = "not" \/ s = "iz" \/ s = "xor") ==>
          ao_fresh_var n s NOTIN ao_fn_fresh_vars g
Proof
  rpt strip_tac >> fs[ao_fn_fresh_vars_def] >>
  metis_tac[ao_fresh_var_full_inj, arithmeticTheory.LESS_EQ_LESS_TRANS,
            prim_recTheory.LESS_REFL]
QED

Triviality phase3_max_id_mono[local]:
  !mid dfg ra targets fn.
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid) ==>
    fn_max_inst_id fn <=
    fn_max_inst_id
      (function_map_transform (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt strip_tac >> irule fn_max_inst_id_le >> rpt strip_tac >>
  qspecl_then [`mid`, `dfg`, `ra`, `targets`, `fn`, `inst`] mp_tac
    ao_phase3_keeps_inst_ids >>
  impl_tac >- metis_tac[] >>
  metis_tac[fn_max_inst_id_bound]
QED

Theorem ao_phase3_outputs_fresh:
  !mid dfg ra targets fn.
    fn_max_inst_id fn <= mid /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) ==>
    !inst v.
      MEM inst (fn_insts
        (function_map_transform (ao_transform_block mid dfg ra targets) fn)) /\
      MEM v inst.inst_outputs ==>
      v NOTIN ao_fn_fresh_vars
        (function_map_transform (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt gen_tac >> strip_tac >>
  `!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid` by
    metis_tac[fn_max_inst_id_bound, arithmeticTheory.LESS_EQ_TRANS] >>
  drule phase3_max_id_mono >>
  disch_then (qspecl_then [`dfg`, `ra`, `targets`] assume_tac) >>
  qabbrev_tac `fn1 =
    function_map_transform (ao_transform_block mid dfg ra targets) fn` >>
  `selfout (ao_fn_fresh_vars fn) (fn_insts fn1)` by
    (simp[Abbr `fn1`, all_instpieces_insts] >>
     irule selfout_flat >> irule all_instpieces_every >> rpt strip_tac >>
     irule selfout_map_resolve >> irule transform_inst_selfout >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `v IN ao_fn_fresh_vars fn`
  >- (`?s. (s = "not" \/ s = "iz" \/ s = "xor") /\
           v = ao_fresh_var inst.inst_id s` by (fs[selfout_def] >> metis_tac[]) >>
      `inst.inst_id <= fn_max_inst_id fn1` by metis_tac[fn_max_inst_id_bound] >>
      metis_tac[own_id_not_fresh]) >>
  metis_tac[fresh_vars_mono, pred_setTheory.SUBSET_DEF]
QED

Theorem ao_phase3_operands_fresh:
  !mid dfg ra targets fn.
    fn_max_inst_id fn <= mid /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!inst v. MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN ao_fn_fresh_vars fn) /\
    (!ch w. MEM ch (MAP SND targets) /\ MEM (Var w) ch ==>
            w NOTIN ao_fn_fresh_vars fn) ==>
    !inst v.
      MEM inst (fn_insts
        (function_map_transform (ao_transform_block mid dfg ra targets) fn)) /\
      MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_fn_fresh_vars
        (function_map_transform (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`mid`, `dfg`, `ra`, `targets`, `fn`] mp_tac
    ao_phase3_outputs_fresh >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `!inst. MEM inst (fn_insts fn) ==> inst.inst_id <= mid` by
    metis_tac[fn_max_inst_id_bound, arithmeticTheory.LESS_EQ_TRANS] >>
  drule phase3_max_id_mono >>
  disch_then (qspecl_then [`dfg`, `ra`, `targets`] assume_tac) >>
  `EVERY (opclosed (ao_fn_fresh_vars fn)) (all_instpieces mid dfg ra targets fn)` by
    (irule all_instpieces_every >> rpt strip_tac >>
     irule opclosed_map_resolve >> conj_tac >- metis_tac[] >>
     irule transform_inst_opclosed >> metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `v IN ao_fn_fresh_vars fn`
  >- (`?l. MEM l (all_instpieces mid dfg ra targets fn) /\ MEM inst l` by
        (fs[all_instpieces_insts, listTheory.MEM_FLAT] >> metis_tac[]) >>
      `MEM v (FLAT (MAP (\i. i.inst_outputs) l))` by
        (fs[listTheory.EVERY_MEM, opclosed_def] >> metis_tac[]) >>
      `?y. MEM y l /\ MEM v y.inst_outputs` by
        (fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
      `MEM y (fn_insts (function_map_transform
         (ao_transform_block mid dfg ra targets) fn))` by
        (simp[all_instpieces_insts, listTheory.MEM_FLAT] >> metis_tac[]) >>
      metis_tac[]) >>
  metis_tac[fresh_vars_mono, pred_setTheory.SUBSET_DEF]
QED

(* ===== iszero targets: chain entries come from the source ===== *)

(* targets chain entries are operands/outputs of the source instructions. *)
Triviality iszero_step_acc[local]:
  !acc h (P:string->bool).
    (!ch w. MEM ch (MAP SND acc) /\ MEM (Var w) ch ==> P w) /\
    (!w. MEM (Var w) h.inst_operands ==> P w) /\
    (!w. MEM w h.inst_outputs ==> P w) ==>
    !ch w. MEM ch (MAP SND (ao_compute_iszero_step acc h)) /\
           MEM (Var w) ch ==> P w
Proof
  rw[ao_compute_iszero_step_def] >> every_case_tac >>
  gvs[listTheory.MEM_SNOC] >> TRY (metis_tac[]) >>
  rename1 `ALOOKUP acc vv = SOME chain` >>
  `MEM (vv, chain) acc` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `MEM chain (MAP SND acc)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `(vv, chain)` >> simp[]) >>
  metis_tac[]
QED

Triviality iszero_step_entries[local]:
  !insts acc (P:string->bool).
    (!ch w. MEM ch (MAP SND acc) /\ MEM (Var w) ch ==> P w) /\
    (!inst w. MEM inst insts /\
       (MEM (Var w) inst.inst_operands \/ MEM w inst.inst_outputs) ==> P w) ==>
    !ch w. MEM ch (MAP SND (FOLDL ao_compute_iszero_step acc insts)) /\
           MEM (Var w) ch ==> P w
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`ao_compute_iszero_step acc h`, `P`] mp_tac) >>
  impl_tac >- (
    conj_tac
    >- (qspecl_then [`acc`, `h`, `P`] mp_tac iszero_step_acc >>
        impl_tac >- (rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
        simp[])
    >- (rpt strip_tac >> metis_tac[])) >>
  simp[]
QED

(* chains of the iszero targets only reference operands/outputs of source insts *)
Theorem ao_fn_iszero_targets_clean:
  !fn P.
    (!inst w. MEM inst (fn_insts fn) /\
       (MEM (Var w) inst.inst_operands \/ MEM w inst.inst_outputs) ==> P w) ==>
    !ch w. MEM ch (MAP SND (ao_compute_fn_iszero_targets fn)) /\
           MEM (Var w) ch ==> P w
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_compute_fn_iszero_targets_def, ao_compute_iszero_targets_def] >>
  qspecl_then [`fn_insts fn`, `[]`, `P`] mp_tac iszero_step_entries >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  simp[]
QED


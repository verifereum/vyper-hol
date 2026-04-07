(*
 * Liveness Analysis — Internal Correctness Proofs
 *
 * Proves:
 *   live_vars_bounded_proof  — live variables come from fn_all_vars
 *   liveness_sound_proof     — live variable implies use-before-def path
 *
 * Proofs are re-exported via livenessAnalysisPropsScript.sml.
 *)

Theory livenessProofs
Ancestors
  livenessDefs cfgDefs dfAnalyzeProofs dfHelperProofs
  cfgAnalysisProps cfgHelpers venomWf

Libs
  listTheory rich_listTheory pred_setTheory arithmeticTheory venomInstTheory
  finite_mapTheory pairTheory indexedListsTheory
  cfgHelpersTheory venomStateTheory
  dfHelperDefsTheory dfAnalyzeDefsTheory dfAnalyzePropsTheory

(* ===== Basic helpers ===== *)

val list_union_mem = list_union_mem_proof;

Theorem live_update_mem:
  ∀v defs uses live.
    MEM v (live_update defs uses live) ⇔
    (MEM v live ∧ ¬MEM v defs) ∨ MEM v uses
Proof
  rw[live_update_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem phi_pairs_subset_uses[local]:
  ∀ops v. MEM v (MAP SND (phi_pairs ops)) ==> MEM v (operand_vars ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  rw[phi_pairs_def, operand_vars_def, operand_var_def] >>
  rpt strip_tac >>
  TRY (Cases_on `operand_var v1`) >> fs[]
QED

(* Helper: collect_phis returns PHI instructions that are in the original list *)
Theorem collect_phis_mem:
  ∀instrs inst. MEM inst (collect_phis instrs) ==>
    MEM inst instrs ∧ inst.inst_opcode = PHI
Proof
  Induct >> simp[collect_phis_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  strip_tac >> gvs[]
QED

(* Helper: FOLDL in input_vars_from only produces elements from base or matching *)
Theorem input_vars_foldl_mem[local]:
  ∀base acc placed op_map matching v.
    MEM v (FST (FOLDL (λ(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) ==>
    MEM v acc ∨ MEM v base ∨ ∃i. FLOOKUP matching i = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[MEM_APPEND] >> metis_tac[])
  >- (rename1 `FLOOKUP op_map h = SOME phi_idx` >>
      Cases_on `MEM phi_idx placed` >> simp[]
      >- (strip_tac >> first_x_assum drule >> metis_tac[])
      >- (Cases_on `FLOOKUP matching phi_idx` >> simp[]
          >- (strip_tac >> first_x_assum drule >> metis_tac[])
          >- (rename1 `FLOOKUP matching phi_idx = SOME src_v` >>
              strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[MEM_APPEND] >> metis_tac[])))
QED

(* FIND produces a member satisfying the predicate *)
Theorem find_some_mem[local]:
  ∀P ls x. FIND P ls = SOME x ==> MEM x ls ∧ P x
Proof
  Induct_on `ls` >> simp[FIND_thm] >> rpt gen_tac >>
  Cases_on `P h` >> simp[] >> strip_tac >> gvs[] >> res_tac >> simp[]
QED

(* Helper: FOLDL over indexed phis preserves matching invariant *)
Theorem foldl_phi_matching_inv[local]:
  ∀phis n acc_op acc_m src i v.
    FLOOKUP (SND (FOLDL
      (λ(op_map,matching) (j,phi).
        (FOLDL (λm w. m |+ (w, j)) op_map phi.inst_outputs,
         case FIND (λ(l,w). l = src) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_, w) => matching |+ (j, w)))
      (acc_op, acc_m) (MAPi (λk phi. (n + k, phi)) phis))) i = SOME v ==>
    FLOOKUP acc_m i = SOME v ∨
    ∃phi. MEM phi phis ∧ MEM (src, v) (phi_pairs phi.inst_operands)
Proof
  Induct_on `phis` >- simp[MAPi_def] >>
  rpt gen_tac >>
  simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (λk phi'. (n + SUC k, phi')) phis =
   MAPi (λk phi'. (SUC n + k, phi')) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >>
  strip_tac >>
  first_x_assum (qspecl_then [
    `SUC n`,
    `FOLDL (λm w. m |+ (w, n)) acc_op h.inst_outputs`,
    `case FIND (λ(l,w). l = src) (phi_pairs h.inst_operands) of
       NONE => acc_m | SOME (_, w) => acc_m |+ (n, w)`,
    `src`, `i`, `v`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[]
  >- ((* Case: FLOOKUP acc_m' i = SOME v, trace through FIND *)
      Cases_on `FIND (λ(l,w). l = src) (phi_pairs h.inst_operands)`
      (* NONE: acc_m' = acc_m, immediate *)
      >- gvs[]
      (* SOME: acc_m' = acc_m |+ (n, SND x) *)
      >- (PairCases_on `x` >> gvs[FLOOKUP_UPDATE] >>
          Cases_on `n = i` >> gvs[] >>
          (* n = i: v came from FIND result *)
          disj2_tac >> qexists_tac `h` >> simp[] >>
          drule_then strip_assume_tac find_some_mem >> gvs[]))
  >- (disj2_tac >> metis_tac[])
QED

(* Helper: build_phi_maps matching values correspond to phi pairs.
   Uses MEM (not EL) for cleaner interface. *)
Theorem build_phi_maps_matching_mem[local]:
  ∀src phis i v.
    FLOOKUP (SND (build_phi_maps src phis)) i = SOME v ==>
    ∃phi. MEM phi phis ∧ MEM (src, v) (phi_pairs phi.inst_operands)
Proof
  rw[build_phi_maps_def, LET_THM] >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `FEMPTY`, `src`, `i`, `v`]
    mp_tac foldl_phi_matching_inv >> simp[]
QED

(* input_vars_from correctness: every output variable either came from
   the base set or corresponds to a PHI operand in the instruction list *)
Theorem input_vars_from_phi_correct_proof:
  ∀src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base ∨
    ∃inst. MEM inst instrs ∧ inst.inst_opcode = PHI ∧
           MEM (src_label, v) (phi_pairs inst.inst_operands)
Proof
  rpt gen_tac >> simp[input_vars_from_def, LET_THM] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps src_label (collect_phis instrs)` >>
  rename1 `build_phi_maps _ _ = (op_map, matching)` >> simp[] >>
  simp[Once UNCURRY] >>
  strip_tac >>
  drule input_vars_foldl_mem >> strip_tac >> gvs[] >>
  qspecl_then [`src_label`, `collect_phis instrs`, `i`, `v`]
    mp_tac build_phi_maps_matching_mem >>
  impl_tac >- gvs[] >>
  strip_tac >>
  disj2_tac >> qexists_tac `phi` >> simp[] >>
  metis_tac[collect_phis_mem]
QED

Theorem input_vars_from_vars_bounded[local]:
  ∀src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base ∨
    ∃inst. MEM inst instrs ∧ MEM v (inst_uses inst)
Proof
  rpt strip_tac >>
  drule input_vars_from_phi_correct_proof >> strip_tac >> fs[] >>
  disj2_tac >> qexists_tac `inst` >> rw[inst_uses_def] >>
  irule phi_pairs_subset_uses >>
  simp[MEM_MAP] >> qexists_tac `(src_label, v)` >> simp[]
QED

Theorem fn_all_vars_mem[local]:
  ∀bbs bb inst v.
    MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
    (MEM v (inst_uses inst) ∨ MEM v (inst_defs inst)) ==>
    MEM v (fn_all_vars bbs)
Proof
  rw[fn_all_vars_def, MEM_FLAT, MEM_MAP, MEM_APPEND] >> (
    qexists_tac `FLAT (MAP (\i. inst_uses i ++ inst_defs i)
      bb.bb_instructions)` >>
    rw[MEM_FLAT, MEM_MAP, MEM_APPEND] >>
    TRY (qexists_tac `bb` >> rw[]) >>
    qexists_tac `inst_uses inst ++ inst_defs inst` >>
    rw[MEM_APPEND] >> qexists_tac `inst` >> rw[])
QED

Theorem lookup_block_mem[local]:
  ∀lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
  gvs[lookup_block_def] >> res_tac >> simp[]
QED

Theorem lookup_block_label[local]:
  ∀lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm]
QED

Theorem lookup_block_unique[local]:
  ∀lbl bbs bb bb'.
    lookup_block lbl bbs = SOME bb ∧ lookup_block lbl bbs = SOME bb' ==>
    bb = bb'
Proof
  rw[] >> gvs[]
QED

Theorem fn_labels_lookup_block[local]:
  ∀lbl bbs.
    MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    ∃bb. lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[] >> rw[] >> metis_tac[lookup_block_def]
QED

(* ===================================================================
   Boundedness proof: live_vars_bounded_proof

   Strategy: Show that all df_at values only contain vars from fn_all_vars.
   Use the fixpoint equations (df_at_intra_transfer, df_at_inter_transfer)
   plus the fact that liveness_transfer and liveness_edge_transfer only
   add variables from actual block instructions.
   =================================================================== *)

(* liveness_transfer preserves boundedness for actual block instructions *)
Theorem liveness_transfer_bounded[local]:
  ∀bbs inst live U.
    (∀v. MEM v live ==> MEM v U) ∧
    (∀v. MEM v (inst_uses inst) ==> MEM v U) ==>
    ∀v. MEM v (liveness_transfer bbs inst live) ==> MEM v U
Proof
  rw[liveness_transfer_def, live_update_mem] >> metis_tac[]
QED

(* liveness_edge_transfer preserves boundedness for actual blocks *)
Theorem liveness_edge_transfer_bounded[local]:
  ∀bbs succ_lbl cur_lbl live U.
    (∀v. MEM v live ==> MEM v U) ∧
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ==>
    ∀v. MEM v (liveness_edge_transfer bbs succ_lbl cur_lbl live) ==> MEM v U
Proof
  rw[liveness_edge_transfer_def] >>
  Cases_on `lookup_block succ_lbl bbs` >> fs[] >>
  drule input_vars_from_vars_bounded >> strip_tac >> fs[] >>
  imp_res_tac lookup_block_mem >> metis_tac[]
QED

(* list_union preserves boundedness *)
Theorem list_union_bounded[local]:
  ∀a b U.
    (∀v. MEM v a ==> MEM v U) ∧ (∀v. MEM v b ==> MEM v U) ==>
    ∀v. MEM v (list_union a b) ==> MEM v U
Proof
  rw[list_union_mem] >> metis_tac[]
QED

(* Backward fold invariant with MEM restriction (mirror of forward) *)
Theorem df_fold_backward_invariant[local]:
  ∀instrs transfer lbl idx acc inst_map fv im P.
    df_fold_backward transfer lbl instrs idx acc inst_map = (fv, im) ∧
    P acc ∧
    (∀k v. FLOOKUP inst_map k = SOME v ==> P v) ∧
    (∀inst v. MEM inst instrs ∧ P v ==> P (transfer inst v)) ==>
    P fv ∧ ∀k v. FLOOKUP im k = SOME v ==> P v
Proof
  Induct_on `instrs` >> rpt gen_tac >> strip_tac
  (* Base: [] *)
  >- (fs[df_fold_backward_def, LET_THM] >> rw[] >>
      Cases_on `k = (lbl,idx)` >> fs[FLOOKUP_UPDATE] >> metis_tac[])
  (* Step: h::instrs *)
  >> fs[df_fold_backward_def, LET_THM] >>
     pairarg_tac >> fs[] >> rw[]
     (* P (transfer h acc') *)
     >- (qpat_x_assum `!transfer lbl idx acc inst_map fv im P. _`
           (qspecl_then [`transfer`, `lbl`, `idx+1`, `acc`, `inst_map`,
                         `acc'`, `inst_map'`, `P`] mp_tac) >>
         rw[] >> res_tac >> fs[])
     (* FLOOKUP (inst_map' |+ ...) k = SOME v ⇒ P v *)
     >> qpat_x_assum `!transfer lbl idx acc inst_map fv im P. _`
          (qspecl_then [`transfer`, `lbl`, `idx+1`, `acc`, `inst_map`,
                        `acc'`, `inst_map'`, `P`] mp_tac) >>
        rw[] >> Cases_on `k = (lbl,idx)` >>
        fs[FLOOKUP_UPDATE] >> res_tac >> metis_tac[]
QED

(* list_union absorption: join(join(a,b),b) = join(a,b) *)
Theorem list_union_absorption[local]:
  ∀a b. list_union (list_union a b) b = list_union a b
Proof
  rw[list_union_def, FILTER_APPEND_DISTRIB] >>
  `FILTER (\v. ~MEM v (a ++ FILTER (\v. ~MEM v a) b)) b = []` suffices_by
    simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >>
  rpt strip_tac >> simp[MEM_FILTER, MEM_APPEND]
QED

(* list_union as set union *)
Theorem list_union_set[local]:
  ∀a b. set (list_union a b) = set a ∪ set b
Proof
  rw[list_union_def, LIST_TO_SET_APPEND, EXTENSION, MEM_FILTER] >>
  metis_tac[]
QED

(* list_union strictly grows when result differs *)
Theorem list_union_neq_card[local]:
  ∀a b. list_union a b <> a ==>
    CARD (set a) < CARD (set (list_union a b))
Proof
  rpt strip_tac >>
  irule CARD_PSUBSET >> simp[FINITE_LIST_TO_SET] >>
  simp[PSUBSET_DEF, list_union_set, SUBSET_DEF] >>
  simp[EXTENSION] >>
  fs[list_union_def] >>
  `FILTER (\v. ~MEM v a) b <> []` by (strip_tac >> fs[]) >>
  Cases_on `FILTER (\v. ~MEM v a) b` >> fs[] >>
  qexists_tac `h` >>
  `MEM h (FILTER (\v. ~MEM v a) b)` by simp[] >>
  fs[MEM_FILTER]
QED

(* FOLDL list_union preserves boundedness *)
Theorem foldl_list_union_bounded[local]:
  ∀vs init U.
    (∀v. MEM v init ==> MEM v U) ∧
    (∀vals. MEM vals vs ==> ∀v. MEM v vals ==> MEM v U) ==>
    ∀v. MEM v (FOLDL list_union init vs) ==> MEM v U
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`list_union init h`, `U`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- (rpt strip_tac >> irule list_union_bounded >>
          qexists_tac `init` >> qexists_tac `h` >> metis_tac[])
      >- metis_tac[])
  >> metis_tac[]
QED

(* Key: df_process_block preserves "all values bounded by U" *)
Theorem edge_transfer_bounded_from_state[local]:
  ∀bbs st nbr lbl U x.
    (∀l v. FLOOKUP st.ds_boundary l = SOME v ==> ∀x. MEM x v ==> MEM x U) ∧
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    MEM x (liveness_edge_transfer bbs nbr lbl (df_boundary [] st nbr)) ==>
    MEM x U
Proof
  rpt strip_tac >>
  qspecl_then [`bbs`, `nbr`, `lbl`, `df_boundary [] st nbr`, `U`]
    mp_tac liveness_edge_transfer_bounded >>
  disch_then irule >> rpt conj_tac
  >> TRY (first_x_assum ACCEPT_TAC)
  >> rpt strip_tac >>
  fs[df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary nbr` >> fs[] >> metis_tac[]
QED

Theorem joined_value_bounded[local]:
  ∀bbs st dir cfg entry_val lbl U x.
    (∀l v. FLOOKUP st.ds_boundary l = SOME v ==> ∀x. MEM x v ==> MEM x U) ∧
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    (case entry_val of NONE => T
     | SOME (l,v) => ∀x. MEM x v ==> MEM x U) ∧
    MEM x (df_joined_val dir [] list_union liveness_edge_transfer bbs
             entry_val cfg st lbl) ==>
    MEM x U
Proof
  rpt strip_tac >>
  fs[df_joined_val_def, LET_THM] >>
  qabbrev_tac `edge_vals = MAP (\nbr. liveness_edge_transfer bbs nbr lbl
    (df_boundary [] st nbr))
    (case dir of Forward => cfg_preds_of cfg lbl
     | Backward => cfg_succs_of cfg lbl)` >>
  `∀ev. MEM ev edge_vals ==> ∀v. MEM v ev ==> MEM v U` by (
    rpt strip_tac >>
    fs[Abbr`edge_vals`, MEM_MAP] >> gvs[] >>
    drule_all edge_transfer_bounded_from_state >> simp[]) >>
  (* entry_val structure: NONE => base; SOME (ev,v) => join v base or base *)
  Cases_on `entry_val` >> fs[]
  (* NONE: just the base case expression *)
  >- (Cases_on `edge_vals` >> fs[] >>
      qspecl_then [`t`, `list_union [] h`, `U`]
        mp_tac foldl_list_union_bounded >>
      impl_tac
      >- (rpt conj_tac >> rpt strip_tac >>
          fs[list_union_mem] >> metis_tac[])
      >- metis_tac[])
  (* SOME: both lbl=ev_lbl and lbl≠ev_lbl reduce to FOLDL goal after gvs *)
  >- (PairCases_on `x'` >> gvs[] >>
      Cases_on `lbl = x'0` >> gvs[] >>
      Cases_on `edge_vals` >> fs[list_union_mem] >>
      (* remaining goals all have h::t and MEM x (FOLDL ...) *)
      `∀v. MEM v (FOLDL list_union (list_union [] h) t) ==> MEM v U` by (
        qspecl_then [`t`, `list_union [] h`, `U`]
          mp_tac foldl_list_union_bounded >>
        impl_tac
        >- (rpt conj_tac >> rpt strip_tac >>
            fs[list_union_mem] >> metis_tac[])
        >- metis_tac[]) >>
      metis_tac[])
QED

Theorem fold_block_bounded[local]:
  ∀dir bbs lbl instrs init_val fv im U.
    df_fold_block dir (liveness_transfer bbs) lbl instrs init_val = (fv, im) ∧
    (∀x. MEM x init_val ==> MEM x U) ∧
    (∀inst. MEM inst instrs ==>
            ∀v. MEM v (inst_uses inst) ==> MEM v U) ∧
    (∀inst. MEM inst instrs ==>
            ∀v. MEM v (inst_defs inst) ==> MEM v U) ==>
    (∀x. MEM x fv ==> MEM x U) ∧
    (∀k v. FLOOKUP im k = SOME v ==> ∀x. MEM x v ==> MEM x U)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dir` >> fs[df_fold_block_def]
  >- (qspecl_then [`instrs`, `liveness_transfer bbs`, `lbl`, `0`,
        `init_val`, `FEMPTY`, `fv`, `im`,
        `\vs:string list. !x. MEM x vs ==> MEM x U`]
      mp_tac df_fold_forward_invariant >>
      simp[FLOOKUP_DEF] >> disch_then irule >>
      rpt strip_tac >> irule liveness_transfer_bounded >> metis_tac[])
  >- (qspecl_then [`instrs`, `liveness_transfer bbs`, `lbl`, `0`,
        `init_val`, `FEMPTY`, `fv`, `im`,
        `\vs:string list. !x. MEM x vs ==> MEM x U`]
      mp_tac df_fold_backward_invariant >>
      simp[FLOOKUP_DEF] >> disch_then irule >>
      rpt strip_tac >> irule liveness_transfer_bounded >> metis_tac[])
QED

Theorem df_process_bounded[local]:
  ∀bbs dir cfg entry_val lbl st U.
    (∀l v. FLOOKUP st.ds_boundary l = SOME v ==>
           ∀x. MEM x v ==> MEM x U) ∧
    (∀l v. FLOOKUP st.ds_inst l = SOME v ==>
           ∀x. MEM x v ==> MEM x U) ∧
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_uses inst) ==> MEM v U) ∧
    (∀bb inst v. MEM bb bbs ∧ MEM inst bb.bb_instructions ∧
                 MEM v (inst_defs inst) ==> MEM v U) ∧
    (case entry_val of NONE => T
     | SOME (l,v) => ∀x. MEM x v ==> MEM x U) ==>
    (∀l v. FLOOKUP (df_process_block dir ([]:string list) list_union
              liveness_transfer liveness_edge_transfer bbs entry_val
              cfg bbs lbl st).ds_boundary l = SOME v ==>
           ∀x. MEM x v ==> MEM x U) ∧
    (∀l v. FLOOKUP (df_process_block dir ([]:string list) list_union
              liveness_transfer liveness_edge_transfer bbs entry_val
              cfg bbs lbl st).ds_inst l = SOME v ==>
           ∀x. MEM x v ==> MEM x U)
Proof
  rpt gen_tac >> strip_tac >>
  simp[df_process_block_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `df_fold_block _ _ _ instrs joined` >>
  qabbrev_tac `fold_result = df_fold_block dir
    (liveness_transfer bbs) lbl instrs joined` >>
  PairCases_on `fold_result` >> fs[] >>
  (* joined bounded *)
  `!x. MEM x joined ==> MEM x U` by (
    simp[Abbr`joined`] >> rpt strip_tac >>
    drule_all joined_value_bounded >> simp[]) >>
  (* instrs bounded *)
  `(∀inst. MEM inst instrs ==> ∀v. MEM v (inst_uses inst) ==> MEM v U) ∧
   (∀inst. MEM inst instrs ==> ∀v. MEM v (inst_defs inst) ==> MEM v U)` by (
    simp[Abbr`instrs`] >> rpt strip_tac >>
    Cases_on `lookup_block lbl bbs` >> fs[] >>
    imp_res_tac lookup_block_mem >> metis_tac[]) >>
  (* fold result bounded - avoid by block, use mp_tac at top level *)
  qspecl_then [`dir`,`bbs`,`lbl`,`instrs`,`joined`,
               `fold_result0`,`fold_result1`,`U`]
    mp_tac fold_block_bounded >>
  impl_tac
  >- (rpt conj_tac >> first_x_assum ACCEPT_TAC)
  >> strip_tac >>
  (* Boundary case *)
  rpt conj_tac >> rpt strip_tac
  >- (Cases_on `l = lbl` >> fs[FLOOKUP_UPDATE]
      >- (qpat_x_assum `list_union _ _ = _` (SUBST_ALL_TAC o SYM) >>
          fs[list_union_mem, df_boundary_def] >>
          Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[] >> res_tac)
      >- res_tac)
  >- (fs[FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP fold_result1 l` >> fs[] >> metis_tac[])
QED

(* ===== Convergence + Boundedness infrastructure ===== *)

(* Invariant: all values bounded by fn_all_vars *)
Definition liveness_bounded_def:
  liveness_bounded bbs (st : string list df_state) <=>
    (∀l v. FLOOKUP st.ds_boundary l = SOME v ==>
           ∀x. MEM x v ==> MEM x (fn_all_vars bbs)) ∧
    (∀l v. FLOOKUP st.ds_inst l = SOME v ==>
           ∀x. MEM x v ==> MEM x (fn_all_vars bbs))
End

(* Compute block instructions for a label *)
Definition block_instrs_def:
  block_instrs lbl bbs =
    case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions
End

Theorem block_instrs_some[local]:
  ∀lbl bbs bb. lookup_block lbl bbs = SOME bb ==>
    block_instrs lbl bbs = bb.bb_instructions
Proof
  simp_tac std_ss [block_instrs_def]
QED

Theorem block_instrs_none[local]:
  ∀lbl bbs. lookup_block lbl bbs = NONE ==>
    block_instrs lbl bbs = []
Proof
  simp_tac std_ss [block_instrs_def]
QED

Theorem not_fn_labels_lookup_none[local]:
  ∀lbl bbs. ¬MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs = NONE
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  metis_tac[lookup_block_def]
QED

(* Compute the joined value for a label from current state (backward: successors) *)
Definition liveness_joined_def:
  liveness_joined fn st lbl =
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let edge_vals = MAP (\nbr. liveness_edge_transfer bbs nbr lbl
                           (df_boundary [] st nbr))
                        (cfg_succs_of cfg lbl) in
    case edge_vals of
      [] => []
    | v4::v5 => FOLDL list_union [] edge_vals
End

(* Canonical fold value: what fold(joined) would give at key (lbl, j) *)
Definition liveness_canonical_inst_def:
  liveness_canonical_inst fn st (lbl, j) =
    let bbs = fn.fn_blocks in
    let joined = liveness_joined fn st lbl in
    let (fv, im) = df_fold_block Backward
          (liveness_transfer bbs) lbl (block_instrs lbl bbs) joined in
    FLOOKUP im (lbl, j)
End

(* Count of canonical inst keys *)
Definition liveness_canonical_count_def:
  liveness_canonical_count fn (st : string list df_state) =
    CARD { k | k IN FDOM st.ds_inst /\
               FLOOKUP st.ds_inst k = liveness_canonical_inst fn st k }
End

(* Upper bound on inst keys *)
Definition liveness_inst_key_bound_def:
  liveness_inst_key_bound fn =
    df_total_inst_slots fn.fn_blocks +
    LENGTH ((cfg_analyze fn).cfg_dfs_post)
End

(* Boundary card sum *)
Definition liveness_boundary_sum_def:
  liveness_boundary_sum fn (st : string list df_state) =
    SUM (MAP (\lbl. CARD (set (df_boundary [] st lbl))) (fn_labels fn))
End

(* Unified state invariant for convergence *)
Definition liveness_state_inv_def:
  liveness_state_inv fn (st : string list df_state) <=>
    liveness_bounded fn.fn_blocks st ∧
    FDOM st.ds_inst SUBSET
      df_valid_inst_keys fn.fn_blocks UNION
      (set ((cfg_analyze fn).cfg_dfs_post) CROSS {0n}) ∧
    (* structural: all lbl-keys imply (lbl,0) exists *)
    (∀lbl j. (lbl, j) IN FDOM st.ds_inst ==> (lbl, 0n) IN FDOM st.ds_inst) ∧
    (* structural: inst implies boundary *)
    (∀lbl. (lbl, 0n) IN FDOM st.ds_inst ==> lbl IN FDOM st.ds_boundary) ∧
    (* fold match: stored values equal fold from stored init *)
    (∀lbl v_init.
       FLOOKUP st.ds_inst (lbl, LENGTH (block_instrs lbl fn.fn_blocks)) =
         SOME v_init ==>
       ∀k v. FLOOKUP (SND (df_fold_block Backward
                (liveness_transfer fn.fn_blocks) lbl
                (block_instrs lbl fn.fn_blocks) v_init)) k = SOME v ==>
             FLOOKUP st.ds_inst k = SOME v) ∧
    (* entry subset: stored init ⊆ current joined *)
    (∀lbl v_init.
       FLOOKUP st.ds_inst (lbl, LENGTH (block_instrs lbl fn.fn_blocks)) =
         SOME v_init ==>
       set v_init SUBSET set (liveness_joined fn st lbl))
End

(* Combined measure: boundary sum scaled by (K+1) + canonical count.
   Case A (boundary grows): first term grows by ≥K+1, canonical count
     decreases by at most K. Net increase ≥1.
   Case C (boundary same, inst values change): first term unchanged,
     canonical count increases by ≥1 (processed label's keys become canonical).
   This ensures strict increase when process ≠ st, without requiring
   set-level changes for inst values. *)
Definition liveness_measure_def:
  liveness_measure fn (st : string list df_state) =
    liveness_boundary_sum fn st * (liveness_inst_key_bound fn + 1) +
    liveness_canonical_count fn st
End

(* ---- Helper lemmas ---- *)

(* Transfer is set-monotone *)
Theorem liveness_transfer_mono[local]:
  ∀bbs inst a b.
    set a SUBSET set b ==>
    set (liveness_transfer bbs inst a) SUBSET set (liveness_transfer bbs inst b)
Proof
  rw[liveness_transfer_def, live_update_def,
     LIST_TO_SET_APPEND, LIST_TO_SET_FILTER, SUBSET_DEF] >>
  metis_tac[]
QED

(* Invariant preserved by process *)
Theorem liveness_bounded_preserved[local]:
  ∀fn lbl st.
    liveness_bounded fn.fn_blocks st ==>
    liveness_bounded fn.fn_blocks
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >> fs[liveness_bounded_def] >>
  qspecl_then [`fn.fn_blocks`, `Backward`, `cfg_analyze fn`, `NONE`,
               `lbl`, `st`, `fn_all_vars fn.fn_blocks`]
    mp_tac df_process_bounded >>
  impl_tac >> simp[] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- (rpt strip_tac >> irule fn_all_vars_mem >> metis_tac[])
  >- (rpt strip_tac >> irule fn_all_vars_mem >> metis_tac[])
QED

(* Boundary unchanged for l ≠ lbl *)
(* For labels other than the processed one, inst lookups are unchanged *)
Theorem process_inst_other[local]:
  ∀dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st lbl' j.
    lbl' <> lbl ==>
    FLOOKUP
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbl st).ds_inst (lbl', j) =
    FLOOKUP st.ds_inst (lbl', j)
Proof
  rw[df_process_block_def, LET_THM] >>
  pairarg_tac >> rw[FLOOKUP_FUNION] >>
  `(lbl', j) NOTIN FDOM inst_map` suffices_by
    (strip_tac >> simp[FLOOKUP_DEF]) >>
  strip_tac >> Cases_on `dir`
  >- (drule dfAnalyzeProofsTheory.df_fold_block_fdom >>
      strip_tac >> fs[IN_IMAGE, IN_COUNT])
  >- (drule dfAnalyzeProofsTheory.df_fold_block_fdom_backward >>
      strip_tac >> fs[IN_IMAGE, IN_COUNT])
QED

(* For labels other than the processed one, FDOM membership is unchanged *)
Theorem process_fdom_other[local]:
  ∀dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st lbl' j.
    lbl' <> lbl ==>
    ((lbl', j) IN FDOM
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbl st).ds_inst <=>
     (lbl', j) IN FDOM st.ds_inst)
Proof
  rpt strip_tac >>
  rw[TO_FLOOKUP, process_inst_other]
QED

Theorem process_boundary_other[local]:
  ∀dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st l.
    l <> lbl ==>
    df_boundary bottom
      (df_process_block dir bottom join transfer edge_transfer
                        ctx entry_val cfg bbs lbl st) l =
    df_boundary bottom st l
Proof
  rw[df_process_block_def, df_boundary_def, LET_THM] >>
  pairarg_tac >> rw[FLOOKUP_UPDATE]
QED

(* Backward fold stores initial value at (lbl, LENGTH instrs) *)
Theorem fold_block_init_value_backward[local]:
  ∀transfer lbl instrs init_val fv im.
    df_fold_block Backward transfer lbl instrs init_val = (fv, im) ==>
    FLOOKUP im (lbl, LENGTH instrs) = SOME init_val
Proof
  rw[df_fold_block_def] >>
  drule dfAnalyzeProofsTheory.df_fold_backward_at >> simp[]
QED

(* Rewrite df_process_block to canonical form for liveness *)
Theorem liveness_process_eq[local]:
  ∀fn lbl st.
    df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = block_instrs lbl fn.fn_blocks in
    let joined = liveness_joined fn st lbl in
    let (fv, inst_map) = df_fold_block Backward
          (liveness_transfer fn.fn_blocks) lbl instrs joined in
      st with <|ds_boundary := st.ds_boundary |+
                  (lbl, list_union (df_boundary [] st lbl) fv);
                ds_inst := FUNION inst_map st.ds_inst|>
Proof
  rw[df_process_block_def, df_joined_val_def] >>
  simp_tac std_ss [LET_THM, direction_case_def] >>
  rw[block_instrs_def] >>
  simp[liveness_joined_def, LET_THM]
QED

val input_vars_from_let =
  SIMP_RULE std_ss [LET_THM] input_vars_from_def;

(* Helper: accumulator elements persist through the FOLDL *)
Theorem foldl_acc_persists[local]:
  ∀base acc placed op_map matching v.
    MEM v acc ==>
    MEM v (FST (FOLDL (λ(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base))
Proof
  Induct >> rw[] >>
  Cases_on `FLOOKUP op_map h` >> simp[] >>
  Cases_on `MEM x placed` >> simp[] >>
  Cases_on `FLOOKUP matching x` >> simp[]
QED

(* Tight upper bound: FOLDL result elements come from acc, passthrough, or replacement *)
Theorem foldl_mem_tight[local]:
  ∀base acc placed op_map matching v.
    MEM v (FST (FOLDL (λ(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) ==>
    MEM v acc ∨
    (MEM v base ∧ FLOOKUP op_map v = NONE) ∨
    (∃idx w. MEM w base ∧ FLOOKUP op_map w = SOME idx ∧
             FLOOKUP matching idx = SOME v)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[MEM_APPEND] >> metis_tac[])
  >- (Cases_on `MEM x placed` >> simp[]
      >- (strip_tac >> first_x_assum drule >> strip_tac >>
          gvs[] >> metis_tac[MEM])
      >- (Cases_on `FLOOKUP matching x` >> simp[]
          >- (strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[] >> metis_tac[MEM])
          >- (strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[MEM_APPEND] >> metis_tac[MEM])))
QED

(* Lower bound: passthrough elements survive *)
Theorem foldl_passthrough[local]:
  ∀base acc placed op_map matching w.
    MEM w base ∧ FLOOKUP op_map w = NONE ==>
    MEM w (FST (FOLDL (λ(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (irule foldl_acc_persists >> simp[])
  >- (
    qmatch_goalsub_abbrev_tac `FOLDL _ init _` >>
    first_x_assum (qspecl_then [`FST init`, `SND init`,
      `op_map`, `matching`, `w`] mp_tac) >>
    simp[Abbr`init`, PAIR])
QED

(* Lower bound: replacement elements appear (or idx already placed) *)
Theorem foldl_replacement[local]:
  ∀base acc placed op_map matching idx src_v.
    (∃w. MEM w base ∧ FLOOKUP op_map w = SOME idx) ∧
    FLOOKUP matching idx = SOME src_v ==>
    MEM src_v (FST (FOLDL (λ(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) ∨ MEM idx placed
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- ((* w = h: op_map h = SOME idx *)
      Cases_on `MEM idx placed` >> simp[] >>
      irule foldl_acc_persists >> simp[])
  >- ((* MEM w base': abbreviate init, use IH via FST/SND *)
      qmatch_goalsub_abbrev_tac `FOLDL _ init _` >>
      first_x_assum (qspecl_then [`FST init`, `SND init`,
        `op_map`, `matching`, `idx`, `src_v`] mp_tac) >>
      simp[PAIR] >>
      impl_tac >- (simp[Abbr`init`] >> metis_tac[]) >>
      strip_tac >> gvs[] >>
      (* Right disjunct case: idx ∈ SND init *)
      simp[Abbr`init`] >>
      Cases_on `FLOOKUP op_map h` >> gvs[] >>
      Cases_on `MEM x placed` >> gvs[] >>
      Cases_on `FLOOKUP matching x` >> gvs[IN_INSERT] >>
      irule foldl_acc_persists >> simp[])
QED

(* input_vars_from is monotone in base *)
Theorem input_vars_from_mono[local]:
  ∀instrs lbl a b.
    set a SUBSET set b ==>
    set (input_vars_from lbl instrs a) SUBSET
    set (input_vars_from lbl instrs b)
Proof
  rpt gen_tac >> simp[input_vars_from_def, LET_THM] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps lbl (collect_phis instrs)` >>
  rename1 `_ = (op_map, matching)` >> simp[] >>
  simp[Ntimes UNCURRY 2] >>
  strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
  drule foldl_mem_tight >> strip_tac >> gvs[]
  >- ((* passthrough: v ∈ a, op_map v = NONE → v passes through in b too *)
      irule foldl_passthrough >> metis_tac[SUBSET_DEF])
  >- ((* replacement: ∃idx w. w ∈ a, op_map w = SOME idx, matching idx = SOME v *)
      `MEM w b` by metis_tac[SUBSET_DEF] >>
      qspecl_then [`b`, `[]`, `[]`, `op_map`, `matching`, `idx`, `x`]
        mp_tac foldl_replacement >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      simp[])
QED

(* edge_transfer is set-monotone *)
Theorem liveness_edge_transfer_mono[local]:
  ∀bbs succ lbl a b.
    set a SUBSET set b ==>
    set (liveness_edge_transfer bbs succ lbl a) SUBSET
    set (liveness_edge_transfer bbs succ lbl b)
Proof
  rw[liveness_edge_transfer_def] >>
  Cases_on `lookup_block succ bbs` >> simp[SUBSET_REFL] >>
  irule input_vars_from_mono >> simp[]
QED

(* FOLDL list_union is set-monotone pointwise *)
Theorem foldl_list_union_mono[local]:
  ∀xs ys a b.
    LENGTH xs = LENGTH ys /\
    set a SUBSET set b /\
    (∀i. i < LENGTH xs ==> set (EL i xs) SUBSET set (EL i ys)) ==>
    set (FOLDL list_union a xs) SUBSET set (FOLDL list_union b ys)
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  Cases_on `ys` >> fs[] >>
  first_x_assum irule >>
  `set h SUBSET set h'` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
  >- simp[]
  >- (simp[list_union_set, SUBSET_DEF] >> metis_tac[SUBSET_DEF])
QED

(* joined is monotone: when all boundaries grow, joined grows *)
Theorem liveness_joined_mono[local]:
  ∀fn st1 st2 lbl.
    (∀l. set (df_boundary [] st1 l) SUBSET set (df_boundary [] st2 l)) ==>
    set (liveness_joined fn st1 lbl) SUBSET set (liveness_joined fn st2 lbl)
Proof
  rw[liveness_joined_def, LET_THM] >>
  Cases_on `cfg_succs_of (cfg_analyze fn) lbl` >> simp[] >>
  irule foldl_list_union_mono >> rpt conj_tac >> simp[EL_MAP] >>
  rpt strip_tac >> simp[list_union_set, SUBSET_DEF] >>
  metis_tac[liveness_edge_transfer_mono, SUBSET_DEF]
QED

(* SUM_MAP_LE alias *)
val SUM_MAP_LE = dfHelperProofsTheory.sum_map_mono_proof;
val SUM_MAP_STRICT = dfHelperProofsTheory.sum_map_strict_increase_proof;

Theorem SUM_MAP_K[local]:
  ∀c (ls:'a list). SUM (MAP (K c) ls) = LENGTH ls * c
Proof
  Induct_on `ls` >> simp[arithmeticTheory.MULT_CLAUSES]
QED

(* three_sum_strict: at least one strict among three ≤ components *)
Theorem three_sum_strict[local]:
  !(a1:num) b1 c1 a2 b2 c2.
    a1 <= a2 /\ b1 <= b2 /\ c1 <= c2 /\
    (a1 < a2 \/ b1 < b2 \/ c1 < c2) ==>
    a1 + b1 + c1 < a2 + b2 + c2
Proof
  DECIDE_TAC
QED

(* Nonlinear arithmetic helper for measure increase *)
Theorem mult_le_helper[local]:
  !(a:num) b c. a <= b ==> a * c <= b * c
Proof
  metis_tac[LESS_MONO_MULT]
QED

Theorem weighted_sum_strict[local]:
  !(a:num) b c d.
    a < b /\ c <= d ==> a * (d + 1) + c < b * (d + 1)
Proof
  rpt gen_tac >> strip_tac >>
  irule LESS_LESS_EQ_TRANS >>
  qexists_tac `(a + 1) * (d + 1)` >>
  conj_tac
  >- (simp_tac std_ss [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB,
                        MULT_LEFT_1, MULT_RIGHT_1] >>
      DECIDE_TAC)
  >- (irule_at Any mult_le_helper >> DECIDE_TAC)
QED

(* Initial state satisfies invariant *)
Theorem liveness_state_inv_init[local]:
  ∀fn. liveness_state_inv fn (init_df_state [] (MAP (\bb. bb.bb_label) fn.fn_blocks))
Proof
  rw[liveness_state_inv_def, liveness_bounded_def, init_df_state_def,
     FDOM_FEMPTY, EMPTY_SUBSET] >>
  imp_res_tac dfAnalyzeProofsTheory.foldl_fempty_val >> gvs[]
QED

(* --- Helpers for liveness_state_inv_preserved --- *)

(* Process FDOM characterization: fold keys have FST = lbl and j ∈ count *)
Theorem process_fdom_lbl[local]:
  ∀fn lbl st j.
    (lbl, j) IN FDOM (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst ==>
    j <= LENGTH (block_instrs lbl fn.fn_blocks) ∨
    (lbl, j) IN FDOM st.ds_inst
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
    (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
  pairarg_tac >> gvs[FDOM_FUNION] >>
  drule dfAnalyzeProofsTheory.df_fold_block_fdom_backward >>
  strip_tac >> gvs[IN_IMAGE, IN_COUNT]
QED

(* Helper: fold key in valid set when MEM lbl *)
Theorem fold_key_in_valid[local]:
  ∀fn lbl j.
    (MEM lbl (fn_labels fn) ∨ MEM lbl (cfg_analyze fn).cfg_dfs_post) ==>
    j <= LENGTH (block_instrs lbl fn.fn_blocks) ==>
    (lbl, j) IN df_valid_inst_keys fn.fn_blocks ∪
    set (cfg_analyze fn).cfg_dfs_post × {0n}
Proof
  rpt gen_tac >> strip_tac >> strip_tac
  >- ((* MEM lbl (fn_labels fn) case *)
      `MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
        metis_tac[fn_labels_def] >>
      imp_res_tac fn_labels_lookup_block >>
      rename1 `lookup_block lbl _ = SOME bb` >>
      imp_res_tac lookup_block_mem >> imp_res_tac lookup_block_label >>
      imp_res_tac block_instrs_some >>
      `j <= LENGTH bb.bb_instructions` by metis_tac[] >>
      simp[IN_UNION, dfAnalyzeProofsTheory.df_valid_inst_keys_def,
           IN_BIGUNION, MEM_MAP] >>
      disj1_tac >>
      qexists_tac `IMAGE (\i. (bb.bb_label, i))
        (count (LENGTH bb.bb_instructions + 1))` >>
      simp[IN_IMAGE, IN_COUNT] >>
      qexists_tac `bb` >> simp[])
  >- ((* MEM lbl cfg_dfs_post case *)
      Cases_on `MEM lbl (fn_labels fn)`
      >- ((* also in fn_labels — use first branch logic *)
          `MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
            metis_tac[fn_labels_def] >>
          imp_res_tac fn_labels_lookup_block >>
          rename1 `lookup_block lbl _ = SOME bb` >>
          imp_res_tac lookup_block_mem >> imp_res_tac lookup_block_label >>
          imp_res_tac block_instrs_some >>
          `j <= LENGTH bb.bb_instructions` by metis_tac[] >>
          simp[IN_UNION, dfAnalyzeProofsTheory.df_valid_inst_keys_def,
               IN_BIGUNION, MEM_MAP] >>
          disj1_tac >>
          qexists_tac `IMAGE (\i. (bb.bb_label, i))
            (count (LENGTH bb.bb_instructions + 1))` >>
          simp[IN_IMAGE, IN_COUNT] >>
          qexists_tac `bb` >> simp[])
      >- ((* not in fn_labels *)
          `lookup_block lbl fn.fn_blocks = NONE` by
            metis_tac[not_fn_labels_lookup_none, fn_labels_def] >>
          imp_res_tac block_instrs_none >>
          gvs[] >>
          simp[IN_UNION, IN_CROSS, IN_INSERT]))
QED

(* Extract FDOM subset from invariant — avoids expanding liveness_state_inv_def *)
Theorem inv_fdom_subset[local]:
  ∀fn st. liveness_state_inv fn st ==>
    FDOM st.ds_inst ⊆
    df_valid_inst_keys fn.fn_blocks ∪
    set (cfg_analyze fn).cfg_dfs_post × {0n}
Proof
  rpt strip_tac >>
  pop_assum (strip_assume_tac o REWRITE_RULE [liveness_state_inv_def])
QED

(* Element-level FDOM subset from invariant *)
Theorem inv_fdom_subset_elem[local]:
  ∀fn st lbl j. liveness_state_inv fn st ⇒ (lbl,j) ∈ FDOM st.ds_inst ⇒
    (lbl,j) ∈ df_valid_inst_keys fn.fn_blocks ∪
    set (cfg_analyze fn).cfg_dfs_post × {0n}
Proof
  rpt strip_tac >> imp_res_tac inv_fdom_subset >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

(* C2: FDOM subset preserved *)
Theorem inv_fdom_subset_preserved[local]:
  ∀fn lbl st.
    liveness_state_inv fn st ==>
    (MEM lbl (fn_labels fn) ∨ MEM lbl (cfg_analyze fn).cfg_dfs_post) ==>
    FDOM (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst ⊆
    df_valid_inst_keys fn.fn_blocks ∪
    set (cfg_analyze fn).cfg_dfs_post × {0n}
Proof
  rpt gen_tac >> strip_tac >> disch_tac >>
  simp[pred_setTheory.SUBSET_DEF] >>
  Cases >> disch_tac >> rename1 `(lbl', j)` >> simp[] >>
  Cases_on `lbl' = lbl`
  >- (qpat_x_assum `lbl' = lbl` SUBST_ALL_TAC >>
      drule process_fdom_lbl >> strip_tac
      >- (drule_all fold_key_in_valid >>
          simp[IN_UNION, IN_CROSS, IN_INSERT])
      >- (drule_all inv_fdom_subset_elem >>
          simp[IN_UNION, IN_CROSS, IN_INSERT]))
  >- (`(lbl', j) IN FDOM st.ds_inst` by metis_tac[process_fdom_other] >>
      drule_all inv_fdom_subset_elem >>
      simp[IN_UNION, IN_CROSS, IN_INSERT])
QED

(* C3: j→0 preserved *)
Theorem inv_j_to_zero_preserved[local]:
  ∀fn lbl st lbl' j.
    liveness_state_inv fn st ∧
    (lbl', j) IN FDOM (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst ==>
    (lbl', 0) IN FDOM (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst
Proof
  rpt strip_tac >>
  Cases_on `lbl' = lbl`
  >- (qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
        (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
      pairarg_tac >> gvs[FDOM_FUNION] >>
      drule dfAnalyzeProofsTheory.df_fold_block_fdom_backward >>
      strip_tac >> simp[IN_IMAGE, IN_COUNT])
  >- (`(lbl', j) IN FDOM st.ds_inst` by metis_tac[process_fdom_other] >>
      `(lbl', 0) IN FDOM st.ds_inst` by
        (fs[liveness_state_inv_def] >> metis_tac[]) >>
      metis_tac[process_fdom_other])
QED

(* C4: 0→boundary preserved *)
Theorem inv_zero_to_boundary_preserved[local]:
  ∀fn lbl st lbl'.
    liveness_state_inv fn st ∧
    (lbl', 0) IN FDOM (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst ==>
    lbl' IN FDOM (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_boundary
Proof
  rpt strip_tac >>
  Cases_on `lbl' = lbl`
  >- (qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
        (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
      pairarg_tac >> gvs[FDOM_FUPDATE])
  >- (`(lbl', 0) IN FDOM st.ds_inst` by metis_tac[process_fdom_other] >>
      `lbl' IN FDOM st.ds_boundary` by
        (fs[liveness_state_inv_def] >> metis_tac[]) >>
      qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
        (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
      pairarg_tac >> gvs[FDOM_FUPDATE])
QED

(* C5: fold match preserved *)
Theorem inv_fold_match_preserved[local]:
  ∀fn lbl st lbl' v_init k v.
    liveness_state_inv fn st ∧
    FLOOKUP (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst
      (lbl', LENGTH (block_instrs lbl' fn.fn_blocks)) = SOME v_init ∧
    FLOOKUP (SND (df_fold_block Backward
      (liveness_transfer fn.fn_blocks) lbl'
      (block_instrs lbl' fn.fn_blocks) v_init)) k = SOME v ==>
    FLOOKUP (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst k = SOME v
Proof
  rpt strip_tac >>
  Cases_on `lbl' = lbl`
  >- ((* lbl' = lbl: process inst = FUNION inst_map st.ds_inst
        where inst_map = SND of the same fold *)
      qpat_x_assum `lbl' = lbl` SUBST_ALL_TAC >>
      qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
        (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
      pairarg_tac >> gvs[] >>
      (* inst_map has init value at (lbl, LENGTH instrs) *)
      drule fold_block_init_value_backward >> strip_tac >>
      (* FUNION prefers inst_map, so v_init = liveness_joined *)
      `v_init = liveness_joined fn st lbl` by
        fs[FLOOKUP_FUNION] >>
      gvs[] >>
      (* fold with same args = (fv, inst_map), so FLOOKUP inst_map k = SOME v *)
      `FLOOKUP inst_map k = SOME v` by fs[] >>
      simp[FLOOKUP_FUNION])
  >- ((* lbl' ≠ lbl: FLOOKUP process = FLOOKUP st by process_inst_other *)
      (* v_init from process = v_init from st *)
      `FLOOKUP st.ds_inst
        (lbl', LENGTH (block_instrs lbl' fn.fn_blocks)) = SOME v_init` by
        metis_tac[process_inst_other] >>
      (* Old invariant C5: fold results from v_init are in st.ds_inst *)
      qpat_x_assum `liveness_state_inv fn st`
        (strip_assume_tac o REWRITE_RULE [liveness_state_inv_def]) >>
      `FLOOKUP st.ds_inst k = SOME v` by metis_tac[] >>
      (* k has FST = lbl' (from fold FDOM), so FST k ≠ lbl *)
      Cases_on `k` >> rename1 `FLOOKUP st.ds_inst (k1, k2) = SOME v` >>
      `(k1, k2) ∈ FDOM (SND (df_fold_block Backward
        (liveness_transfer fn.fn_blocks) lbl'
        (block_instrs lbl' fn.fn_blocks) v_init))` by
        (fs[flookup_thm]) >>
      Cases_on `df_fold_block Backward
        (liveness_transfer fn.fn_blocks) lbl'
        (block_instrs lbl' fn.fn_blocks) v_init` >>
      fs[] >>
      drule dfAnalyzeProofsTheory.df_fold_block_fdom_backward >> strip_tac >>
      `k1 = lbl'` by (gvs[IN_IMAGE, IN_COUNT] >> fs[]) >>
      gvs[] >>
      metis_tac[process_inst_other])
QED

(* All boundaries monotone under process *)
Theorem boundary_mono_process[local]:
  ∀fn lbl st l.
    set (df_boundary [] st l) ⊆
    set (df_boundary []
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st) l)
Proof
  rpt gen_tac >>
  Cases_on `l = lbl`
  >- (qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
        (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
      pairarg_tac >> gvs[df_boundary_def, FLOOKUP_UPDATE] >>
      simp[list_union_set, SUBSET_UNION])
  >- simp[process_boundary_other]
QED

(* liveness_joined monotone under process *)
Theorem liveness_joined_process_mono[local]:
  ∀fn lbl st lbl'.
    set (liveness_joined fn st lbl') ⊆
    set (liveness_joined fn
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st) lbl')
Proof
  rpt gen_tac >> irule liveness_joined_mono >>
  simp[boundary_mono_process]
QED

(* C6: entry subset preserved *)
Theorem inv_entry_subset_preserved[local]:
  ∀fn lbl st lbl' v_init.
    liveness_state_inv fn st ∧
    FLOOKUP (df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st).ds_inst
      (lbl', LENGTH (block_instrs lbl' fn.fn_blocks)) = SOME v_init ==>
    set v_init ⊆ set (liveness_joined fn
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st) lbl')
Proof
  rpt strip_tac >>
  Cases_on `lbl' = lbl`
  >- ((* lbl' = lbl: v_init = liveness_joined fn st lbl *)
      qpat_x_assum `lbl' = lbl` SUBST_ALL_TAC >>
      (* Show v_init = liveness_joined fn st lbl *)
      `v_init = liveness_joined fn st lbl` by (
        qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
          (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
        pairarg_tac >> gvs[] >>
        drule fold_block_init_value_backward >> strip_tac >>
        fs[FLOOKUP_FUNION]) >>
      gvs[] >> metis_tac[liveness_joined_process_mono])
  >- ((* lbl' ≠ lbl: v_init from old state, chain with joined_process_mono *)
      `FLOOKUP st.ds_inst
        (lbl', LENGTH (block_instrs lbl' fn.fn_blocks)) = SOME v_init` by
        metis_tac[process_inst_other] >>
      qpat_x_assum `liveness_state_inv fn st`
        (strip_assume_tac o REWRITE_RULE [liveness_state_inv_def]) >>
      `set v_init ⊆ set (liveness_joined fn st lbl')` by metis_tac[] >>
      irule SUBSET_TRANS >>
      qexists_tac `set (liveness_joined fn st lbl')` >>
      simp[liveness_joined_process_mono])
QED

(* State invariant preserved — the main work *)
Theorem liveness_state_inv_preserved[local]:
  ∀fn lbl st.
    (MEM lbl (fn_labels fn) ∨ MEM lbl (cfg_analyze fn).cfg_dfs_post) ∧
    liveness_state_inv fn st ==>
    liveness_state_inv fn
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt gen_tac >> disch_tac >>
  `liveness_state_inv fn st` by metis_tac[] >>
  PURE_REWRITE_TAC [liveness_state_inv_def] >> rpt conj_tac
  >- (irule liveness_bounded_preserved >>
      pop_assum (fn th =>
        ACCEPT_TAC (CONJUNCT1 (REWRITE_RULE [liveness_state_inv_def] th))))
  >- metis_tac[inv_fdom_subset_preserved]
  >- metis_tac[inv_j_to_zero_preserved]
  >- metis_tac[inv_zero_to_boundary_preserved]
  >- metis_tac[inv_fold_match_preserved]
  >- metis_tac[inv_entry_subset_preserved]
QED

(* --- Canonical count helpers --- *)

(* The canonical set is finite *)
Theorem canonical_set_finite[local]:
  ∀fn (st : string list df_state).
    FINITE { k | k IN FDOM st.ds_inst ∧
                 FLOOKUP st.ds_inst k = liveness_canonical_inst fn st k }
Proof
  rw[] >> irule pred_setTheory.SUBSET_FINITE >>
  qexists_tac `FDOM st.ds_inst` >> rw[pred_setTheory.SUBSET_DEF]
QED

(* Canonical count ≤ CARD(FDOM inst) *)
Theorem canonical_count_le_fdom[local]:
  ∀fn (st : string list df_state).
    liveness_canonical_count fn st <= CARD (FDOM st.ds_inst)
Proof
  rw[liveness_canonical_count_def] >>
  irule pred_setTheory.CARD_SUBSET >> rw[canonical_set_finite] >>
  rw[pred_setTheory.SUBSET_DEF]
QED

(* Canonical count bounded by inst key bound *)
Theorem canonical_count_bounded[local]:
  ∀fn st.
    liveness_state_inv fn st ==>
    liveness_canonical_count fn st <= liveness_inst_key_bound fn
Proof
  rw[] >>
  irule LESS_EQ_TRANS >>
  qexists_tac `CARD (FDOM st.ds_inst)` >>
  conj_tac >- simp[canonical_count_le_fdom] >>
  fs[liveness_state_inv_def, liveness_inst_key_bound_def] >>
  irule LESS_EQ_TRANS >>
  qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks UNION
    (set (cfg_analyze fn).cfg_dfs_post CROSS {0n}))` >>
  conj_tac
  >- (irule pred_setTheory.CARD_SUBSET >>
      rw[pred_setTheory.FINITE_UNION, dfAnalyzeProofsTheory.df_valid_inst_keys_finite,
         pred_setTheory.FINITE_CROSS])
  >- (irule LESS_EQ_TRANS >>
      qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks) +
                   CARD (set (cfg_analyze fn).cfg_dfs_post CROSS {0n})` >>
      conj_tac
      >- (irule pred_setTheory.CARD_UNION_LE >>
          rw[dfAnalyzeProofsTheory.df_valid_inst_keys_finite,
             pred_setTheory.FINITE_CROSS])
      >- (`CARD (df_valid_inst_keys fn.fn_blocks) <=
            df_total_inst_slots fn.fn_blocks` by
            simp[dfAnalyzeProofsTheory.df_valid_inst_keys_card] >>
          `CARD (set (cfg_analyze fn).cfg_dfs_post CROSS {0n}) <=
            LENGTH (cfg_analyze fn).cfg_dfs_post` by
            (simp[pred_setTheory.CARD_CROSS, pred_setTheory.CARD_SING] >>
             simp[listTheory.CARD_LIST_TO_SET]) >>
          DECIDE_TAC))
QED

(* Boundary sum bounded *)
Theorem boundary_sum_bounded[local]:
  ∀fn st.
    liveness_state_inv fn st ==>
    liveness_boundary_sum fn st <=
    LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks))
Proof
  rw[liveness_boundary_sum_def, liveness_state_inv_def, liveness_bounded_def] >>
  irule LESS_EQ_TRANS >>
  qexists_tac `SUM (MAP (K (CARD (set (fn_all_vars fn.fn_blocks)))) (fn_labels fn))` >>
  conj_tac
  >- (irule dfHelperProofsTheory.sum_map_mono_proof >>
      rw[listTheory.EVERY_MEM] >> rename1 `MEM lbl (fn_labels fn)` >>
      irule pred_setTheory.CARD_SUBSET >>
      rw[listTheory.FINITE_LIST_TO_SET] >>
      rw[pred_setTheory.SUBSET_DEF, df_boundary_def] >>
      rpt strip_tac >>
      Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[] >> metis_tac[])
  >- simp[SUM_MAP_K]
QED

(* Measure bounded *)
Theorem liveness_measure_bounded[local]:
  ∀fn st.
    liveness_state_inv fn st ==>
    liveness_measure fn st <=
    LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks)) *
      (liveness_inst_key_bound fn + 1) +
    liveness_inst_key_bound fn
Proof
  rw[liveness_measure_def] >>
  `liveness_boundary_sum fn st <=
   LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks))` by
    metis_tac[boundary_sum_bounded] >>
  `liveness_canonical_count fn st <= liveness_inst_key_bound fn` by
    metis_tac[canonical_count_bounded] >>
  `(liveness_inst_key_bound fn + 1) * liveness_boundary_sum fn st <=
   (liveness_inst_key_bound fn + 1) *
   (LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks)))` by
    simp[] >>
  DECIDE_TAC
QED

(* --- Boundary changes when list_union differs --- *)
Theorem boundary_sum_increases[local]:
  ∀fn lbl st new_b.
    MEM lbl (fn_labels fn) ∧
    new_b = list_union (df_boundary [] st lbl) fv ∧
    new_b <> df_boundary [] st lbl ==>
    liveness_boundary_sum fn (st with ds_boundary := st.ds_boundary |+ (lbl, new_b)) >
    liveness_boundary_sum fn st
Proof
  rw[liveness_boundary_sum_def, GREATER_DEF] >>
  irule dfHelperProofsTheory.sum_map_strict_increase_proof >>
  conj_tac
  >- (rw[EVERY_MEM] >> rename1 `MEM l (fn_labels fn)` >>
      Cases_on `l = lbl` >> simp[df_boundary_def, FLOOKUP_UPDATE] >>
      irule pred_setTheory.CARD_SUBSET >>
      simp[listTheory.FINITE_LIST_TO_SET, list_union_set,
           pred_setTheory.SUBSET_UNION])
  >- (qexists_tac `lbl` >>
      simp[df_boundary_def, FLOOKUP_UPDATE] >>
      simp[GSYM df_boundary_def] >>
      imp_res_tac list_union_neq_card >> fs[])
QED

(* Boundary sum is monotone under process *)
Theorem boundary_sum_process_mono[local]:
  ∀fn lbl st.
    liveness_boundary_sum fn st <=
    liveness_boundary_sum fn
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt gen_tac >>
  qspecl_then [`fn`, `lbl`, `st`] mp_tac liveness_process_eq >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  simp[liveness_boundary_sum_def] >>
  irule dfHelperProofsTheory.sum_map_mono_proof >>
  rw[EVERY_MEM] >> rename1 `MEM l (fn_labels fn)` >>
  Cases_on `l = lbl`
  >- (simp[df_boundary_def, FLOOKUP_UPDATE] >>
      irule pred_setTheory.CARD_SUBSET >>
      simp[listTheory.FINITE_LIST_TO_SET, list_union_set,
           pred_setTheory.SUBSET_UNION])
  >- simp[df_boundary_def, FLOOKUP_UPDATE]
QED

(* --- Helpers for canonical count case C --- *)

(* list_union is identity when rhs set is contained *)
Theorem list_union_identity[local]:
  ∀a b. set b ⊆ set a ⇒ list_union a b = a
Proof
  rw[list_union_def] >>
  `FILTER (λv. ¬MEM v a) b = []` suffices_by simp[] >>
  rw[FILTER_EQ_NIL, EVERY_MEM] >> fs[SUBSET_DEF]
QED

(* Component-wise equality from SUM equality + pointwise ≤ *)
Theorem sum_map_eq_all_eq[local]:
  ∀f g ls. SUM (MAP f ls) = SUM (MAP g ls) ∧ EVERY (λx. f x ≤ g x) ls ⇒
    ∀x. MEM x ls ⇒ f x = g x
Proof
  Induct_on `ls` >> rw[] >>
  `SUM (MAP f ls) ≤ SUM (MAP g ls)` by
    (qpat_x_assum `EVERY _ _` mp_tac >> qid_spec_tac `ls` >>
     Induct >> rw[] >> res_tac >> DECIDE_TAC) >>
  `f h = g h` by DECIDE_TAC >>
  `SUM (MAP f ls) = SUM (MAP g ls)` by DECIDE_TAC >>
  metis_tac[]
QED

(* More directly usable: SUM eq + pointwise le + MEM ⇒ contradiction with < *)
Theorem sum_le_not_lt[local]:
  ∀f g ls x.
    SUM (MAP f ls) = SUM (MAP g ls) ∧
    (∀y. MEM y ls ⇒ f y ≤ g y) ∧
    MEM x ls ∧ f x < g x ⇒ F
Proof
  rpt strip_tac >>
  `EVERY (λy. f y ≤ g y) ls` by fs[EVERY_MEM] >>
  `f x = g x` by metis_tac[sum_map_eq_all_eq] >>
  DECIDE_TAC
QED

(* Labels not in fn_labels have no successors *)
Theorem not_fn_labels_succs_empty[local]:
  ∀fn lbl. ¬MEM lbl (fn_labels fn) ⇒
    cfg_succs_of (cfg_analyze fn) lbl = []
Proof
  rw[cfg_succs_of_def, fmap_lookup_list_def] >>
  `(cfg_analyze fn).cfg_succs = build_succs fn.fn_blocks` by (
    rw[cfg_analyze_def, LET_THM] >>
    Cases_on `entry_block fn` >> simp[] >>
    pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
  `lbl ∉ FDOM (build_succs fn.fn_blocks)` by
    (simp[cfgHelpersTheory.fdom_build_succs] >> fs[fn_labels_def]) >>
  fs[FLOOKUP_DEF]
QED

(* Labels not in fn_labels have empty joined *)
Theorem not_fn_labels_joined_empty[local]:
  ∀fn st lbl. ¬MEM lbl (fn_labels fn) ⇒
    liveness_joined fn st lbl = []
Proof
  rw[liveness_joined_def, LET_THM] >>
  imp_res_tac not_fn_labels_succs_empty >> simp[]
QED

(* --- Canonical count increases when inst_map values are canonical --- *)

(* Helper: if all inst_map values equal canonical targets and FUNION changes
   something, then canonical count strictly increases *)
Theorem funion_canonical_count_increases[local]:
  ∀fn st inst_map.
    (∀k. k ∈ FDOM inst_map ⇒
       FLOOKUP inst_map k = liveness_canonical_inst fn st k) ∧
    FDOM inst_map ⊆ FDOM (FUNION inst_map st.ds_inst) ∧
    FUNION inst_map st.ds_inst ≠ st.ds_inst ⇒
    CARD { k | k ∈ FDOM st.ds_inst ∧
               FLOOKUP st.ds_inst k = liveness_canonical_inst fn st k } <
    CARD { k | k ∈ FDOM (FUNION inst_map st.ds_inst) ∧
               FLOOKUP (FUNION inst_map st.ds_inst) k =
               liveness_canonical_inst fn st k }
Proof
  rpt strip_tac >>
  (* Abbreviate the two canonical sets *)
  qabbrev_tac `S_old = { k | k ∈ FDOM st.ds_inst ∧
    FLOOKUP st.ds_inst k = liveness_canonical_inst fn st k }` >>
  qabbrev_tac `S_new = { k | k ∈ FDOM (FUNION inst_map st.ds_inst) ∧
    FLOOKUP (FUNION inst_map st.ds_inst) k =
    liveness_canonical_inst fn st k }` >>
  (* S_new is finite *)
  `FINITE S_new` by (
    simp[Abbr`S_new`] >> irule SUBSET_FINITE >>
    qexists_tac `FDOM (FUNION inst_map st.ds_inst)` >>
    simp[FDOM_FUNION] >> rw[SUBSET_DEF]) >>
  irule CARD_PSUBSET >> simp[] >>
  rw[PSUBSET_DEF, Abbr`S_old`, Abbr`S_new`]
  >- ((* SUBSET: old canonical ⊆ new canonical *)
      rw[SUBSET_DEF, FDOM_FUNION, FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP inst_map x` >> fs[] >>
      `x ∈ FDOM inst_map` by fs[FLOOKUP_DEF] >> metis_tac[])
  >- ((* ≠: there exists k in new but not old *)
      simp[EXTENSION] >> CCONTR_TAC >> fs[] >>
      (* Every element of the new canonical set is in the old ⇒ FUNION = st.ds_inst *)
      `FUNION inst_map st.ds_inst = st.ds_inst` suffices_by metis_tac[] >>
      simp_tac std_ss [fmap_eq_flookup, FLOOKUP_FUNION] >> gen_tac >>
      Cases_on `FLOOKUP inst_map x` >> simp[] >>
      rename1 `FLOOKUP inst_map x = SOME v` >>
      `x ∈ FDOM inst_map` by fs[FLOOKUP_DEF] >>
      `liveness_canonical_inst fn st x = SOME v` by metis_tac[] >>
      (* x is in new canonical set, so must be in old too *)
      qpat_x_assum `!x. _ <=> _` (qspec_then `x` mp_tac) >>
      simp[FDOM_FUNION, FLOOKUP_FUNION] >> strip_tac >>
      gvs[FLOOKUP_DEF])
QED


(* Core: SUM eq + pointwise CARD ≤ ⇒ pointwise CARD = *)
Theorem boundary_sum_eq_pointwise[local]:
  ∀fn st st'.
    liveness_boundary_sum fn st' = liveness_boundary_sum fn st ∧
    (∀l. MEM l (fn_labels fn) ⇒
         CARD (set (df_boundary [] st l)) ≤
         CARD (set (df_boundary [] st' l))) ⇒
    ∀l. MEM l (fn_labels fn) ⇒
        CARD (set (df_boundary [] st l)) =
        CARD (set (df_boundary [] st' l))
Proof
  rpt strip_tac >>
  CCONTR_TAC >> fs[liveness_boundary_sum_def] >>
  `CARD (set (df_boundary [] st l)) <
   CARD (set (df_boundary [] st' l))` by (
    first_x_assum (qspec_then `l` mp_tac) >> simp[] >> DECIDE_TAC) >>
  `SUM (MAP (\l. CARD (set (df_boundary [] st l))) (fn_labels fn)) <
   SUM (MAP (\l'. CARD (set (df_boundary [] st' l'))) (fn_labels fn))` by (
    irule sum_map_strict_increase_proof >>
    simp[EVERY_MEM] >> metis_tac[]) >>
  DECIDE_TAC
QED

(* Helper: if boundary_sum unchanged after process, then list_union is identity *)
Theorem boundary_unchanged_list_union_identity[local]:
  ∀fn lbl st fv inst_map.
    df_fold_block Backward (liveness_transfer fn.fn_blocks)
      lbl (block_instrs lbl fn.fn_blocks)
      (liveness_joined fn st lbl) = (fv, inst_map) ∧
    liveness_state_inv fn st ∧
    liveness_boundary_sum fn
      (st with <|ds_boundary := st.ds_boundary |+
         (lbl, list_union (df_boundary [] st lbl) fv);
       ds_inst := FUNION inst_map st.ds_inst|>) =
    liveness_boundary_sum fn st ⇒
    list_union (df_boundary [] st lbl) fv = df_boundary [] st lbl
Proof
  rpt strip_tac >>
  Cases_on `MEM lbl (fn_labels fn)`
  >- (irule list_union_identity >>
      qabbrev_tac `st' = st with <|ds_boundary := st.ds_boundary |+
        (lbl, list_union (df_boundary [] st lbl) fv);
        ds_inst := FUNION inst_map st.ds_inst|>` >>
      `!l'. MEM l' (fn_labels fn) ==>
            CARD (set (df_boundary [] st l')) <=
            CARD (set (df_boundary [] st' l'))` by (
        rw[Abbr `st'`] >> simp[df_boundary_def, FLOOKUP_UPDATE] >>
        Cases_on `l' = lbl` >> simp[] >>
        irule CARD_SUBSET >>
        simp[FINITE_LIST_TO_SET, list_union_set, SUBSET_UNION]) >>
      `liveness_boundary_sum fn st' = liveness_boundary_sum fn st` by
        fs[Abbr `st'`] >>
      `CARD (set (df_boundary [] st lbl)) =
       CARD (set (df_boundary [] st' lbl))` by
        metis_tac[boundary_sum_eq_pointwise] >>
      `df_boundary [] st' lbl =
       list_union (df_boundary [] st lbl) fv` by
        simp[Abbr `st'`, df_boundary_def, FLOOKUP_UPDATE] >>
      `CARD (set (df_boundary [] st lbl)) =
       CARD (set (list_union (df_boundary [] st lbl) fv))` by
        metis_tac[] >>
      `set (df_boundary [] st lbl) SUBSET
       set (list_union (df_boundary [] st lbl) fv)` by
        simp[list_union_set, SUBSET_UNION] >>
      `set (df_boundary [] st lbl) =
       set (list_union (df_boundary [] st lbl) fv)` by (
        match_mp_tac (MP_CANON SUBSET_EQ_CARD) >>
        simp[FINITE_LIST_TO_SET, list_union_set, SUBSET_UNION]) >>
      qpat_x_assum `set _ = set (list_union _ _)` mp_tac >>
      simp[list_union_set] >> strip_tac >>
      pop_assum SUBST1_TAC >> simp[SUBSET_UNION])
  >- (imp_res_tac not_fn_labels_joined_empty >>
      fs[fn_labels_def] >>
      imp_res_tac not_fn_labels_lookup_none >>
      imp_res_tac block_instrs_none >>
      `fv = liveness_joined fn st lbl` suffices_by simp[list_union_def] >>
      qpat_x_assum `df_fold_block _ _ _ _ _ = _` mp_tac >>
      simp[df_fold_block_def, df_fold_backward_def])
QED

(* When boundary unchanged and process ≠ st, canonical count strictly increases *)
Theorem canonical_count_case_c[local]:
  ∀fn lbl st st'.
    st' = df_process_block Backward [] list_union
            liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
            (cfg_analyze fn) fn.fn_blocks lbl st ∧
    liveness_state_inv fn st ∧
    st' <> st ∧
    liveness_boundary_sum fn st' = liveness_boundary_sum fn st ==>
    liveness_canonical_count fn st' > liveness_canonical_count fn st
Proof
  rpt gen_tac >> disch_tac >>
  qspecl_then [`fn`, `lbl`, `st`] strip_assume_tac
    (SIMP_RULE std_ss [LET_THM] liveness_process_eq) >>
  pairarg_tac >> gvs[] >>
  (* Step 1: boundary unchanged *)
  `list_union (df_boundary [] st lbl) fv = df_boundary [] st lbl` by (
    mp_tac (Q.SPECL [`fn`, `lbl`, `st`, `fv`, `inst_map`]
            boundary_unchanged_list_union_identity) >>
    simp[]) >>
  (* Step 2: canonical_inst unchanged *)
  `∀k. liveness_canonical_inst fn
    <|ds_inst := FUNION inst_map st.ds_inst;
      ds_boundary := st.ds_boundary |+
        (lbl, list_union (df_boundary [] st lbl) fv)|> k =
    liveness_canonical_inst fn st k` by (
    Cases >> simp[liveness_canonical_inst_def, LET_THM, liveness_joined_def] >>
    `!nbr. df_boundary []
        <|ds_inst := FUNION inst_map st.ds_inst;
          ds_boundary := st.ds_boundary |+ (lbl, df_boundary [] st lbl)|> nbr =
      df_boundary [] st nbr` by (
      rw[df_boundary_def, FLOOKUP_UPDATE] >> rw[]) >>
    simp[MAP_EQ_f]) >>
  (* Step 3: inst_map values ARE canonical *)
  `∀k. k ∈ FDOM inst_map ⇒
     FLOOKUP inst_map k = liveness_canonical_inst fn st k` by (
    rw[] >>
    drule df_fold_block_fdom_backward >> strip_tac >>
    `∃j. k = (lbl, j)` by (fs[IN_IMAGE, IN_COUNT] >> metis_tac[]) >>
    rw[liveness_canonical_inst_def, LET_THM] >>
    pairarg_tac >> fs[] >>
    `im = inst_map` by (
      qpat_x_assum `df_fold_block _ _ _ _ _ = (fv, inst_map)` mp_tac >>
      simp[] >> strip_tac >> gvs[]) >>
    simp[]) >>
  (* Step 4: FUNION inst_map st.ds_inst ≠ st.ds_inst *)
  `FUNION inst_map st.ds_inst <> st.ds_inst` by (
    CCONTR_TAC >> gvs[] >>
    (* Now: inst unchanged, boundary update is the only difference *)
    (* Derive lbl ∈ FDOM st.ds_boundary from invariant + fold FDOM *)
    `lbl IN FDOM st.ds_boundary` by (
      qpat_x_assum `liveness_state_inv fn st`
        (strip_assume_tac o REWRITE_RULE [liveness_state_inv_def]) >>
      qpat_x_assum `df_fold_block _ _ _ _ _ = _`
        (strip_assume_tac o MATCH_MP df_fold_block_fdom_backward) >>
      `(lbl, 0n) IN FDOM inst_map` by
        (fs[IN_IMAGE, IN_COUNT] >> qexists_tac `0` >> simp[]) >>
      `(lbl, 0n) IN FDOM st.ds_inst` by
        metis_tac[FDOM_FUNION, IN_UNION] >>
      metis_tac[]) >>
    (* Now boundary update is idempotent *)
    qpat_x_assum `_ <> st` mp_tac >>
    simp[df_state_component_equality] >>
    irule FUPDATE_ELIM >> simp[df_boundary_def, FLOOKUP_DEF]) >>
  (* Step 5: canonical_count st' = CARD {funion canonical set with st targets} *)
  `liveness_canonical_count fn
    <|ds_inst := FUNION inst_map st.ds_inst;
      ds_boundary := st.ds_boundary |+
        (lbl, list_union (df_boundary [] st lbl) fv)|> =
   CARD {k | k IN FDOM (FUNION inst_map st.ds_inst) /\
             FLOOKUP (FUNION inst_map st.ds_inst) k =
             liveness_canonical_inst fn st k}` by (
    simp[liveness_canonical_count_def] >>
    AP_TERM_TAC >> rw[EXTENSION]) >>
  pop_assum (fn eq => REWRITE_TAC [GREATER_DEF, eq]) >>
  REWRITE_TAC [liveness_canonical_count_def] >>
  irule funion_canonical_count_increases >>
  simp[FDOM_FUNION]
QED

(* Measure strictly increases when state changes *)
Theorem liveness_measure_increases[local]:
  ∀fn lbl st.
    (MEM lbl (fn_labels fn) ∨ MEM lbl (cfg_analyze fn).cfg_dfs_post) ∧
    liveness_state_inv fn st ∧
    df_process_block Backward [] list_union
      liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
      (cfg_analyze fn) fn.fn_blocks lbl st <> st ==>
    liveness_measure fn st <
    liveness_measure fn
      (df_process_block Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
        (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt gen_tac >> disch_tac >>
  qabbrev_tac `st' = df_process_block Backward [] list_union
    liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
    (cfg_analyze fn) fn.fn_blocks lbl st` >>
  simp_tac std_ss [liveness_measure_def] >>
  `liveness_state_inv fn st` by fs[] >>
  `st' <> st` by fs[] >>
  `liveness_canonical_count fn st <= liveness_inst_key_bound fn` by
    metis_tac[canonical_count_bounded] >>
  Cases_on `liveness_boundary_sum fn st' = liveness_boundary_sum fn st`
  >- ((* Case C: boundary unchanged, canonical count increases *)
      `liveness_canonical_count fn st' > liveness_canonical_count fn st` by
        (mp_tac (Q.SPECL [`fn`, `lbl`, `st`, `st'`] canonical_count_case_c) >>
         simp_tac std_ss [Abbr`st'`] >>
         disch_tac >> first_x_assum match_mp_tac >>
         rpt conj_tac >> first_x_assum ACCEPT_TAC) >>
      fs[GREATER_DEF] >> DECIDE_TAC)
  >- ((* Case A: boundary changed → boundary_sum strictly increased *)
      `liveness_boundary_sum fn st < liveness_boundary_sum fn st'` suffices_by
        (strip_tac >>
         irule LESS_LESS_EQ_TRANS >>
         qexists_tac `liveness_boundary_sum fn st' *
                        (liveness_inst_key_bound fn + 1)` >>
         conj_tac >- (irule weighted_sum_strict >> simp[]) >>
         DECIDE_TAC) >>
      (* boundary_sum st <= boundary_sum st' (mono) + ≠ → strict *)
      `liveness_boundary_sum fn st <= liveness_boundary_sum fn st'` by
        (simp[Abbr`st'`] >> metis_tac[boundary_sum_process_mono]) >>
      DECIDE_TAC)
QED

(* Main boundedness theorem *)
Theorem live_vars_bounded_proof:
  ∀fn lbl idx v.
    let st = liveness_analyze fn in
    MEM v (live_vars_at st lbl idx) ⇒
    MEM v (fn_all_vars fn.fn_blocks)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  simp[liveness_analyze_def, live_vars_at_def, df_at_def] >>
  strip_tac >>
  qabbrev_tac `result = df_analyze Backward [] list_union
    liveness_transfer liveness_edge_transfer fn.fn_blocks NONE fn` >>
  (* Show liveness_state_inv result holds *)
  `liveness_state_inv fn result` by (
    simp[Abbr`result`] >>
    irule (SIMP_RULE std_ss [LET_THM]
      dfAnalyzeProofsTheory.df_analyze_invariant_backward_restricted) >>
    conj_tac
    >- (qexistsl_tac [
          `LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks)) *
             (liveness_inst_key_bound fn + 1) +
           liveness_inst_key_bound fn`,
          `liveness_measure fn`,
          `\lbl. MEM lbl (fn_labels fn) \/
                 MEM lbl (cfg_analyze fn).cfg_dfs_post`] >>
        simp_tac std_ss [] >> rpt conj_tac
        >- metis_tac[liveness_measure_bounded]
        >- metis_tac[liveness_state_inv_preserved]
        >- metis_tac[liveness_measure_increases]
        >- (rpt strip_tac >>
            mp_tac (Q.SPEC `fn` dfAnalyzeProofsTheory.preds_subset_fn_labels) >>
            simp[EVERY_MEM] >> metis_tac[])
        >- (simp[EVERY_MEM]))
    >- simp[liveness_state_inv_init]) >>
  fs[liveness_state_inv_def, liveness_bounded_def] >>
  Cases_on `FLOOKUP result.ds_inst (lbl, idx)` >> fs[] >>
  metis_tac[]
QED

(* ===== Convergence (for soundness, requires wf_function) ===== *)

(* Convergence: establish is_fixpoint for liveness analysis *)
Theorem liveness_convergence:
  ∀fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let result = liveness_analyze fn in
    let process = df_process_block Backward [] list_union
                    liveness_transfer liveness_edge_transfer bbs NONE
                    cfg bbs in
    is_fixpoint process cfg.cfg_dfs_pre result
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  simp[liveness_analyze_def] >>
  irule (SIMP_RULE std_ss [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_backward) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule (SIMP_RULE std_ss [LET_THM, direction_case_def]
        (Q.SPEC `Backward`
          dfAnalyzeProofsTheory.df_process_deps_complete_proof)) >>
      simp[list_union_absorption] >>
      metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond])
  >- (qexistsl_tac [
        `liveness_state_inv fn`,
        `LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks)) *
           (liveness_inst_key_bound fn + 1) +
         liveness_inst_key_bound fn`,
        `liveness_measure fn`] >>
      simp_tac std_ss [optionTheory.option_case_def] >>
      conj_tac >- metis_tac[liveness_measure_bounded] >>
      conj_tac
      >- (rpt strip_tac >>
          `MEM lbl (fn_labels fn) \/
           MEM lbl (cfg_analyze fn).cfg_dfs_post` by simp[] >>
          metis_tac[liveness_state_inv_preserved])
      >- (conj_tac
          >- (rpt strip_tac >>
              `MEM lbl (fn_labels fn) \/
               MEM lbl (cfg_analyze fn).cfg_dfs_post` by simp[] >>
              metis_tac[liveness_measure_increases])
          >- simp[liveness_state_inv_init]))
QED

(* ===================================================================
   Soundness proof: liveness_sound_proof
   =================================================================== *)

(* ===== Membership helpers for transfer functions ===== *)

Theorem mem_live_update_cases[local]:
  ∀v defs uses live.
    MEM v (live_update defs uses live) ⇒
    MEM v uses ∨ (MEM v live ∧ ¬MEM v defs)
Proof
  rw[live_update_def, LET_THM, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem mem_foldl_list_union[local]:
  ∀v ls base.
    MEM v (FOLDL list_union base ls) ⇔
    MEM v base ∨ ∃x. MEM x ls ∧ MEM v x
Proof
  Induct_on `ls` >>
  simp[list_union_mem_proof] >>
  metis_tac[]
QED

(* ===== Soundness invariant ===== *)

(* The key soundness invariant: every live variable has a witness path *)
Definition liveness_sound_inv_def:
  liveness_sound_inv bbs cfg (st : string list df_state) ⇔
    (∀lbl idx v. MEM v (df_at [] st lbl idx) ⇒
      ∃path. cfg_exec_path cfg ((lbl,idx)::path) ∧
             used_before_defined bbs v ((lbl,idx)::path)) ∧
    (∀lbl v. MEM v (df_boundary [] st lbl) ⇒
      ∃path. cfg_exec_path cfg ((lbl,0)::path) ∧
             used_before_defined bbs v ((lbl,0)::path))
End

(* input_vars_from membership: if v is in the output, either v was in the
   base liveness (and survived PHI processing) or v is a PHI operand.
   Proved via input_vars_from_phi_correct_proof (same statement). *)
Theorem input_vars_from_mem:
  ∀instrs v src_lbl live.
    MEM v (input_vars_from src_lbl instrs live) ⇒
    MEM v live ∨
    ∃inst. MEM inst instrs ∧ inst.inst_opcode = PHI ∧
           MEM (src_lbl, v) (phi_pairs inst.inst_operands)
Proof
  metis_tac[input_vars_from_phi_correct_proof]
QED

(* ===== Path construction helpers ===== *)

(* Intra-block path: consecutive indices within a single block form
   a valid execution path *)
Theorem cfg_exec_path_intra:
  ∀n lbl s cfg.
    cfg_exec_path cfg (GENLIST (\i. (lbl:string, s + i)) (SUC n))
Proof
  Induct >- simp[GENLIST_CONS, cfg_exec_path_def] >>
  rpt gen_tac >>
  simp[Once GENLIST_CONS, combinTheory.o_DEF] >>
  `GENLIST (\x. (lbl:string, s + SUC x)) (SUC n) =
   GENLIST (\i. (lbl, SUC s + i)) (SUC n)` by (
    irule GENLIST_CONG >> simp[ADD_CLAUSES]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`lbl`, `SUC s`, `cfg`] mp_tac) >>
  Cases_on `GENLIST (\i. (lbl:string, SUC s + i)) (SUC n)` >- fs[GENLIST] >>
  strip_tac >>
  `h = (lbl, SUC s)` by (
    qpat_x_assum `_ = h::t` (mp_tac o SYM) >>
    simp[GENLIST_CONS, combinTheory.o_DEF]) >>
  rw[cfg_exec_path_def]
QED

(* Extending an execution path: append a valid continuation that starts
   either at the next index in the same block or at index 0 of a successor *)
Theorem cfg_exec_path_extend:
  ∀path lbl2 idx2 suffix cfg.
    cfg_exec_path cfg path ∧ path <> [] ∧
    ((lbl2 = FST (LAST path) ∧ idx2 = SND (LAST path) + 1) ∨
     (MEM lbl2 (cfg_succs_of cfg (FST (LAST path))) ∧ idx2 = 0)) ∧
    cfg_exec_path cfg ((lbl2, idx2) :: suffix) ==>
    cfg_exec_path cfg (path ++ (lbl2, idx2) :: suffix)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `path`
  >- (gvs[cfg_exec_path_def]) >>
  gvs[cfg_exec_path_def] >>
  PairCases_on `h` >> gvs[cfg_exec_path_def]
QED

Theorem not_var_defined_at_phi[local]:
  ∀bbs lbl idx v bb.
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx < LENGTH bb.bb_instructions ∧
    (EL idx bb.bb_instructions).inst_opcode = PHI ==>
    ¬var_defined_at bbs lbl idx v
Proof
  rw[var_defined_at_def]
QED

Theorem used_before_defined_witness[local]:
  ∀bbs v positions k.
    k < LENGTH positions ∧
    var_used_at bbs (FST (EL k positions)) (SND (EL k positions)) v ∧
    (∀j. j < k ==> ¬var_defined_at bbs (FST (EL j positions))
                                         (SND (EL j positions)) v) ==>
    used_before_defined bbs v positions
Proof
  rw[used_before_defined_def] >> qexists_tac `k` >> simp[]
QED

(* Prepending positions that don't define v preserves used-before-defined *)
Theorem used_before_defined_prepend:
  ∀prefix bbs v suffix.
    used_before_defined bbs v suffix ∧
    (∀j. j < LENGTH prefix ==>
       ¬var_defined_at bbs (FST (EL j prefix)) (SND (EL j prefix)) v) ==>
    used_before_defined bbs v (prefix ++ suffix)
Proof
  rw[used_before_defined_def] >>
  qexists_tac `LENGTH prefix + k` >>
  simp[EL_APPEND2, EL_APPEND1] >>
  rpt strip_tac >>
  Cases_on `j < LENGTH prefix`
  >- (res_tac >> gvs[EL_APPEND1]) >>
  `j - LENGTH prefix < k` by simp[] >>
  `LENGTH prefix <= j` by simp[] >>
  gvs[EL_APPEND2]
QED

Theorem use_in_block_path_aux[local]:
  ∀n bbs cfg lbl bb idx j v.
    n = j - idx ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx <= j ∧ j < LENGTH bb.bb_instructions ∧
    MEM v (inst_uses (EL j bb.bb_instructions)) ∧
    (∀k. idx <= k ∧ k < j ==> ¬MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  Induct
  >- (
    rpt strip_tac >>
    `j = idx` by simp[] >> gvs[] >>
    qexists_tac `[]` >> simp[cfg_exec_path_def] >>
    irule used_before_defined_witness >> qexists_tac `0` >>
    simp[var_used_at_def] >>
    qexistsl_tac [`bb`, `EL idx bb.bb_instructions`] >> simp[])
  >- (
    rpt strip_tac >>
    `idx < j` by simp[] >>
    `?path. cfg_exec_path cfg ((lbl, SUC idx) :: path) /\
            used_before_defined bbs v ((lbl, SUC idx) :: path)` by (
      first_x_assum (qspecl_then [`bbs`,`cfg`,`lbl`,`bb`,`SUC idx`,`j`,`v`]
        mp_tac) >> fs[]) >>
    qexists_tac `(lbl, SUC idx) :: path` >>
    simp[cfg_exec_path_def, ADD1] >>
    `~var_defined_at bbs lbl idx v` by (
      simp[var_defined_at_def] >> rpt strip_tac >>
      `bb' = bb` by metis_tac[lookup_block_unique] >> gvs[] >>
      first_x_assum (qspec_then `idx` mp_tac) >> simp[]) >>
    fs[used_before_defined_def] >>
    qexists_tac `SUC k` >>
    gvs[ADD1] >>
    rpt strip_tac >>
    Cases_on `j'`
    >- gvs[]
    >- (gvs[] >> first_x_assum (qspec_then `n'` mp_tac) >> simp[]))
QED

Theorem use_in_block_path[local]:
  ∀bbs cfg lbl bb idx j v.
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx <= j ∧ j < LENGTH bb.bb_instructions ∧
    MEM v (inst_uses (EL j bb.bb_instructions)) ∧
    (∀k. idx <= k ∧ k < j ==> ¬MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  metis_tac[use_in_block_path_aux]
QED

(* Cross-block path construction: if v is not killed from idx to block end,
   and a use-before-def path exists from successor entry, then a
   use-before-def path exists from (lbl, idx) *)
Theorem cross_block_path:
  ∀bbs cfg lr fn bb lbl idx succ_lbl succ_path v.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ bbs = fn.fn_blocks ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM succ_lbl (cfg_succs_of cfg lbl) ∧
    cfg_exec_path cfg ((succ_lbl, 0) :: succ_path) ∧
    (∀k. idx <= k ∧ k < LENGTH bb.bb_instructions ==>
       ¬MEM v (inst_defs (EL k bb.bb_instructions))) ∧
    used_before_defined bbs v ((succ_lbl, 0) :: succ_path) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  rpt strip_tac >>
  qabbrev_tac `last_idx = LENGTH bb.bb_instructions - 1` >>
  `idx <= last_idx` by simp[Abbr`last_idx`] >>
  qabbrev_tac `gl = GENLIST (\i. (lbl:string, idx + i)) (SUC (last_idx - idx))` >>
  `cfg_exec_path cfg gl` by metis_tac[cfg_exec_path_intra] >>
  `gl <> []` by simp[Abbr`gl`, GENLIST] >>
  `HD gl = (lbl, idx)` by simp[Abbr`gl`, GENLIST_CONS] >>
  `LAST gl = (lbl, last_idx)` by simp[Abbr`gl`, LAST_EL, EL_GENLIST, Abbr`last_idx`] >>
  `LENGTH gl = SUC (last_idx - idx)` by simp[Abbr`gl`] >>
  `∀k. k < LENGTH gl ==> EL k gl = (lbl, idx + k)` by simp[Abbr`gl`, EL_GENLIST] >>
  `cfg_exec_path cfg (gl ++ (succ_lbl, 0) :: succ_path)` by (
    irule cfg_exec_path_extend >> rpt conj_tac >> fs[] >> metis_tac[]) >>
  qexists_tac `TL gl ++ (succ_lbl, 0) :: succ_path` >>
  `(lbl,idx) :: (TL gl ++ (succ_lbl,0)::succ_path) =
   gl ++ (succ_lbl,0)::succ_path` by
    (Cases_on `gl` >> fs[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  conj_tac >- fs[] >>
  irule used_before_defined_prepend >> fs[] >>
  rpt strip_tac >>
  `EL j gl = (lbl, idx + j)` by (
    first_x_assum (qspec_then `j` mp_tac) >> fs[]) >>
  fs[var_defined_at_def] >>
  `bb' = bb` by metis_tac[lookup_block_unique] >>
  gvs[Abbr`last_idx`]
QED

Theorem phi_use_path[local]:
  ∀bbs cfg succ_lbl succ_bb src_lbl inst v.
    lookup_block succ_lbl bbs = SOME succ_bb ∧ succ_bb.bb_label = succ_lbl ∧
    bb_well_formed succ_bb ∧
    MEM inst succ_bb.bb_instructions ∧ inst.inst_opcode = PHI ∧
    MEM (src_lbl, v) (phi_pairs inst.inst_operands) ==>
    ∃path.
      cfg_exec_path cfg ((succ_lbl, 0) :: path) ∧
      used_before_defined bbs v ((succ_lbl, 0) :: path)
Proof
  rpt strip_tac >>
  `∃k. k < LENGTH succ_bb.bb_instructions ∧
       EL k succ_bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
  `∀j. j < k ==> (EL j succ_bb.bb_instructions).inst_opcode = PHI` by
    (rpt strip_tac >> fs[bb_well_formed_def] >> metis_tac[]) >>
  imp_res_tac lookup_block_label >>
  qabbrev_tac `positions = GENLIST (\i. (succ_lbl:string, i)) (SUC k)` >>
  `LENGTH positions = SUC k` by simp[Abbr`positions`] >>
  `positions <> []` by simp[Abbr`positions`, GENLIST] >>
  `HD positions = (succ_lbl, 0)` by simp[Abbr`positions`, GENLIST_CONS] >>
  `(succ_lbl, 0) :: TL positions = positions` by
    (Cases_on `positions` >> fs[]) >>
  `cfg_exec_path cfg ((succ_lbl, 0) :: TL positions)` by (
    `(succ_lbl, 0) :: TL positions =
     GENLIST (\i. (succ_lbl, 0 + i)) (SUC (k - 0))` by
      simp[Abbr`positions`] >>
    pop_assum SUBST1_TAC >>
    irule cfg_exec_path_intra >> simp[]) >>
  qexists_tac `TL positions` >> conj_tac >- simp[] >>
  `(succ_lbl, 0) :: TL positions = positions` by fs[] >>
  asm_rewrite_tac[] >>
  irule used_before_defined_witness >> qexists_tac `k` >> simp[] >>
  conj_tac
  >- (
    rpt gen_tac >> strip_tac >>
    `EL j positions = (succ_lbl, j)` by simp[Abbr`positions`, EL_GENLIST] >>
    simp[] >> irule not_var_defined_at_phi >>
    qexists_tac `succ_bb` >> simp[])
  >- (
    `EL k positions = (succ_lbl, k)` by simp[Abbr`positions`, EL_GENLIST] >>
    simp[var_used_at_def, inst_uses_def] >>
    irule phi_pairs_subset_uses >>
    simp[MEM_MAP] >> qexists_tac `(src_lbl, v)` >> simp[])
QED

(* ===== Fold value soundness ===== *)

(* Key lemma: backward fold values at each index have witness paths.
   Proved by induction on (LENGTH instrs - idx).
   At idx = LENGTH instrs: value is joined (from successors).
   At idx < LENGTH instrs: value is live_update(defs, uses, val_at_(idx+1)). *)
Theorem fold_values_sound[local]:
  ∀n fn cfg bbs bb lbl idx instrs joined im fv v.
    n = LENGTH instrs - idx ∧
    wf_function fn ∧ cfg = cfg_analyze fn ∧ bbs = fn.fn_blocks ∧
    lookup_block lbl bbs = SOME bb ∧ bb.bb_label = lbl ∧
    instrs = bb.bb_instructions ∧
    df_fold_block Backward (liveness_transfer bbs) lbl instrs joined = (fv, im) ∧
    idx <= LENGTH instrs ∧
    (* Joined value is sound: every var in it has a witness path *)
    (∀w. MEM w joined ⇒
      ∃path. cfg_exec_path cfg ((lbl, LENGTH instrs) :: path) ∧
             used_before_defined bbs w ((lbl, LENGTH instrs) :: path)) ∧
    MEM v (THE (FLOOKUP im (lbl, idx))) ⇒
    ∃path. cfg_exec_path cfg ((lbl, idx) :: path) ∧
           used_before_defined bbs v ((lbl, idx) :: path)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (
    (* Base: n = 0, so idx = LENGTH instrs. Value is joined. *)
    `idx = LENGTH instrs` by DECIDE_TAC >>
    `df_fold_backward (liveness_transfer bbs) lbl instrs 0 joined FEMPTY =
     (fv, im)` by fs[df_fold_block_def] >>
    drule dfAnalyzeProofsTheory.df_fold_backward_at >> strip_tac >>
    `FLOOKUP im (lbl, LENGTH instrs) = SOME joined` by fs[] >>
    gvs[])
  >- (
    (* Step: n = SUC n', so idx < LENGTH instrs *)
    `idx < LENGTH instrs` by (
      Cases_on `idx = LENGTH instrs` >> gvs[]) >>
    (* Get fold characterization without consuming df_fold_block assumption *)
    `df_fold_backward (liveness_transfer bbs) lbl instrs 0 joined FEMPTY =
     (fv, im)` by fs[df_fold_block_def] >>
    drule dfAnalyzeProofsTheory.df_fold_backward_at >> strip_tac >>
    (* Value at idx is transfer(instrs[idx], value at idx+1) *)
    `FLOOKUP im (lbl, idx) =
     SOME (liveness_transfer bbs (EL idx instrs)
       (THE (FLOOKUP im (lbl, SUC idx))))` by (
      first_x_assum (qspec_then `idx` mp_tac) >> simp[]) >>
    fs[liveness_transfer_def] >>
    (* MEM v (live_update ...) → disjunction *)
    drule mem_live_update_cases >> strip_tac
    >- (
      (* Case 1: v is used by instrs[idx] *)
      irule use_in_block_path >>
      qexistsl_tac [`bb`, `idx`] >> gvs[])
    >- (
      (* Case 2: v is live at idx+1 and not defined by instrs[idx] *)
      (* Apply IH to get path from SUC idx *)
      first_x_assum (qspecl_then
        [`fn`,`bb`,`SUC idx`,`joined`,`im`,`fv`,`v`] mp_tac) >>
      impl_tac >- gvs[] >>
      strip_tac >>
      qexists_tac `(bb.bb_label, SUC idx) :: path` >>
      conj_tac >- gvs[cfg_exec_path_def, ADD1] >>
      (* Extend used_before_defined by prepending (lbl, idx) *)
      `(lbl,idx)::(bb.bb_label,SUC idx)::path =
       [(lbl,idx)] ++ ((bb.bb_label,SUC idx)::path)` by simp[] >>
      pop_assum SUBST1_TAC >>
      match_mp_tac used_before_defined_prepend >>
      conj_tac >- metis_tac[] >>
      simp[] >>
      simp[var_defined_at_def] >> rpt strip_tac >>
      `bb' = bb` by metis_tac[lookup_block_unique] >>
      gvs[inst_defs_def]))
QED

(* Helper: any fold output value has a witness path — covers both
   lookup_block NONE (empty block) and SOME cases *)
Theorem fold_output_sound[local]:
  ∀fn bbs cfg lbl idx instrs joined im fv v.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ bbs = fn.fn_blocks ∧
    instrs = block_instrs lbl bbs ∧
    df_fold_block Backward (liveness_transfer bbs) lbl instrs joined = (fv, im) ∧
    idx <= LENGTH instrs ∧
    (∀w. MEM w joined ⇒
      ∃path. cfg_exec_path cfg ((lbl, LENGTH instrs) :: path) ∧
             used_before_defined bbs w ((lbl, LENGTH instrs) :: path)) ∧
    MEM v (THE (FLOOKUP im (lbl, idx))) ⇒
    ∃path. cfg_exec_path cfg ((lbl, idx) :: path) ∧
           used_before_defined bbs v ((lbl, idx) :: path)
Proof
  rpt strip_tac >>
  Cases_on `lookup_block lbl bbs`
  >- (
    imp_res_tac block_instrs_none >> gvs[] >>
    drule fold_block_init_value_backward >> strip_tac >>
    gvs[])
  >- (
    rename1 `lookup_block lbl bbs = SOME bb` >>
    imp_res_tac block_instrs_some >>
    imp_res_tac lookup_block_label >>
    imp_res_tac lookup_block_mem >>
    `bb_well_formed bb` by metis_tac[wf_function_def] >>
    gvs[] >>
    irule fold_values_sound >>
    conj_tac >- (qexists_tac `fn` >> simp[]) >>
    qexistsl_tac [`bb`, `fv`, `im`, `bb.bb_instructions`,
                  `joined`, `LENGTH bb.bb_instructions - idx`] >>
    gvs[])
QED

(* Helper: joined value from successors is sound *)
Theorem joined_value_sound[local]:
  ∀fn bbs cfg st lbl v.
    wf_function fn ∧ cfg = cfg_analyze fn ∧ bbs = fn.fn_blocks ∧
    liveness_sound_inv bbs cfg st ∧
    MEM v (liveness_joined fn st lbl) ⇒
    ∃path. cfg_exec_path cfg ((lbl, LENGTH (block_instrs lbl bbs)) :: path) ∧
           used_before_defined bbs v ((lbl, LENGTH (block_instrs lbl bbs)) :: path)
Proof
  rpt strip_tac >>
  fs[liveness_joined_def, LET_THM] >>
  gvs[] >>
  (* Case split on whether succs is empty *)
  Cases_on `MAP (λnbr. liveness_edge_transfer fn.fn_blocks nbr lbl
              (df_boundary [] st nbr)) (cfg_succs_of (cfg_analyze fn) lbl)` >>
  gvs[] >>
  (* Non-empty case: extract a specific neighbor *)
  `∃nbr. MEM nbr (cfg_succs_of (cfg_analyze fn) lbl) ∧
         MEM v (liveness_edge_transfer fn.fn_blocks nbr lbl
                  (df_boundary [] st nbr))` by (
    `∃y. MEM y (h::t) ∧ MEM v y` by (
      fs[mem_foldl_list_union, list_union_mem_proof] >>
      metis_tac[MEM]) >>
    `MEM y (MAP (λnbr. liveness_edge_transfer fn.fn_blocks nbr lbl
                (df_boundary [] st nbr)) (cfg_succs_of (cfg_analyze fn) lbl))`
      by metis_tac[] >>
    gvs[MEM_MAP] >> metis_tac[]) >>
  (* Get path from (nbr, 0) via edge_transfer analysis *)
  `∃path. cfg_exec_path (cfg_analyze fn) ((nbr, 0) :: path) ∧
          used_before_defined fn.fn_blocks v ((nbr, 0) :: path)` by (
    Cases_on `lookup_block nbr fn.fn_blocks`
    >- (
      fs[liveness_edge_transfer_def] >>
      metis_tac[liveness_sound_inv_def])
    >- (
      rename1 `lookup_block nbr fn.fn_blocks = SOME succ_bb` >>
      fs[liveness_edge_transfer_def] >>
      drule input_vars_from_mem >> strip_tac
      >- metis_tac[liveness_sound_inv_def]
      >- (
        imp_res_tac lookup_block_label >>
        `bb_well_formed succ_bb` by (
          fs[wf_function_def] >> metis_tac[lookup_block_mem]) >>
        irule phi_use_path >> metis_tac[]))) >>
  (* Extend path from (nbr, 0) to (lbl, LENGTH instrs) *)
  qexists_tac `(nbr, 0) :: path` >>
  simp[cfg_exec_path_def] >>
  `(lbl, LENGTH (block_instrs lbl fn.fn_blocks)) :: (nbr, 0) :: path =
   [(lbl, LENGTH (block_instrs lbl fn.fn_blocks))] ++ ((nbr, 0) :: path)` by simp[] >>
  pop_assum SUBST1_TAC >>
  match_mp_tac used_before_defined_prepend >>
  conj_tac >- metis_tac[] >>
  simp[var_defined_at_def] >>
  rpt strip_tac >> imp_res_tac block_instrs_some >> simp[]
QED

(* Soundness invariant preservation *)
Theorem liveness_sound_inv_preserved[local]:
  ∀fn st lbl.
    wf_function fn ⇒
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Backward [] list_union
          liveness_transfer liveness_edge_transfer bbs NONE cfg bbs in
    liveness_state_inv fn st ∧ liveness_sound_inv bbs cfg st ⇒
    liveness_sound_inv bbs cfg (process lbl st)
Proof
  rpt strip_tac >>
  simp[LET_THM] >> strip_tac >>
  simp[liveness_sound_inv_def] >>
  (* Set up fold decomposition *)
  qabbrev_tac `process = df_process_block Backward [] list_union
    liveness_transfer liveness_edge_transfer fn.fn_blocks NONE
    (cfg_analyze fn) fn.fn_blocks` >>
  Cases_on `df_fold_block Backward (liveness_transfer fn.fn_blocks)
              lbl (block_instrs lbl fn.fn_blocks)
              (liveness_joined fn st lbl)` >>
  rename1 `_ = (fv, im)` >>
  qabbrev_tac `instrs = block_instrs lbl fn.fn_blocks` >>
  qabbrev_tac `joined = liveness_joined fn st lbl` >>
  `FDOM im = IMAGE (λi. (lbl,i)) (count (LENGTH instrs + 1))` by
    metis_tac[df_fold_block_fdom_backward] >>
  (* Derive process = record form *)
  `process lbl st =
     st with <|ds_boundary := st.ds_boundary |+
                (lbl, list_union (df_boundary [] st lbl) fv);
               ds_inst := im ⊌ st.ds_inst|>` by (
    mp_tac (SIMP_RULE std_ss [LET_THM]
      (Q.SPECL [`fn`, `lbl`, `st`] liveness_process_eq)) >>
    simp[Abbr `process`]) >>
  (* Derive joined soundness — reusable in both parts *)
  `∀w. MEM w joined ⇒
    ∃path. cfg_exec_path (cfg_analyze fn) ((lbl, LENGTH instrs) :: path) ∧
           used_before_defined fn.fn_blocks w ((lbl, LENGTH instrs) :: path)` by (
    simp[Abbr `instrs`, Abbr `joined`] >> rpt strip_tac >>
    qspecl_then [`fn`, `fn.fn_blocks`, `cfg_analyze fn`, `st`, `lbl`, `w`]
      mp_tac joined_value_sound >>
    simp[]) >>
  conj_tac
  (* Part 1: inst values — case on FLOOKUP im directly *)
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP im (lbl', idx)`
      (* NONE: FUNION falls through to st *)
      >- (
        `df_at [] (process lbl st) lbl' idx = df_at [] st lbl' idx` by
          simp[df_at_def, FLOOKUP_FUNION] >>
        gvs[] >> metis_tac[liveness_sound_inv_def])
      (* SOME: (lbl',idx) ∈ FDOM im, so lbl' = lbl *)
      >- (
        `(lbl', idx) IN FDOM im` by metis_tac[flookup_thm] >>
        `lbl' = lbl` by (gvs[IN_IMAGE, IN_COUNT]) >>
        gvs[] >>
        (* Normalize df_at to FLOOKUP form *)
        fs[df_at_def, FLOOKUP_FUNION] >>
        `idx <= LENGTH instrs` by fs[IN_IMAGE, IN_COUNT] >>
        qspecl_then [`fn`, `fn.fn_blocks`, `cfg_analyze fn`, `lbl`,
                     `idx`, `block_instrs lbl fn.fn_blocks`, `joined`,
                     `im`, `fv`, `v`]
          mp_tac fold_output_sound >>
        simp[Abbr `instrs`, Abbr `joined`]))
  (* Part 2: boundary values *)
  >- (rpt strip_tac >>
      Cases_on `lbl' = lbl`
      (* lbl' = lbl: boundary updated *)
      >- (
        gvs[] >>
        fs[df_boundary_def, FLOOKUP_UPDATE] >>
        fs[list_union_mem_proof]
        (* MEM v (old boundary) → fold back to df_boundary, use old invariant *)
        >- metis_tac[liveness_sound_inv_def, df_boundary_def]
        (* MEM v fv → derive fv = THE(FLOOKUP im (lbl,0)), apply fold_output_sound *)
        >- (
          `df_fold_backward (liveness_transfer fn.fn_blocks)
             lbl instrs 0 joined FEMPTY = (fv, im)` by
            fs[df_fold_block_def] >>
          drule dfAnalyzeProofsTheory.df_fold_backward_at >> strip_tac >>
          `MEM v (THE (FLOOKUP im (lbl, 0)))` by gvs[] >>
          qspecl_then [`fn`, `fn.fn_blocks`, `cfg_analyze fn`, `lbl`,
                       `0`, `block_instrs lbl fn.fn_blocks`, `joined`,
                       `im`, `fv`, `v`]
            mp_tac fold_output_sound >>
          simp[Abbr `instrs`, Abbr `joined`]))
      (* lbl' ≠ lbl: boundary unchanged *)
      >- (
        `df_boundary [] (process lbl st) lbl' =
         df_boundary [] st lbl'` by
          simp[Abbr `process`, process_boundary_other] >>
        metis_tac[liveness_sound_inv_def]))
QED

(* Init lemma for soundness invariant *)
Theorem liveness_sound_inv_init[local]:
  ∀bbs cfg lbls. liveness_sound_inv bbs cfg (init_df_state [] lbls)
Proof
  simp[liveness_sound_inv_def, init_df_state_def, df_at_def, df_boundary_def] >>
  rpt gen_tac >> strip_tac >>
  `∀k v. FLOOKUP (FOLDL (λm lbl. m |+ (lbl, ([]:(string list)))) FEMPTY lbls) k =
         SOME v ⇒ v = []` by
    metis_tac[dfAnalyzeProofsTheory.foldl_fupdate_flookup, FLOOKUP_EMPTY,
              optionTheory.NOT_SOME_NONE] >>
  Cases_on `FLOOKUP (FOLDL (λm lbl. m |+ (lbl, ([]:(string list)))) FEMPTY lbls) lbl` >>
  fs[] >> res_tac >> gvs[]
QED

(* Helper: soundness invariant holds for analysis result *)
Theorem liveness_sound_inv_result[local]:
  ∀fn.
    wf_function fn ⇒
    liveness_sound_inv fn.fn_blocks (cfg_analyze fn)
      (df_analyze Backward [] list_union
        liveness_transfer liveness_edge_transfer fn.fn_blocks NONE fn)
Proof
  rpt strip_tac >>
  `(λst. liveness_state_inv fn st ∧
         liveness_sound_inv fn.fn_blocks (cfg_analyze fn) st)
     (df_analyze Backward [] list_union
       liveness_transfer liveness_edge_transfer fn.fn_blocks NONE fn)`
    suffices_by simp[] >>
  irule (SIMP_RULE std_ss [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_invariant_backward_restricted) >>
  conj_tac
  >- (qexistsl_tac [
        `LENGTH (fn_labels fn) * CARD (set (fn_all_vars fn.fn_blocks)) *
           (liveness_inst_key_bound fn + 1) +
         liveness_inst_key_bound fn`,
        `liveness_measure fn`,
        `\lbl. MEM lbl (fn_labels fn) \/
               MEM lbl (cfg_analyze fn).cfg_dfs_post`] >>
      simp_tac std_ss [] >> rpt conj_tac
      >- metis_tac[liveness_measure_bounded]
      >- metis_tac[liveness_state_inv_preserved, liveness_sound_inv_preserved]
      >- metis_tac[liveness_measure_increases]
      >- (rpt strip_tac >>
          mp_tac (Q.SPEC `fn` dfAnalyzeProofsTheory.preds_subset_fn_labels) >>
          simp[EVERY_MEM] >> metis_tac[])
      >- (simp[EVERY_MEM]))
  >- simp[liveness_state_inv_init, liveness_sound_inv_init]
QED

(* Main soundness theorem *)
Theorem liveness_sound_proof:
  ∀fn lbl idx v.
    let cfg = cfg_analyze fn in
    let st = liveness_analyze fn in
    let bbs = fn.fn_blocks in
    wf_function fn ∧
    MEM v (live_vars_at st lbl idx) ⇒
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  simp[liveness_analyze_def, live_vars_at_def, df_at_def] >>
  strip_tac >>
  qabbrev_tac `result = df_analyze Backward [] list_union
    liveness_transfer liveness_edge_transfer fn.fn_blocks NONE fn` >>
  (* Show soundness invariant holds for result *)
  `liveness_sound_inv fn.fn_blocks (cfg_analyze fn) result` by
    (simp[Abbr`result`] >> metis_tac[liveness_sound_inv_result]) >>
  (* Extract inst-level soundness *)
  fs[liveness_sound_inv_def] >>
  first_x_assum (qspecl_then [`lbl`, `idx`, `v`] mp_tac) >>
  simp[df_at_def]
QED

(* ===================================================================
   Liveness completeness infrastructure
   (Fixpoint-based transfer equations for backward liveness)
   =================================================================== *)

(* Intra-block transfer: live_vars_at relates adjacent indices *)
Theorem live_vars_at_transfer:
  ∀fn lbl bb idx.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    SUC idx ≤ LENGTH bb.bb_instructions ⇒
    live_vars_at lr lbl idx =
      liveness_transfer fn.fn_blocks (EL idx bb.bb_instructions)
        (live_vars_at lr lbl (SUC idx))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  drule liveness_convergence >> simp_tac std_ss [LET_THM] >>
  fs[liveness_analyze_def] >> strip_tac >> strip_tac >>
  simp[live_vars_at_def] >>
  irule (SIMP_RULE (std_ss ++ boolSimps.LIFT_COND_ss)
    [LET_THM, direction_case_def, direction_distinct]
    (Q.SPEC `Backward` (INST_TYPE [beta |-> ``:basic_block list``]
      dfAnalyzeProofsTheory.df_at_intra_transfer_proof))) >>
  simp[]
QED

(* A variable used at instruction idx is live at idx *)
Theorem live_vars_at_uses:
  ∀fn lbl bb idx v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM v (inst_uses (EL idx bb.bb_instructions)) ⇒
    MEM v (live_vars_at lr lbl idx)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac (* wf_function *) >> strip_tac >>
  drule_then assume_tac live_vars_at_transfer >>
  pop_assum (qspecl_then [`lbl`, `bb`, `idx`] mp_tac) >>
  fs[] >> simp[liveness_transfer_def, live_update_mem]
QED

(* Backward propagation: if live at idx+1 and not killed at idx, live at idx *)
Theorem live_vars_at_propagate:
  ∀fn lbl bb idx v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    idx < LENGTH bb.bb_instructions ∧
    MEM v (live_vars_at lr lbl (SUC idx)) ∧
    ¬MEM v (inst_defs (EL idx bb.bb_instructions)) ⇒
    MEM v (live_vars_at lr lbl idx)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac (* wf_function *) >> strip_tac >>
  drule_then assume_tac live_vars_at_transfer >>
  pop_assum (qspecl_then [`lbl`, `bb`, `idx`] mp_tac) >>
  fs[] >> simp[liveness_transfer_def, live_update_mem]
QED

(* Propagate from any index j down to index i, if not killed in between *)
Theorem live_vars_at_propagate_range:
  ∀fn lbl bb i j v.
    wf_function fn ⇒
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    i ≤ j ∧ j ≤ LENGTH bb.bb_instructions ∧
    MEM v (live_vars_at lr lbl j) ∧
    (∀k. i ≤ k ∧ k < j ⇒ ¬MEM v (inst_defs (EL k bb.bb_instructions))) ⇒
    MEM v (live_vars_at lr lbl i)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  Induct_on `j - i`
  >- (rpt strip_tac >> `i = j` by DECIDE_TAC >> gvs[])
  >> rpt strip_tac >>
  `i < j` by DECIDE_TAC >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl (SUC i))` by (
    first_x_assum (qspecl_then [`j`, `SUC i`] mp_tac) >>
    impl_tac >- DECIDE_TAC >>
    disch_then irule >> simp[] >> rpt conj_tac >> TRY DECIDE_TAC >>
    rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  drule_all live_vars_at_propagate >>
  simp_tac std_ss [LET_THM] >>
  disch_then (qspecl_then [`lbl`, `bb`, `i`, `v`] mp_tac) >>
  simp[]
QED

(* ===================================================================
   Cross-block liveness transfer
   =================================================================== *)

(* FOLDL of string updates: FLOOKUP in result means in acc or in list *)
Theorem foldl_string_update_flookup[local]:
  !outs (m:string |-> num) n v i.
    FLOOKUP (FOLDL (\m w. m |+ (w, n)) m outs) v = SOME i ==>
    FLOOKUP m v = SOME i \/ MEM v outs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `h = v` >> gvs[]
QED

(* op_map in build_phi_maps: v in domain ⟹ v appears in some phi's outputs *)
Theorem build_phi_maps_op_map_mem[local]:
  !phis n acc_op acc_m src v i.
    FLOOKUP (FST (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m w. m |+ (w, j)) op_map phi.inst_outputs,
         case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_, w) => matching |+ (j, w)))
      (acc_op, acc_m) (MAPi (\k phi. (n + k, phi)) phis))) v = SOME i ==>
    FLOOKUP acc_op v = SOME i \/
    ?phi. MEM phi phis /\ MEM v phi.inst_outputs
Proof
  Induct >> simp[MAPi_def] >> rpt gen_tac >>
  simp[combinTheory.o_DEF] >>
  `MAPi (\k phi'. (n + SUC k, phi')) phis =
   MAPi (\k phi'. (SUC n + k, phi')) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >> strip_tac >>
  first_x_assum (qspecl_then [
    `SUC n`,
    `FOLDL (\m w. m |+ (w, n)) acc_op h.inst_outputs`,
    `case FIND (\(l,w). l = src) (phi_pairs h.inst_operands) of
       NONE => acc_m | SOME (_, w) => acc_m |+ (n, w)`,
    `src`, `v`, `i`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
  >- (drule foldl_string_update_flookup >> strip_tac >> gvs[] >>
      disj2_tac >> qexists_tac `h` >> simp[])
  >- (disj2_tac >> metis_tac[])
QED

Theorem build_phi_maps_op_map_char[local]:
  !src phis v i.
    FLOOKUP (FST (build_phi_maps src phis)) v = SOME i ==>
    ?phi. MEM phi phis /\ MEM v phi.inst_outputs
Proof
  rw[build_phi_maps_def, LET_THM] >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `FEMPTY`, `src`, `v`, `i`]
    mp_tac build_phi_maps_op_map_mem >> simp[]
QED

(* Non-phi-output variables pass through input_vars_from *)
Theorem input_vars_from_non_phi:
  !src_lbl instrs base v.
    MEM v base /\
    (!inst. MEM inst (collect_phis instrs) ==>
            ~MEM v inst.inst_outputs) ==>
    MEM v (input_vars_from src_lbl instrs base)
Proof
  rpt strip_tac >> simp[input_vars_from_def, LET_THM] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps src_lbl (collect_phis instrs)` >>
  rename1 `_ = (op_map, matching)` >> simp[] >>
  simp[Once UNCURRY] >>
  `FLOOKUP op_map v = NONE` by (
    Cases_on `FLOOKUP op_map v` >> simp[] >>
    `FLOOKUP (FST (build_phi_maps src_lbl (collect_phis instrs))) v = SOME x` by
      gvs[] >>
    drule build_phi_maps_op_map_char >> strip_tac >> metis_tac[]) >>
  irule foldl_passthrough >> simp[]
QED

(* Helper: element of a list in FOLDL list_union is in the result *)
Theorem foldl_list_union_mem[local]:
  !ls acc v.
    MEM v (FOLDL list_union acc ls) <=> MEM v acc \/ ?x. MEM x ls /\ MEM v x
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[list_union_mem_proof] >> metis_tac[]
QED

(* If v is in some member of a list, it's in the FOLDL list_union *)
Theorem foldl_list_union_intro[local]:
  !ls acc x v. MEM x ls /\ MEM v x ==> MEM v (FOLDL list_union acc ls)
Proof
  rpt strip_tac >> simp[foldl_list_union_mem] >> disj2_tac >>
  qexists_tac `x` >> simp[]
QED

(* Backward liveness: live at block entry ⟹ in boundary.
   Wraps df_boundary_fixpoint + list_union reasoning. *)
Theorem live_at_entry_in_boundary:
  !fn lbl bb v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (live_vars_at lr lbl 0) ==>
    MEM v (df_boundary []
      (df_analyze Backward [] list_union liveness_transfer
         liveness_edge_transfer fn.fn_blocks NONE fn) lbl)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac >> strip_tac >>
  drule liveness_convergence >> simp_tac std_ss [LET_THM] >>
  simp[liveness_analyze_def] >> strip_tac >>
  qabbrev_tac `result = df_analyze Backward [] list_union liveness_transfer
    liveness_edge_transfer fn.fn_blocks NONE fn` >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  mp_tac (INST_TYPE [alpha |-> ``:string list``,
                     beta |-> ``:basic_block list``]
    df_boundary_fixpoint) >>
  disch_then (qspecl_then [`Backward`, `[]`, `list_union`,
    `liveness_transfer`, `liveness_edge_transfer`, `fn.fn_blocks`,
    `NONE`, `fn`, `lbl`, `bb`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- gvs[Abbr `cfg`, Abbr `result`]) >>
  gvs[Abbr `cfg`, Abbr `result`] >>
  strip_tac >>
  pop_assum (fn eq => ONCE_REWRITE_TAC [eq]) >>
  simp[list_union_mem_proof] >> DISJ2_TAC >>
  gvs[live_vars_at_def, liveness_analyze_def, df_at_def]
QED

(* Helper: if v is in the edge transfer from a successor, v is in the
   backward joined value. Avoids painful case-expression handling. *)
Theorem df_joined_val_mem_backward[local]:
  !edge_transfer ctx entry_val cfg st lbl nbr bottom v.
    MEM nbr (cfg_succs_of cfg lbl) /\
    MEM v (edge_transfer ctx nbr lbl (df_boundary bottom st nbr)) ==>
    MEM v (df_joined_val Backward bottom list_union edge_transfer
      ctx entry_val cfg st lbl)
Proof
  rpt strip_tac >>
  simp[df_joined_val_def, LET_THM, direction_case_def] >>
  (* entry_val: NONE gives base, SOME adds a list_union *)
  Cases_on `entry_val` >> simp[]
  >- (
    (* NONE: result = case edge_vals of [] => bottom | _ => FOLDL ... *)
    `MEM v (FOLDL list_union bottom
      (MAP (\nbr'. edge_transfer ctx nbr' lbl (df_boundary bottom st nbr'))
           (cfg_succs_of cfg lbl)))` suffices_by (
      strip_tac >>
      Cases_on `MAP (\nbr'. edge_transfer ctx nbr' lbl
                       (df_boundary bottom st nbr'))
                    (cfg_succs_of cfg lbl)` >> gvs[]) >>
    irule foldl_list_union_intro >>
    qexists_tac `edge_transfer ctx nbr lbl (df_boundary bottom st nbr)` >>
    simp[MEM_MAP] >> qexists_tac `nbr` >> simp[])
  >- (
    (* SOME: result = if lbl = ev_lbl then list_union v' base else base *)
    PairCases_on `x` >> simp[] >>
    IF_CASES_TAC >> gvs[list_union_mem_proof] >>
    TRY DISJ2_TAC >>
    `MEM v (FOLDL list_union bottom
      (MAP (\nbr'. edge_transfer ctx nbr' lbl (df_boundary bottom st nbr'))
           (cfg_succs_of cfg lbl)))` suffices_by (
      strip_tac >>
      Cases_on `MAP (\nbr'. edge_transfer ctx nbr' lbl
                       (df_boundary bottom st nbr'))
                    (cfg_succs_of cfg lbl)` >> gvs[]) >>
    irule foldl_list_union_intro >>
    qexists_tac `edge_transfer ctx nbr lbl (df_boundary bottom st nbr)` >>
    simp[MEM_MAP] >> qexists_tac `nbr` >> simp[])
QED

(* Cross-block liveness transfer: if v is live at entry of a successor
   and v is not a phi operand variable in the successor, then v is live
   at exit of the predecessor.

   Requires succ_lbl ∈ cfg_dfs_pre (for df_boundary_fixpoint). *)
Theorem live_vars_at_cross_block:
  !fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb /\
    MEM v (live_vars_at lr succ_lbl 0) /\
    (!inst. MEM inst (collect_phis succ_bb.bb_instructions) ==>
            ~MEM v inst.inst_outputs) ==>
    MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >>
  strip_tac >> strip_tac >>
  drule liveness_convergence >> simp_tac std_ss [LET_THM] >>
  simp[liveness_analyze_def] >> strip_tac >>
  qabbrev_tac `result = df_analyze Backward [] list_union liveness_transfer
    liveness_edge_transfer fn.fn_blocks NONE fn` >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  (* Step 1: live_vars_at at block exit = joined from successors *)
  mp_tac (INST_TYPE [alpha |-> ``:string list``,
                     beta |-> ``:basic_block list``]
    df_at_inter_transfer) >>
  disch_then (qspecl_then [`Backward`, `[]`, `list_union`,
    `liveness_transfer`, `liveness_edge_transfer`, `fn.fn_blocks`,
    `NONE`, `fn`, `pred_lbl`, `pred_bb`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- gvs[Abbr `cfg`, Abbr `bbs`, Abbr `result`]) >>
  strip_tac >>
  simp[live_vars_at_def, Abbr `result`, Abbr `bbs`] >>
  pop_assum (fn eq => REWRITE_TAC [eq]) >>
  (* Step 2: v is in joined value via edge transfer from succ_lbl *)
  irule df_joined_val_mem_backward >>
  qexists_tac `succ_lbl` >> gvs[Abbr `cfg`] >>
  (* Goal: MEM v (liveness_edge_transfer bbs succ_lbl pred_lbl
                    (df_boundary [] result succ_lbl)) *)
  simp[liveness_edge_transfer_def] >>
  (* lookup_block succ_lbl bbs = SOME succ_bb *)
  irule input_vars_from_non_phi >>
  conj_tac
  >- simp[]
  >- (
    (* MEM v (df_boundary [] ... succ_lbl) via fixpoint equation *)
    drule_then (qspecl_then [`succ_lbl`, `succ_bb`, `v`] mp_tac)
      live_at_entry_in_boundary >>
    simp_tac std_ss [LET_THM] >> simp[])
QED

(* Forward propagation of "not live": if v is not live at the start of
   a range and no instruction in the range defines v, then v is not live
   at any point in the range. Contrapositive of live_vars_at_propagate_range. *)
Theorem not_live_forward_in_block:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at lr lbl i) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ~MEM v (live_vars_at lr lbl j)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  drule_then assume_tac live_vars_at_propagate_range >>
  pop_assum (qspecl_then [`lbl`, `bb`, `i`, `j`, `v`] mp_tac) >>
  simp_tac std_ss [LET_THM] >> simp[]
QED

(* Cross-block forward propagation: if v is not live at exit of a block,
   and succ has no phi output for v, then v is not live at entry of succ.
   Contrapositive of live_vars_at_cross_block. *)
Theorem not_live_cross_block:
  !fn pred_lbl pred_bb succ_lbl succ_bb v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM pred_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl cfg.cfg_dfs_pre /\
    MEM succ_lbl (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    lookup_block succ_lbl fn.fn_blocks = SOME succ_bb /\
    ~MEM v (live_vars_at lr pred_lbl (LENGTH pred_bb.bb_instructions)) /\
    (!inst. MEM inst (collect_phis succ_bb.bb_instructions) ==>
            ~MEM v inst.inst_outputs) ==>
    ~MEM v (live_vars_at lr succ_lbl 0)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  drule_then assume_tac live_vars_at_cross_block >>
  pop_assum (qspecl_then [`pred_lbl`, `pred_bb`, `succ_lbl`, `succ_bb`, `v`]
    mp_tac) >>
  simp_tac std_ss [LET_THM] >> simp[]
QED

(* Forward propagation: if v is live at position i and not killed in [i,j),
   then either v is live at j or v is used at some position in [i,j).
   Uses the transfer equality (both directions). *)
Theorem live_vars_at_forward_or_used:
  !fn lbl bb i j v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    i <= j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at lr lbl i) /\
    (!k. i <= k /\ k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    MEM v (live_vars_at lr lbl j) \/
    (?k. i <= k /\ k < j /\ MEM v (inst_uses (EL k bb.bb_instructions)))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  Induct_on `j - i` >> rpt strip_tac
  >- (`i = j` by DECIDE_TAC >> gvs[])
  >> `i < j` by DECIDE_TAC >>
  drule_then assume_tac live_vars_at_transfer >>
  pop_assum (qspecl_then [`lbl`, `bb`, `i`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- simp[]) >> strip_tac >>
  `MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
            (live_vars_at (liveness_analyze fn) lbl (SUC i)))` by
    metis_tac[] >>
  pop_assum mp_tac >> simp[liveness_transfer_def, live_update_mem] >>
  strip_tac
  >- (
    qpat_x_assum `!j i. _ = j - i ==> _`
      (qspecl_then [`j`, `SUC i`] mp_tac) >>
    simp[] >> metis_tac[DECIDE ``SUC i <= k ==> i <= k``])
  >- (disj2_tac >> qexists_tac `i` >> simp[])
QED

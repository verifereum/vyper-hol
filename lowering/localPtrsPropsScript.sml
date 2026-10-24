(*
 * Frame lemmas for local_ptrs_rel
 *
 * local_ptrs_rel (compileEnv) relates the locals in scope that are held
 * through pointer variables to Venom memory.  These lemmas say which Venom
 * steps keep it, and how a declaration or a write to a local
 * re-establishes it.
 *
 * TOP-LEVEL:
 *   mstore_keeps_val_in_memory    — an MSTORE outside a value keeps it
 *   local_ptrs_rel_frame          — kept when the pointers, allocations and
 *                                   the locals' values in memory are kept
 *   local_ptrs_rel_mem_agree      — kept by any step that keeps the pointers
 *                                   and allocations and the bytes of every
 *                                   live region
 *   local_ptrs_rel_update_var     — assigning a non-pointer variable
 *   local_ptrs_rel_fresh_not_local_ptr — a fresh compiler variable is not a
 *                                   live local's pointer
 *   local_ptrs_rel_mstore         — an MSTORE outside the live regions
 *   local_ptrs_rel_exec_alloca    — an ALLOCA, fresh or re-executed
 *   local_ptrs_rel_exec_alloca_fresh — a fresh ALLOCA gives a region
 *                                   disjoint from the live ones
 *   alloca_inv_exec_alloca        — an ALLOCA keeps alloca_inv
 *   local_ptrs_rel_alloca_disjoint — under alloca_inv, another ALLOCA's
 *                                   allocation misses every live local
 *   local_ptrs_rel_above_frontier — a range at or above vs_alloca_next
 *                                   misses every live local
 *   local_ptrs_rel_write_local    — writing a local in its own region
 *                                   (declaration, assignment, partial write)
 *   local_ptrs_rel_set_local      — declaring a local with memory unchanged
 *   fn_inst_ids_distinct_inj      — instruction ids name instructions
 *   local_ptrs_rel_push_scope, local_ptrs_rel_pop_scope — scope changes
 *
 * Helper:
 *   local_backed_frame            — local_backed under allocation growth
 *   local_ptrs_rel_inst_idx       — moving the instruction index keeps it
 *   alloca_inv_fields             — alloca_inv reads only vs_allocas and
 *                                   vs_alloca_next
 *)

Theory localPtrsProps
Ancestors
  list finite_map words
  venomMemDefs
  vyperState valueEncoding valueEncodingProps compileEnv
  venomState venomExecSemantics venomInst venomWf

(* An MSTORE outside a value's footprint keeps it. *)
Theorem mstore_keeps_val_in_memory:
  ∀ty v off ss off2 (w:bytes32).
    val_in_memory ty v off ss.vs_memory ∧ val_wf ty v ∧
    (off2 + 32 ≤ off ∨ off + type_memory_size ty ≤ off2) ⇒
    val_in_memory ty v off (mstore off2 w ss).vs_memory
Proof
  rpt strip_tac >>
  `mstore off2 w ss = mstore off2 w (ss with vs_memory := ss.vs_memory)` by
    simp[mstore_def] >>
  pop_assum SUBST1_TAC >>
  irule (CONJUNCT1 mstore_preserves_val_in_memory) >> simp[]
QED

(* A region below the old frontier stays backed when allocations are only
   added, each at or above the old frontier. *)
Theorem local_backed_frame:
  ∀func p ss ss' lo sz.
    local_backed func p ss lo sz ∧ lo + sz ≤ ss.vs_alloca_next ∧
    (∀aid r. FLOOKUP ss.vs_allocas aid = SOME r ⇒
             FLOOKUP ss'.vs_allocas aid = SOME r) ∧
    (∀aid b sz'. FLOOKUP ss'.vs_allocas aid = SOME (b, sz') ∧
                 FLOOKUP ss.vs_allocas aid = NONE ⇒
                 ss.vs_alloca_next ≤ b) ⇒
    local_backed func p ss' lo sz
Proof
  rpt strip_tac >> fs[local_backed_def]
  >- (disj1_tac >> qexists_tac `inst` >> res_tac >> simp[]) >>
  disj2_tac >> rpt strip_tac >>
  Cases_on `FLOOKUP ss.vs_allocas aid`
  >- (`ss.vs_alloca_next ≤ b` by metis_tac[] >>
      simp[regions_disjoint_def]) >>
  rename1 `FLOOKUP ss.vs_allocas aid = SOME r` >> PairCases_on `r` >>
  `FLOOKUP ss'.vs_allocas aid = SOME (r0, r1)` by res_tac >>
  gvs[] >> res_tac
QED

Theorem local_ptrs_rel_frame:
  ∀func cenv scopes ss ss'.
    local_ptrs_rel func cenv scopes ss ∧
    (∀name entry p sz.
       lookup_scopes name scopes = SOME entry ∧
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ⇒
       lookup_var p ss' = lookup_var p ss) ∧
    (∀aid r. FLOOKUP ss.vs_allocas aid = SOME r ⇒
             FLOOKUP ss'.vs_allocas aid = SOME r) ∧
    (∀aid b sz. FLOOKUP ss'.vs_allocas aid = SOME (b, sz) ∧
                FLOOKUP ss.vs_allocas aid = NONE ⇒
                ss.vs_alloca_next ≤ b) ∧
    ss.vs_alloca_next ≤ ss'.vs_alloca_next ∧
    (∀name entry p sz w.
       lookup_scopes name scopes = SOME entry ∧
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
       lookup_var p ss = SOME w ∧ w2n w + sz ≤ ss.vs_alloca_next ∧
       type_memory_size entry.type ≤ sz ∧ val_wf entry.type entry.value ∧
       val_in_memory entry.type entry.value (w2n w) ss.vs_memory ⇒
       val_in_memory entry.type entry.value (w2n w) ss'.vs_memory) ⇒
    local_ptrs_rel func cenv scopes ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def, local_region_def]) >>
  rewrite_tac[local_ptrs_rel_def, local_region_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `∀name entry p sz. P name entry p sz ⇒
                    lookup_var p ss' = lookup_var p ss`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_assum `∀name entry p sz. P name entry p sz ⇒ ∃w. Q name entry p sz w`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `w` >> rpt conj_tac
      >- simp[]
      >- (irule local_backed_frame >> qexists_tac `ss` >> rpt conj_tac >>
          FIRST [first_assum ACCEPT_TAC, simp[]])
      >- (irule arithmeticTheory.LESS_EQ_TRANS >>
          qexists_tac `ss.vs_alloca_next` >> simp[])
      >- simp[]
      >- simp[] >>
      qpat_x_assum `∀name entry p sz w. P name entry p sz w ⇒ Q name entry p sz w`
        (qspecl_then [`name`, `entry`, `p`, `sz`, `w`] mp_tac) >>
      simp[]) >>
  rpt strip_tac >>
  `lookup_var p ss = SOME w ∧ lookup_var p' ss = SOME w'` by
    (conj_tac
     >- (qpat_assum `∀name entry p sz. P name entry p sz ⇒
                       lookup_var p ss' = lookup_var p ss`
           (qspecl_then [`n1`, `entry`, `p`, `sz1`] mp_tac) >> simp[]) >>
     qpat_assum `∀name entry p sz. P name entry p sz ⇒
                   lookup_var p ss' = lookup_var p ss`
       (qspecl_then [`n2`, `entry'`, `p'`, `sz2`] mp_tac) >> simp[]) >>
  qpat_x_assum `∀n1 n2 b1 sz1 b2 sz2. P n1 n2 b1 sz1 b2 sz2 ⇒
                  regions_disjoint b1 sz1 b2 sz2` irule >>
  qexistsl_tac [`n1`, `n2`] >> rpt conj_tac >>
  FIRST [simp[] >> NO_TAC,
         qexistsl_tac [`entry`, `p`, `w`] >> simp[] >> NO_TAC,
         qexistsl_tac [`entry'`, `p'`, `w'`] >> simp[] >> NO_TAC]
QED

(* Any step that keeps the live pointers, only adds allocations at or above
   the frontier, and keeps the bytes of every live region keeps the
   relation: MSTORE, MCOPY, CALLDATACOPY, RETURNDATACOPY or a callee's writes
   outside the live regions. *)
Theorem local_ptrs_rel_mem_agree:
  ∀func cenv scopes ss ss'.
    local_ptrs_rel func cenv scopes ss ∧
    (∀name entry p sz.
       lookup_scopes name scopes = SOME entry ∧
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ⇒
       lookup_var p ss' = lookup_var p ss) ∧
    (∀aid r. FLOOKUP ss.vs_allocas aid = SOME r ⇒
             FLOOKUP ss'.vs_allocas aid = SOME r) ∧
    (∀aid b sz. FLOOKUP ss'.vs_allocas aid = SOME (b, sz) ∧
                FLOOKUP ss.vs_allocas aid = NONE ⇒
                ss.vs_alloca_next ≤ b) ∧
    ss.vs_alloca_next ≤ ss'.vs_alloca_next ∧
    (∀name b sz. local_region cenv scopes ss name b sz ⇒
                 mem_bytes_at b sz ss.vs_memory =
                 mem_bytes_at b sz ss'.vs_memory) ⇒
    local_ptrs_rel func cenv scopes ss'
Proof
  rpt strip_tac >> irule local_ptrs_rel_frame >> qexists_tac `ss` >>
  rpt conj_tac >~ [`val_in_memory`]
  >- (rpt strip_tac >> irule val_in_memory_mem_agree >>
      simp[] >> qexistsl_tac [`sz`, `ss.vs_memory`] >> simp[] >>
      first_x_assum irule >> simp[local_region_def] >>
      qexistsl_tac [`name`, `entry`, `p`] >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem local_ptrs_rel_update_var:
  ∀func cenv scopes ss x v.
    local_ptrs_rel func cenv scopes ss ∧ not_local_ptr cenv scopes x ⇒
    local_ptrs_rel func cenv scopes (update_var x v ss)
Proof
  rpt strip_tac >> irule local_ptrs_rel_frame >> qexists_tac `ss` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> fs[not_local_ptr_def] >> res_tac >> fs[]
QED

Theorem local_ptrs_rel_inst_idx:
  !func cenv sc s n.
    local_ptrs_rel func cenv sc (s with vs_inst_idx := n) <=>
    local_ptrs_rel func cenv sc s
Proof
  simp[local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def]
QED

(* A variable the compiler has not handed out yet is unbound in Venom, so it
   is no live local's pointer. *)
Theorem local_ptrs_rel_fresh_not_local_ptr:
  ∀func cenv scopes st ss n.
    local_ptrs_rel func cenv scopes ss ∧ fresh_vars_wrt st ss ∧
    n ≥ st.cs_next_var ⇒
    not_local_ptr cenv scopes (STRING #"%" (toString n))
Proof
  rw[not_local_ptr_def] >> strip_tac >>
  fs[local_ptrs_rel_def, fresh_vars_wrt_def] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >> fs[lookup_var_def, FLOOKUP_DEF]
QED

Theorem local_ptrs_rel_mstore:
  ∀func cenv scopes ss off (v:bytes32).
    local_ptrs_rel func cenv scopes ss ∧
    (∀name b sz. local_region cenv scopes ss name b sz ⇒
                 off + 32 ≤ b ∨ b + sz ≤ off) ⇒
    local_ptrs_rel func cenv scopes (mstore off v ss)
Proof
  rpt strip_tac >>
  `(mstore off v ss).vs_vars = ss.vs_vars ∧
   (mstore off v ss).vs_allocas = ss.vs_allocas ∧
   (mstore off v ss).vs_alloca_next = ss.vs_alloca_next` by
    simp[mstore_def, LET_THM] >>
  irule local_ptrs_rel_mem_agree >> qexists_tac `ss` >>
  simp[lookup_var_def] >> rpt strip_tac >~ [`mem_bytes_at`]
  >- (irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >>
      `off + 32 ≤ b ∨ b + sz ≤ off` by (first_x_assum irule >> metis_tac[]) >>
      simp[]) >>
  fs[]
QED

(* Fresh or re-executed: an ALLOCA writes only its output variable and adds
   at most an allocation at the frontier. *)
Theorem local_ptrs_rel_exec_alloca:
  ∀func cenv scopes ss ss' inst x asz.
    exec_alloca inst ss asz = OK ss' ∧ inst.inst_outputs = [x] ∧
    local_ptrs_rel func cenv scopes ss ∧ not_local_ptr cenv scopes x ⇒
    local_ptrs_rel func cenv scopes ss'
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP ss.vs_allocas inst.inst_id`
  >- (gvs[exec_alloca_def, LET_THM] >>
      irule local_ptrs_rel_update_var >> simp[] >>
      irule local_ptrs_rel_frame >> qexists_tac `ss` >>
      simp[lookup_var_def, FLOOKUP_UPDATE] >> rw[] >> gvs[]) >>
  rename1 `FLOOKUP _ _ = SOME pr` >> Cases_on `pr` >>
  gvs[exec_alloca_def, LET_THM] >>
  irule local_ptrs_rel_update_var >> simp[]
QED

(* A fresh ALLOCA binds its output to the frontier: a region of the
   requested size, recorded in vs_allocas, disjoint from every live local. *)
Theorem local_ptrs_rel_exec_alloca_fresh:
  ∀func cenv scopes ss ss' inst x asz.
    exec_alloca inst ss asz = OK ss' ∧ inst.inst_outputs = [x] ∧
    FLOOKUP ss.vs_allocas inst.inst_id = NONE ∧
    ss.vs_alloca_next < dimword (:256) ∧
    local_ptrs_rel func cenv scopes ss ∧ not_local_ptr cenv scopes x ⇒
    local_ptrs_rel func cenv scopes ss' ∧
    ∃w. lookup_var x ss' = SOME w ∧ w2n w = ss.vs_alloca_next ∧
        FLOOKUP ss'.vs_allocas inst.inst_id = SOME (w2n w, w2n asz) ∧
        w2n w + w2n asz ≤ ss'.vs_alloca_next ∧
        ∀name b sz. local_region cenv scopes ss' name b sz ⇒
                    regions_disjoint (w2n w) (w2n asz) b sz
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (n2w ss.vs_alloca_next : bytes32) = ss.vs_alloca_next` by
    (rewrite_tac[w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- (drule_all local_ptrs_rel_exec_alloca >> simp[]) >>
  gvs[exec_alloca_def, LET_THM] >>
  qexists_tac `n2w ss.vs_alloca_next` >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rw[local_region_def, regions_disjoint_def] >>
  fs[lookup_var_def, FLOOKUP_UPDATE] >>
  `p ≠ x` by
    (strip_tac >> fs[not_local_ptr_def] >> res_tac >> fs[]) >>
  fs[] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  qpat_x_assum `∀name entry p sz. P name entry p sz ⇒ ∃w. Q name entry p sz w`
    drule_all >>
  strip_tac >> gvs[lookup_var_def]
QED

(* Bump allocation keeps recorded allocations pairwise disjoint and below
   the frontier. *)
Theorem alloca_inv_exec_alloca:
  ∀inst ss ss' asz.
    exec_alloca inst ss asz = OK ss' ∧ alloca_inv ss ⇒ alloca_inv ss'
Proof
  rpt strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs(), LET_THM] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     update_var_def, FLOOKUP_UPDATE] >>
  rw[] >> res_tac >> fs[]
QED

Theorem alloca_inv_fields:
  !s s'.
    alloca_inv s /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next ==> alloca_inv s'
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

(* Instruction ids of a function name its instructions. *)
Theorem fn_inst_ids_distinct_inj:
  ∀func i1 i2.
    fn_inst_ids_distinct func ∧ MEM i1 (fn_insts func) ∧
    MEM i2 (fn_insts func) ∧ i1.inst_id = i2.inst_id ⇒ i1 = i2
Proof
  rpt strip_tac >>
  `∀bbs. MAP (λi. i.inst_id) (fn_insts_blocks bbs) =
         FLAT (MAP (λbb. MAP (λi. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
  `ALL_DISTINCT (MAP (λi. i.inst_id) (fn_insts func))` by
    fs[fn_inst_ids_distinct_def, fn_insts_def] >>
  fs[MEM_EL] >> rename1 `i2 = EL m _` >>
  `EL n (MAP (λi. i.inst_id) (fn_insts func)) =
   EL m (MAP (λi. i.inst_id) (fn_insts func))` by gvs[EL_MAP] >>
  `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]
QED

(* An allocation of another instruction of func, one whose output is no
   live local's pointer, misses every live local: the step a consumer needs
   to write into a re-executed temporary (compile_alloc_buffer in a loop, an
   internal call's return buffer) or to re-declare a local whose ALLOCA ran
   before (a loop body). *)
Theorem local_ptrs_rel_alloca_disjoint:
  ∀func cenv scopes ss inst q b asz name lo sz.
    alloca_inv ss ∧ fn_inst_ids_distinct func ∧
    local_ptrs_rel func cenv scopes ss ∧
    MEM inst (fn_insts func) ∧ inst.inst_outputs = [q] ∧
    not_local_ptr cenv scopes q ∧
    FLOOKUP ss.vs_allocas inst.inst_id = SOME (b, asz) ∧
    local_region cenv scopes ss name lo sz ⇒
    regions_disjoint b asz lo sz
Proof
  rw[local_region_def] >>
  `q ≠ p` by (strip_tac >> gvs[not_local_ptr_def] >> res_tac) >>
  fs[local_ptrs_rel_def] >> first_x_assum drule_all >> strip_tac >>
  gvs[local_backed_def]
  >- (rename1 `inst'.inst_outputs = [p]` >>
      `inst ≠ inst'` by (strip_tac >> gvs[]) >>
      `inst.inst_id ≠ inst'.inst_id` by metis_tac[fn_inst_ids_distinct_inj] >>
      fs[alloca_inv_def, allocas_non_overlapping_def, regions_disjoint_def] >>
      first_x_assum (qspecl_then [`inst.inst_id`, `inst'.inst_id`, `b`, `asz`,
                                  `w2n w`, `sz`] mp_tac) >>
      simp[]) >>
  first_x_assum drule >> simp[regions_disjoint_def] >> DECIDE_TAC
QED

(* A range starting at or above the frontier misses every live local: the
   consumer's route for writes into DALLOCA/FMP buffers.  It needs
   vs_alloca_next ≤ off at each such write, and the frontier only grows (each
   internal call allocates its frame afresh, also inside loops), so this
   takes an invariant that keeps the frontier below the DALLOCA area at every
   step, not a fact about the entry state. *)
Theorem local_ptrs_rel_above_frontier:
  ∀func cenv scopes ss name lo sz off len.
    local_ptrs_rel func cenv scopes ss ∧
    local_region cenv scopes ss name lo sz ∧
    ss.vs_alloca_next ≤ off ⇒
    regions_disjoint lo sz off len
Proof
  rw[local_region_def, local_ptrs_rel_def, regions_disjoint_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

(* The disjointness half of local_ptrs_rel_write_local. *)
Theorem write_local_disjoint[local]:
  ∀cenv scopes scopes' ss ss' name sz w.
    (∀n1 n2 b1 sz1 b2 sz2.
       n1 ≠ n2 ∧ local_region cenv scopes ss n1 b1 sz1 ∧
       local_region cenv scopes ss n2 b2 sz2 ⇒
       regions_disjoint b1 sz1 b2 sz2) ∧
    (∀n b sz'. n ≠ name ⇒
       (local_region cenv scopes' ss' n b sz' ⇔
        local_region cenv scopes ss n b sz')) ∧
    (∀b sz'. local_region cenv scopes' ss' name b sz' ⇒ b = w2n w ∧ sz' = sz) ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               regions_disjoint (w2n w) sz b sz') ⇒
    ∀n1 n2 b1 sz1 b2 sz2.
      n1 ≠ n2 ∧ local_region cenv scopes' ss' n1 b1 sz1 ∧
      local_region cenv scopes' ss' n2 b2 sz2 ⇒
      regions_disjoint b1 sz1 b2 sz2
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  Cases_on `n1 = name` >> Cases_on `n2 = name` >> fs[]
  >- (`local_region cenv scopes ss n2 b2 sz2` by
        (qpat_x_assum `local_region cenv scopes' ss' n2 b2 sz2` mp_tac >> simp[]) >>
      qpat_assum `∀b sz'. local_region cenv scopes' ss' name b sz' ⇒ Q b sz'`
        (fn th => drule th) >> strip_tac >> fs[] >>
      qpat_x_assum `∀n b sz'. P n b sz' ⇒ regions_disjoint (w2n w) sz b sz'`
        irule >>
      qexists_tac `n2` >> simp[])
  >- (`local_region cenv scopes ss n1 b1 sz1` by
        (qpat_x_assum `local_region cenv scopes' ss' n1 b1 sz1` mp_tac >> simp[]) >>
      qpat_assum `∀b sz'. local_region cenv scopes' ss' name b sz' ⇒ Q b sz'`
        (fn th => drule th) >> strip_tac >> fs[] >>
      `regions_disjoint (w2n w) sz b1 sz1` by
        (qpat_x_assum `∀n b sz'. P n b sz' ⇒ regions_disjoint (w2n w) sz b sz'`
           irule >>
         qexists_tac `n1` >> simp[]) >>
      fs[regions_disjoint_def] >> DECIDE_TAC) >>
  `local_region cenv scopes ss n1 b1 sz1 ∧ local_region cenv scopes ss n2 b2 sz2` by
    (conj_tac
     >- (qpat_x_assum `local_region cenv scopes' ss' n1 b1 sz1` mp_tac >> simp[]) >>
     qpat_x_assum `local_region cenv scopes' ss' n2 b2 sz2` mp_tac >> simp[]) >>
  qpat_x_assum `∀n1 n2 b1 sz1 b2 sz2. P n1 n2 b1 sz1 b2 sz2 ⇒
                  regions_disjoint b1 sz1 b2 sz2` irule >>
  qexistsl_tac [`n1`, `n2`] >> simp[]
QED

(* write_local with the variables and allocations unchanged. *)
Theorem write_local_same_frame[local]:
  ∀func cenv scopes scopes' ss ss' name entry p sz w.
    local_ptrs_rel func cenv scopes ss ∧
    lookup_scopes name scopes' = SOME entry ∧
    (∀n. n ≠ name ⇒ lookup_scopes n scopes' = lookup_scopes n scopes) ∧
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
    lookup_var p ss = SOME w ∧ local_backed func p ss (w2n w) sz ∧
    w2n w + sz ≤ ss.vs_alloca_next ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               regions_disjoint (w2n w) sz b sz') ∧
    ss'.vs_vars = ss.vs_vars ∧ ss'.vs_allocas = ss.vs_allocas ∧
    ss'.vs_alloca_next = ss.vs_alloca_next ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               mem_bytes_at b sz' ss.vs_memory =
               mem_bytes_at b sz' ss'.vs_memory) ∧
    type_memory_size entry.type ≤ sz ∧ val_wf entry.type entry.value ∧
    val_in_memory entry.type entry.value (w2n w) ss'.vs_memory ⇒
    local_ptrs_rel func cenv scopes' ss'
Proof
  rpt gen_tac >> strip_tac >>
  `(∀x. lookup_var x ss' = lookup_var x ss) ∧
   (∀q b sz'. local_backed func q ss' b sz' ⇔ local_backed func q ss b sz')` by
    simp[lookup_var_def, local_backed_def] >>
  `∀n b sz'. n ≠ name ⇒
     (local_region cenv scopes' ss' n b sz' ⇔
      local_region cenv scopes ss n b sz')` by
    (rpt strip_tac >> simp[local_region_def]) >>
  `∀b sz'. local_region cenv scopes' ss' name b sz' ⇒ b = w2n w ∧ sz' = sz` by
    (rw[local_region_def] >> gvs[]) >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  rewrite_tac[local_ptrs_rel_def] >> conj_tac
  >- (rpt strip_tac >>
      Cases_on `name' = name`
      >- (gvs[] >> qexists_tac `w` >> simp[]) >>
      `lookup_scopes name' scopes = SOME entry'` by
        (qpat_x_assum `∀n. P n ⇒ lookup_scopes n scopes' = lookup_scopes n scopes`
           (qspec_then `name'` mp_tac) >> simp[]) >>
      qpat_x_assum `∀name entry p sz. P name entry p sz ⇒ ∃w. Q name entry p sz w`
        drule_all >>
      strip_tac >> qexists_tac `w'` >> simp[] >>
      irule val_in_memory_mem_agree >>
      simp[] >> qexistsl_tac [`sz'`, `ss.vs_memory`] >> simp[] >>
      first_x_assum irule >> qexists_tac `name'` >>
      REWRITE_TAC[local_region_def] >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`entry'`, `p'`, `w'`] >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  qspecl_then [`cenv`, `scopes`, `scopes'`, `ss`, `ss'`, `name`, `sz`, `w`]
    mp_tac write_local_disjoint >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* Writing a local: the scopes change only at name, the memory keeps the
   bytes of the other live locals' regions, and the new entry is held in
   name's region, disjoint from the other live locals.  Covers a declaration
   (name not live before), an assignment, an augmented assignment and a
   partial write such as x[i] = e (name live, old value overwritten). *)
Theorem local_ptrs_rel_write_local:
  ∀func cenv scopes scopes' ss ss' name entry p sz w.
    local_ptrs_rel func cenv scopes ss ∧
    lookup_scopes name scopes' = SOME entry ∧
    (∀n. n ≠ name ⇒ lookup_scopes n scopes' = lookup_scopes n scopes) ∧
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
    lookup_var p ss = SOME w ∧ local_backed func p ss (w2n w) sz ∧
    w2n w + sz ≤ ss.vs_alloca_next ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               regions_disjoint (w2n w) sz b sz') ∧
    (∀n e q sq.
       lookup_scopes n scopes' = SOME e ∧
       FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) sq) ⇒
       lookup_var q ss' = lookup_var q ss) ∧
    (∀aid r. FLOOKUP ss.vs_allocas aid = SOME r ⇒
             FLOOKUP ss'.vs_allocas aid = SOME r) ∧
    (∀aid b sb. FLOOKUP ss'.vs_allocas aid = SOME (b, sb) ∧
                FLOOKUP ss.vs_allocas aid = NONE ⇒
                ss.vs_alloca_next ≤ b) ∧
    ss.vs_alloca_next ≤ ss'.vs_alloca_next ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               mem_bytes_at b sz' ss.vs_memory =
               mem_bytes_at b sz' ss'.vs_memory) ∧
    type_memory_size entry.type ≤ sz ∧ val_wf entry.type entry.value ∧
    val_in_memory entry.type entry.value (w2n w) ss'.vs_memory ⇒
    local_ptrs_rel func cenv scopes' ss'
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv scopes' (ss with vs_memory := ss'.vs_memory)` by
    (irule write_local_same_frame >>
     qexistsl_tac [`entry`, `name`, `p`, `scopes`, `ss`, `sz`, `w`] >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
            simp[] >> first_assum ACCEPT_TAC]) >>
  irule local_ptrs_rel_frame >>
  qexists_tac `ss with vs_memory := ss'.vs_memory` >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC,
         simp[] >> first_assum ACCEPT_TAC,
         rpt strip_tac >>
         qpat_x_assum `∀n e q sq. P n e q sq ⇒ lookup_var q ss' = lookup_var q ss`
           drule_all >>
         simp[lookup_var_def]]
QED

(* Declaring a local whose value is already in its region: the scopes change
   only at name, memory is unchanged.  A declaration followed by stores into
   the region, or any write to a live local, goes through
   local_ptrs_rel_write_local. *)
Theorem local_ptrs_rel_set_local:
  ∀func cenv scopes scopes' ss name entry p sz w.
    local_ptrs_rel func cenv scopes ss ∧
    lookup_scopes name scopes' = SOME entry ∧
    (∀n. n ≠ name ⇒ lookup_scopes n scopes' = lookup_scopes n scopes) ∧
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
    lookup_var p ss = SOME w ∧ local_backed func p ss (w2n w) sz ∧
    w2n w + sz ≤ ss.vs_alloca_next ∧
    type_memory_size entry.type ≤ sz ∧ val_wf entry.type entry.value ∧
    val_in_memory entry.type entry.value (w2n w) ss.vs_memory ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               regions_disjoint (w2n w) sz b sz') ⇒
    local_ptrs_rel func cenv scopes' ss
Proof
  rpt strip_tac >> irule local_ptrs_rel_write_local >>
  qexistsl_tac [`entry`, `name`, `p`, `scopes`, `ss`, `sz`, `w`] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, rpt strip_tac >> fs[]]
QED

Theorem local_ptrs_rel_push_scope:
  ∀func cenv scopes ss.
    local_ptrs_rel func cenv (FEMPTY::scopes) ss ⇔ local_ptrs_rel func cenv scopes ss
Proof
  simp[local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

(* Popping a scope that shadows nothing keeps the relation.  Vyper rejects
   shadowing, but nothing in semantics/prop carries that as an invariant of
   the scope stack yet, so the consumer has to supply one. *)
Theorem local_ptrs_rel_pop_scope:
  ∀func cenv sc scopes ss.
    local_ptrs_rel func cenv (sc::scopes) ss ∧
    (∀n. n ∈ FDOM sc ⇒ lookup_scopes n scopes = NONE) ⇒
    local_ptrs_rel func cenv scopes ss
Proof
  rpt strip_tac >>
  `∀n e. lookup_scopes n scopes = SOME e ⇒
         lookup_scopes n (sc::scopes) = SOME e` by
    (rw[lookup_scopes_def] >> Cases_on `FLOOKUP sc n` >> gvs[FLOOKUP_DEF] >>
     res_tac >> gvs[]) >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def, local_region_def]) >>
  rewrite_tac[local_ptrs_rel_def, local_region_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `∀name entry p sz. P name entry p sz ⇒ ∃w. Q name entry p sz w`
        irule >>
      qexists_tac `name` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `∀n1 n2 b1 sz1 b2 sz2. P n1 n2 b1 sz1 b2 sz2 ⇒
                  regions_disjoint b1 sz1 b2 sz2` irule >>
  qexistsl_tac [`n1`, `n2`] >> rpt conj_tac >>
  FIRST [simp[] >> NO_TAC,
         qexistsl_tac [`entry`, `p`, `w`] >> simp[] >> NO_TAC,
         qexistsl_tac [`entry'`, `p'`, `w'`] >> simp[] >> NO_TAC]
QED

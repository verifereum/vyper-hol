(*
 * Frame lemmas for local_ptrs_rel
 *
 * local_ptrs_rel (compileEnv) relates the locals in scope that are held
 * through ALLOCA'd pointer variables to Venom memory.  These lemmas say
 * which Venom steps keep it, and how a declaration or assignment
 * re-establishes it.
 *
 * TOP-LEVEL:
 *   mstore_keeps_val_in_memory    — an MSTORE outside a value keeps it
 *   local_ptrs_rel_frame          — kept when the pointers, allocations and
 *                                   the locals' memory are kept
 *   local_ptrs_rel_update_var     — assigning a non-pointer variable
 *   local_ptrs_rel_mstore         — an MSTORE outside the live regions
 *   local_ptrs_rel_exec_alloca    — an ALLOCA, fresh or re-executed
 *   local_ptrs_rel_exec_alloca_fresh — a fresh ALLOCA gives a region
 *                                   disjoint from the live ones
 *   local_ptrs_rel_set_local      — declaring or assigning a local
 *   local_ptrs_rel_push_scope, local_ptrs_rel_pop_scope — scope changes
 *)

Theory localPtrsProps
Ancestors
  list finite_map words
  vyperState valueEncoding valueEncodingProps compileEnv
  venomState venomExecSemantics

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

Theorem local_ptrs_rel_frame:
  ∀cenv scopes ss ss'.
    local_ptrs_rel cenv scopes ss ∧
    (∀name entry p sz.
       lookup_scopes name scopes = SOME entry ∧
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ⇒
       lookup_var p ss' = lookup_var p ss) ∧
    (∀aid r. FLOOKUP ss.vs_allocas aid = SOME r ⇒
             FLOOKUP ss'.vs_allocas aid = SOME r) ∧
    ss.vs_alloca_next ≤ ss'.vs_alloca_next ∧
    (∀name entry p sz w.
       lookup_scopes name scopes = SOME entry ∧
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
       lookup_var p ss = SOME w ∧ w2n w + sz ≤ ss.vs_alloca_next ∧
       type_memory_size entry.type ≤ sz ∧ val_wf entry.type entry.value ∧
       val_in_memory entry.type entry.value (w2n w) ss.vs_memory ⇒
       val_in_memory entry.type entry.value (w2n w) ss'.vs_memory) ⇒
    local_ptrs_rel cenv scopes ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def, local_region_def]) >>
  rewrite_tac[local_ptrs_rel_def, local_region_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `∀name entry p sz. P name entry p sz ⇒
                    lookup_var p ss' = lookup_var p ss`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_assum `∀name entry p sz. P name entry p sz ⇒
                    ∃w aid. Q name entry p sz w aid`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`w`, `aid`] >> rpt conj_tac
      >- simp[]
      >- (qpat_x_assum `∀aid r. P aid r ⇒ Q aid r` irule >> simp[])
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

Theorem local_ptrs_rel_update_var:
  ∀cenv scopes ss x v.
    local_ptrs_rel cenv scopes ss ∧ not_local_ptr cenv scopes x ⇒
    local_ptrs_rel cenv scopes (update_var x v ss)
Proof
  rpt strip_tac >> irule local_ptrs_rel_frame >> qexists_tac `ss` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> fs[not_local_ptr_def] >> res_tac >> fs[]
QED

Theorem local_ptrs_rel_mstore:
  ∀cenv scopes ss off (v:bytes32).
    local_ptrs_rel cenv scopes ss ∧
    (∀name b sz. local_region cenv scopes ss name b sz ⇒
                 off + 32 ≤ b ∨ b + sz ≤ off) ⇒
    local_ptrs_rel cenv scopes (mstore off v ss)
Proof
  rpt strip_tac >>
  `(mstore off v ss).vs_vars = ss.vs_vars ∧
   (mstore off v ss).vs_allocas = ss.vs_allocas ∧
   (mstore off v ss).vs_alloca_next = ss.vs_alloca_next` by
    simp[mstore_def, LET_THM] >>
  irule local_ptrs_rel_frame >> qexists_tac `ss` >>
  simp[lookup_var_def] >> rpt strip_tac >>
  irule mstore_keeps_val_in_memory >> simp[] >>
  `off + 32 ≤ w2n w ∨ w2n w + sz ≤ off` by
    (qpat_x_assum `∀name b sz. local_region _ _ _ name b sz ⇒ P name b sz`
       irule >>
     qexists_tac `name` >> simp[local_region_def, lookup_var_def] >>
     qexistsl_tac [`entry`, `p`, `w`] >> simp[]) >>
  pop_assum strip_assume_tac >- simp[] >>
  disj2_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `w2n w + sz` >> simp[]
QED

(* Fresh or re-executed: an ALLOCA writes only its output variable and adds
   at most an allocation above the frontier. *)
Theorem local_ptrs_rel_exec_alloca:
  ∀cenv scopes ss ss' inst x asz.
    exec_alloca inst ss asz = OK ss' ∧ inst.inst_outputs = [x] ∧
    local_ptrs_rel cenv scopes ss ∧ not_local_ptr cenv scopes x ⇒
    local_ptrs_rel cenv scopes ss'
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
  ∀cenv scopes ss ss' inst x asz.
    exec_alloca inst ss asz = OK ss' ∧ inst.inst_outputs = [x] ∧
    FLOOKUP ss.vs_allocas inst.inst_id = NONE ∧
    ss.vs_alloca_next < dimword (:256) ∧
    local_ptrs_rel cenv scopes ss ∧ not_local_ptr cenv scopes x ⇒
    local_ptrs_rel cenv scopes ss' ∧
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
  qpat_x_assum `local_ptrs_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  qpat_x_assum `∀name entry p sz. P name entry p sz ⇒
                  ∃w aid. Q name entry p sz w aid` drule_all >>
  strip_tac >> gvs[lookup_var_def]
QED

(* Declaring or assigning a local: the scopes change only at name, and the
   new entry is held in its pointer's region, disjoint from the other live
   locals. *)
Theorem local_ptrs_rel_set_local:
  ∀cenv scopes scopes' ss name entry p sz w aid.
    local_ptrs_rel cenv scopes ss ∧
    lookup_scopes name scopes' = SOME entry ∧
    (∀n. n ≠ name ⇒ lookup_scopes n scopes' = lookup_scopes n scopes) ∧
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ∧
    lookup_var p ss = SOME w ∧
    FLOOKUP ss.vs_allocas aid = SOME (w2n w, sz) ∧
    w2n w + sz ≤ ss.vs_alloca_next ∧
    type_memory_size entry.type ≤ sz ∧ val_wf entry.type entry.value ∧
    val_in_memory entry.type entry.value (w2n w) ss.vs_memory ∧
    (∀n b sz'. n ≠ name ∧ local_region cenv scopes ss n b sz' ⇒
               regions_disjoint (w2n w) sz b sz') ⇒
    local_ptrs_rel cenv scopes' ss
Proof
  rpt gen_tac >> strip_tac >>
  `∀n b sz'. n ≠ name ⇒
     (local_region cenv scopes' ss n b sz' ⇔
      local_region cenv scopes ss n b sz')` by
    (rpt strip_tac >> simp[local_region_def]) >>
  `∀b sz'. local_region cenv scopes' ss name b sz' ⇒ b = w2n w ∧ sz' = sz` by
    (rw[local_region_def] >> gvs[]) >>
  qpat_x_assum `local_ptrs_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
  rewrite_tac[local_ptrs_rel_def] >> conj_tac
  >- (rpt strip_tac >>
      Cases_on `name' = name`
      >- (gvs[] >>
          FIRST [qexistsl_tac [`w`, `aid`] >> simp[] >> NO_TAC,
                 qexists_tac `aid` >> simp[]]) >>
      `lookup_scopes name' scopes = SOME entry'` by
        (qpat_x_assum `∀n. P n ⇒ lookup_scopes n scopes' = lookup_scopes n scopes`
           (qspec_then `name'` mp_tac) >> simp[]) >>
      qpat_x_assum `∀name entry p sz. P name entry p sz ⇒
                      ∃w aid. Q name entry p sz w aid` drule_all >>
      simp[]) >>
  rpt strip_tac >>
  Cases_on `n1 = name` >> Cases_on `n2 = name` >> fs[]
  >- (`local_region cenv scopes ss n2 b2 sz2` by
        (qpat_x_assum `local_region cenv scopes' ss n2 b2 sz2` mp_tac >> simp[]) >>
      qpat_assum `∀b sz'. local_region cenv scopes' ss name b sz' ⇒ Q b sz'`
        (fn th => drule th) >> strip_tac >> fs[] >>
      qpat_x_assum `∀n b sz'. P n b sz' ⇒ regions_disjoint (w2n w) sz b sz'`
        irule >>
      qexists_tac `n2` >> simp[])
  >- (`local_region cenv scopes ss n1 b1 sz1` by
        (qpat_x_assum `local_region cenv scopes' ss n1 b1 sz1` mp_tac >> simp[]) >>
      qpat_assum `∀b sz'. local_region cenv scopes' ss name b sz' ⇒ Q b sz'`
        (fn th => drule th) >> strip_tac >> fs[] >>
      `regions_disjoint (w2n w) sz b1 sz1` by
        (qpat_x_assum `∀n b sz'. P n b sz' ⇒ regions_disjoint (w2n w) sz b sz'`
           irule >>
         qexists_tac `n1` >> simp[]) >>
      fs[regions_disjoint_def] >> DECIDE_TAC) >>
  `local_region cenv scopes ss n1 b1 sz1 ∧ local_region cenv scopes ss n2 b2 sz2` by
    (conj_tac
     >- (qpat_x_assum `local_region cenv scopes' ss n1 b1 sz1` mp_tac >> simp[]) >>
     qpat_x_assum `local_region cenv scopes' ss n2 b2 sz2` mp_tac >> simp[]) >>
  qpat_x_assum `∀n1 n2 b1 sz1 b2 sz2. P n1 n2 b1 sz1 b2 sz2 ⇒
                  regions_disjoint b1 sz1 b2 sz2` irule >>
  qexistsl_tac [`n1`, `n2`] >> simp[]
QED

Theorem local_ptrs_rel_push_scope:
  ∀cenv scopes ss.
    local_ptrs_rel cenv (FEMPTY::scopes) ss ⇔ local_ptrs_rel cenv scopes ss
Proof
  simp[local_ptrs_rel_def, local_region_def, lookup_scopes_def]
QED

(* Popping a scope that shadows nothing keeps the relation. *)
Theorem local_ptrs_rel_pop_scope:
  ∀cenv sc scopes ss.
    local_ptrs_rel cenv (sc::scopes) ss ∧
    (∀n. n ∈ FDOM sc ⇒ lookup_scopes n scopes = NONE) ⇒
    local_ptrs_rel cenv scopes ss
Proof
  rpt strip_tac >>
  `∀n e. lookup_scopes n scopes = SOME e ⇒
         lookup_scopes n (sc::scopes) = SOME e` by
    (rw[lookup_scopes_def] >> Cases_on `FLOOKUP sc n` >> gvs[FLOOKUP_DEF] >>
     res_tac >> gvs[]) >>
  qpat_x_assum `local_ptrs_rel _ _ _`
    (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def, local_region_def]) >>
  rewrite_tac[local_ptrs_rel_def, local_region_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `∀name entry p sz. P name entry p sz ⇒
                      ∃w aid. Q name entry p sz w aid` irule >>
      qexists_tac `name` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `∀n1 n2 b1 sz1 b2 sz2. P n1 n2 b1 sz1 b2 sz2 ⇒
                  regions_disjoint b1 sz1 b2 sz2` irule >>
  qexistsl_tac [`n1`, `n2`] >> rpt conj_tac >>
  FIRST [simp[] >> NO_TAC,
         qexistsl_tac [`entry`, `p`, `w`] >> simp[] >> NO_TAC,
         qexistsl_tac [`entry'`, `p'`, `w'`] >> simp[] >> NO_TAC]
QED

(*
 * Internal calls: the caller's live regions survive the call (#638)
 *
 * A returning INVOKE gives the caller merge_callee_state: the caller's
 * variables, vs_allocas and vs_alloca_next, with the callee's memory.  The
 * caller's live locals (local_ptrs_rel) sit in regions below the caller's
 * allocation frontier, and setup_callee starts the callee at that frontier
 * with no allocations, so every allocation the callee makes, its own and
 * its callees', is at or above it.  The caller's live regions therefore
 * survive the call when the callee changes no byte below that frontier
 * outside the buffers the caller hands it (the return buffer of a memory
 * return); the callee's own regions, all above the frontier, are free.
 *
 * TOP-LEVEL:
 *   allocas_above, result_allocas_above — every allocation, and the
 *                                 frontier, at or above a bound
 *   step_inst_allocas_above, exec_block_allocas_above,
 *   run_blocks_allocas_above    — execution keeps allocas_above, through
 *                                 INVOKEs too
 *   setup_callee_allocas_above  — the callee starts above the caller's
 *                                 frontier
 *   invoke_callee_allocas_above — every state the callee's run ends in has
 *                                 its allocations above the caller's
 *                                 frontier
 *   allocas_above_live_disjoint — such an allocation misses every live
 *                                 region of the caller
 *   callee_writes_above         — memory below a bound is kept outside some
 *                                 exempt regions
 *   callee_writes_above_refl, callee_writes_above_trans,
 *   callee_writes_above_mstore  — building it up over the callee's steps
 *   callee_writes_above_live    — it keeps the bytes of every live region
 *                                 of the caller
 *   invoke_return_frame         — what the INVOKE's return keeps of the
 *                                 caller
 *   invoke_return_local_ptrs_rel — KEY LEMMA: the caller's local_ptrs_rel
 *                                 holds after the return
 *   step_inst_invoke_live_regions — the returning INVOKE step keeps the
 *                                 caller's live locals and its frame
 *
 * Helpers:
 *   allocas_above_fields, exec_alloca_allocas_above,
 *   result_allocas_above_mono, foldl_update_var_frame
 *)

Theory intCallFrame
Ancestors
  list finite_map arithmetic words
  venomExecSemantics venomExecProofs venomMemProofs venomState venomInst
  valueEncoding valueEncodingProps localPtrsProps compileEnv

(* ===== Allocations above a bound ===== *)

Definition allocas_above_def:
  allocas_above lo (s:venom_state) ⇔
    lo ≤ s.vs_alloca_next ∧
    ∀aid b sz. FLOOKUP s.vs_allocas aid = SOME (b, sz) ⇒ lo ≤ b
End

Definition result_allocas_above_def:
  result_allocas_above lo (OK s) = allocas_above lo s ∧
  result_allocas_above lo (IntRet ir s) = allocas_above lo s ∧
  result_allocas_above lo (Halt s) = allocas_above lo s ∧
  result_allocas_above lo (Abort a s) = allocas_above lo s ∧
  result_allocas_above lo (Error e) = T
End

Theorem allocas_above_fields:
  ∀lo s s'.
    s'.vs_allocas = s.vs_allocas ∧ s'.vs_alloca_next = s.vs_alloca_next ⇒
    (allocas_above lo s' ⇔ allocas_above lo s)
Proof
  simp[allocas_above_def]
QED

Theorem result_allocas_above_mono:
  ∀lo lo' r. lo ≤ lo' ∧ result_allocas_above lo' r ⇒ result_allocas_above lo r
Proof
  Cases_on `r` >> rw[result_allocas_above_def, allocas_above_def] >>
  res_tac >> decide_tac
QED

Theorem exec_alloca_allocas_above:
  ∀lo inst s n.
    allocas_above lo s ⇒ result_allocas_above lo (exec_alloca inst s n)
Proof
  rw[exec_alloca_def] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[result_allocas_above_def]) >>
  gvs[allocas_above_def, update_var_def, FLOOKUP_UPDATE] >> rw[] >>
  res_tac >> decide_tac
QED

(* bind_outputs over the INVOKE's return changes only variables, and only
   at the outputs. *)
Theorem foldl_update_var_frame:
  ∀kvs base.
    (∃vars. FOLDL (λs' (k,v). update_var k v s') base kvs =
            base with vs_vars := vars) ∧
    ∀x. ¬MEM x (MAP FST kvs) ⇒
        lookup_var x (FOLDL (λs' (k,v). update_var k v s') base kvs) =
        lookup_var x base
Proof
  Induct >- simp[venom_state_component_equality] >>
  Cases >> qx_gen_tac `b0` >>
  first_x_assum (qspec_then `update_var q r b0` strip_assume_tac) >>
  simp[] >> conj_tac
  >- (qexists_tac `vars` >> gvs[update_var_def, venom_state_component_equality])
  >- (rpt strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE])
QED

Theorem invoke_return_frame:
  ∀outs vals ret s cs' s'.
    bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s cs')) =
      SOME s' ⇒
    s'.vs_allocas = s.vs_allocas ∧ s'.vs_alloca_next = s.vs_alloca_next ∧
    s'.vs_memory = cs'.vs_memory ∧
    ∀x. ¬MEM x outs ⇒ lookup_var x s' = lookup_var x s
Proof
  rpt gen_tac >> simp[bind_outputs_def] >> strip_tac >>
  qspecl_then [`ZIP (outs, vals)`,
               `adopt_return_fmp ret (merge_callee_state s cs')`]
    strip_assume_tac foldl_update_var_frame >>
  gvs[MAP_ZIP] >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def, lookup_var_def]
QED

(* ===== Execution keeps allocations above a bound ===== *)

(* An INVOKE's own results are the merged caller state, with the caller's
   allocation fields, or a callee's exit state, which allocates only above
   the caller's frontier. *)
Theorem allocas_above_joint[local]:
  (∀fuel ctx inst s lo.
     allocas_above lo s ⇒
     result_allocas_above lo (step_inst fuel ctx inst s)) ∧
  (∀fuel ctx bb s lo.
     allocas_above lo s ⇒
     result_allocas_above lo (exec_block fuel ctx bb s)) ∧
  (∀fuel ctx fn s lo.
     allocas_above lo s ⇒
     result_allocas_above lo (run_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac >> rpt strip_tac
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
          rpt (BasicProvers.TOP_CASE_TAC >> simp[result_allocas_above_def]) >>
          rename1 `setup_callee _ _ _ = SOME cs` >>
          `allocas_above s.vs_alloca_next cs` by
            gvs[setup_callee_def, AllCaseEqs(), allocas_above_def] >>
          gvs[] >> first_x_assum drule >> strip_tac >>
          drule_at (Pos last) result_allocas_above_mono >>
          disch_then (qspec_then `lo` mp_tac) >>
          gvs[allocas_above_def, result_allocas_above_def] >>
          rpt strip_tac >>
          TRY (drule_then strip_assume_tac invoke_return_frame) >>
          gvs[] >> res_tac >> simp[]) >>
      Cases_on `inst.inst_opcode = ALLOCA`
      >- (ONCE_REWRITE_TAC[step_inst_def] >> simp[step_inst_base_def] >>
          rpt (BasicProvers.TOP_CASE_TAC >> simp[result_allocas_above_def]) >>
          metis_tac[exec_alloca_allocas_above]) >>
      `step_inst fuel ctx inst s = step_inst_base inst s` by
        (ONCE_REWRITE_TAC[step_inst_def] >> simp[]) >>
      Cases_on `step_inst_base inst s` >> gvs[result_allocas_above_def] >>
      imp_res_tac step_inst_base_preserves_alloca_fields >>
      gvs[allocas_above_def] >> first_assum ACCEPT_TAC)
  >- (ONCE_REWRITE_TAC[exec_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >>
      simp[result_allocas_above_def] >> gvs[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      qpat_x_assum `∀lo. allocas_above lo s ⇒ _`
        (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[result_allocas_above_def] >> rw[result_allocas_above_def] >>
      first_x_assum irule >> gvs[allocas_above_def] >>
      first_assum ACCEPT_TAC) >>
  ONCE_REWRITE_TAC[run_blocks_def] >> simp[] >>
  Cases_on `fuel` >> simp[result_allocas_above_def] >>
  rename1 `SUC fuel'` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[result_allocas_above_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> simp[result_allocas_above_def] >>
  rename1 `eval_phis _ _ = OK s_phi` >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  `allocas_above lo
     (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (gvs[allocas_above_def] >> first_assum ACCEPT_TAC) >>
  gvs[] >>
  qpat_x_assum `∀lo. allocas_above lo (_ with vs_inst_idx := _) ⇒ _`
    drule >>
  Cases_on `exec_block fuel' ctx bb
              (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  rw[result_allocas_above_def] >> first_x_assum irule >> simp[]
QED

Theorem step_inst_allocas_above:
  ∀fuel ctx inst s lo.
    allocas_above lo s ⇒ result_allocas_above lo (step_inst fuel ctx inst s)
Proof
  metis_tac[allocas_above_joint]
QED

Theorem exec_block_allocas_above:
  ∀fuel ctx bb s lo.
    allocas_above lo s ⇒ result_allocas_above lo (exec_block fuel ctx bb s)
Proof
  metis_tac[allocas_above_joint]
QED

Theorem run_blocks_allocas_above:
  ∀fuel ctx fn s lo.
    allocas_above lo s ⇒ result_allocas_above lo (run_blocks fuel ctx fn s)
Proof
  metis_tac[allocas_above_joint]
QED

Theorem setup_callee_allocas_above:
  ∀callee args s cs.
    setup_callee callee args s = SOME cs ⇒
    allocas_above s.vs_alloca_next cs
Proof
  rw[setup_callee_def, allocas_above_def] >> gvs[]
QED

(* Whatever state the callee's run ends in, IntRet, Halt or Abort, all its
   allocations lie at or above the caller's frontier at the call. *)
Theorem invoke_callee_allocas_above:
  ∀fuel ctx callee args s cs.
    setup_callee callee args s = SOME cs ⇒
    result_allocas_above s.vs_alloca_next (run_blocks fuel ctx callee cs)
Proof
  metis_tac[setup_callee_allocas_above, run_blocks_allocas_above]
QED

(* An allocation at or above the caller's frontier misses each of the
   caller's live regions. *)
Theorem allocas_above_live_disjoint:
  ∀func cenv scopes s t name lo sz aid b n.
    local_ptrs_rel func cenv scopes s ∧
    local_region cenv scopes s name lo sz ∧
    allocas_above s.vs_alloca_next t ∧
    FLOOKUP t.vs_allocas aid = SOME (b, n) ⇒
    regions_disjoint lo sz b n
Proof
  rw[allocas_above_def] >> res_tac >>
  irule local_ptrs_rel_above_frontier >> metis_tac[]
QED

(* ===== The callee's writes ===== *)

(* m' keeps the bytes of m below lo, outside the exempt regions excl. *)
Definition callee_writes_above_def:
  callee_writes_above lo excl m m' ⇔
    ∀b sz. b + sz ≤ lo ∧
           EVERY (λ(eb,esz). regions_disjoint b sz eb esz) excl ⇒
           mem_bytes_at b sz m' = mem_bytes_at b sz m
End

Theorem callee_writes_above_refl:
  ∀lo excl m. callee_writes_above lo excl m m
Proof
  simp[callee_writes_above_def]
QED

Theorem callee_writes_above_trans:
  ∀lo excl m1 m2 m3.
    callee_writes_above lo excl m1 m2 ∧ callee_writes_above lo excl m2 m3 ⇒
    callee_writes_above lo excl m1 m3
Proof
  rw[callee_writes_above_def] >> res_tac >> simp[]
QED

(* An MSTORE at or above lo, or inside an exempt region, keeps it. *)
Theorem callee_writes_above_mstore:
  ∀lo excl m ss off w.
    callee_writes_above lo excl m ss.vs_memory ∧
    (lo ≤ off ∨
     ∃eb esz. MEM (eb, esz) excl ∧ eb ≤ off ∧ off + 32 ≤ eb + esz) ⇒
    callee_writes_above lo excl m (mstore off w ss).vs_memory
Proof
  rw[callee_writes_above_def] >> res_tac >>
  `b + sz ≤ off ∨ off + 32 ≤ b` suffices_by
    (strip_tac >> simp[mstore_mem_bytes_at_disjoint]) >>
  gvs[EVERY_MEM] >> res_tac >> gvs[regions_disjoint_def] >> decide_tac
QED

(* The caller's live regions lie below its frontier; those that miss the
   exempt regions keep their bytes. *)
Theorem callee_writes_above_live:
  ∀func cenv scopes s excl m'.
    local_ptrs_rel func cenv scopes s ∧
    callee_writes_above s.vs_alloca_next excl s.vs_memory m' ∧
    (∀name lo sz. local_region cenv scopes s name lo sz ⇒
       EVERY (λ(eb,esz). regions_disjoint lo sz eb esz) excl) ⇒
    ∀name lo sz. local_region cenv scopes s name lo sz ⇒
      mem_bytes_at lo sz s.vs_memory = mem_bytes_at lo sz m'
Proof
  rpt strip_tac >>
  `lo + sz ≤ s.vs_alloca_next` by
    (gvs[local_region_def, local_ptrs_rel_def] >> res_tac >> gvs[]) >>
  gvs[callee_writes_above_def] >> metis_tac[]
QED

(* ===== The caller after the return ===== *)

(* KEY LEMMA: the INVOKE's return keeps the caller's live locals when the
   callee kept the bytes of their regions and no output is a live local's
   pointer.  The caller's allocations are unchanged (merge_callee_state). *)
Theorem invoke_return_local_ptrs_rel:
  ∀func cenv scopes s cs' outs vals ret s'.
    local_ptrs_rel func cenv scopes s ∧
    bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s cs')) =
      SOME s' ∧
    EVERY (not_local_ptr cenv scopes) outs ∧
    (∀name lo sz. local_region cenv scopes s name lo sz ⇒
       mem_bytes_at lo sz s.vs_memory = mem_bytes_at lo sz cs'.vs_memory) ⇒
    local_ptrs_rel func cenv scopes s'
Proof
  rpt strip_tac >> drule invoke_return_frame >> strip_tac >>
  irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  conj_tac >~ [`mem_bytes_at`]
  >- (rpt strip_tac >>
      qpat_x_assum `∀name lo sz. local_region _ _ _ _ _ _ ⇒ _` drule >>
      simp[]) >>
  rpt strip_tac >~ [`lookup_var _ s' = lookup_var _ s`]
  >- (qpat_x_assum `∀x. ¬MEM x outs ⇒ _` irule >> strip_tac >>
      gvs[EVERY_MEM, not_local_ptr_def] >> metis_tac[]) >>
  gvs[]
QED

(* The returning INVOKE step: from a caller state with its live locals
   related, a callee that changed no byte below the caller's frontier
   outside the exempt buffers (which miss the live regions) gives back a
   caller state with the same live locals, allocations and frontier. *)
Theorem step_inst_invoke_live_regions:
  ∀fuel ctx inst s name arg_ops callee args cs ret cs'
   func cenv scopes excl.
    inst.inst_opcode = INVOKE ∧
    decode_invoke inst = SOME (name, arg_ops) ∧
    lookup_function name ctx.ctx_functions = SOME callee ∧
    eval_operands arg_ops s = SOME args ∧
    setup_callee callee args s = SOME cs ∧
    run_blocks fuel ctx callee cs = IntRet ret cs' ∧
    LENGTH inst.inst_outputs = LENGTH ret.iret_values ∧
    local_ptrs_rel func cenv scopes s ∧
    EVERY (not_local_ptr cenv scopes) inst.inst_outputs ∧
    callee_writes_above s.vs_alloca_next excl s.vs_memory cs'.vs_memory ∧
    (∀name lo sz. local_region cenv scopes s name lo sz ⇒
       EVERY (λ(eb,esz). regions_disjoint lo sz eb esz) excl) ⇒
    ∃s'. step_inst fuel ctx inst s = OK s' ∧
         local_ptrs_rel func cenv scopes s' ∧
         s'.vs_allocas = s.vs_allocas ∧
         s'.vs_alloca_next = s.vs_alloca_next ∧
         s'.vs_memory = cs'.vs_memory
Proof
  rpt strip_tac >>
  `∃s'. bind_outputs inst.inst_outputs ret.iret_values
          (adopt_return_fmp ret (merge_callee_state s cs')) = SOME s'` by
    simp[bind_outputs_def] >>
  qexists_tac `s'` >>
  `step_inst fuel ctx inst s = OK s'` by simp[Once step_inst_def] >>
  drule invoke_return_frame >> strip_tac >> simp[] >>
  qspecl_then [`func`, `cenv`, `scopes`, `s`, `cs'`, `inst.inst_outputs`,
               `ret.iret_values`, `ret`, `s'`]
    mp_tac invoke_return_local_ptrs_rel >>
  impl_tac >- (simp[] >> metis_tac[callee_writes_above_live]) >>
  simp[]
QED

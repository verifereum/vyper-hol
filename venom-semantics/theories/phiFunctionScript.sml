(*
 * PHI Elimination Function-Level Correctness
 *
 * This theory proves function and context-level correctness of PHI elimination.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - phi_elimination_correct         : Function-level correctness
 *   - phi_elimination_context_correct : Context-level correctness
 *
 * HELPER THEOREMS:
 *   - run_function_state_equiv        : Function execution preserves equiv
 *   - run_block_result_equiv_exists   : Block result equivalence witness
 *
 * ============================================================================
 *)

Theory phiFunction
Ancestors
  phiBlock execEquiv venomSem venomInst stateEquiv phiWellFormed phiTransform dfgDefs list

(* ==========================================================================
   Function Execution Helpers
   ========================================================================== *)

(* run_block result equivalence - derived from execEquiv version *)
Theorem run_block_result_equiv_exists:
  !fn bb s1 s2 r1.
    state_equiv s1 s2 /\
    run_block fn bb s1 = r1
  ==>
    ?r2. run_block fn bb s2 = r2 /\ result_equiv r1 r2
Proof
  rpt strip_tac >>
  qexists_tac `run_block fn bb s2` >> simp[] >>
  metis_tac[run_block_result_equiv]
QED

(* Function execution preserves state equivalence - induction on fuel *)
Theorem run_function_state_equiv:
  !fuel fn s1 s2 r1.
    state_equiv s1 s2 /\
    run_function fuel fn s1 = r1
  ==>
    ?r2. run_function fuel fn s2 = r2 /\ result_equiv r1 r2
Proof
  Induct_on `fuel` >>
  rpt strip_tac
  >- (
    (* Base case: fuel = 0 - explicitly provide witness *)
    qexists_tac `run_function 0 fn s2` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  ) >>
  (* SUC fuel case - unfold carefully *)
  qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
  simp[Once run_function_def] >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  simp[Once run_function_def] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >> gvs[result_equiv_def] >>
  `result_equiv (run_block fn x s1) (run_block fn x s2)` by (
    irule run_block_result_equiv >> simp[]
  ) >>
  Cases_on `run_block fn x s1` >> Cases_on `run_block fn x s2` >> gvs[] >>
  (* OK/OK case - check vs_halted *)
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* ==========================================================================
   Function-level Correctness
   ========================================================================== *)

(* TOP-LEVEL: Main correctness theorem for PHI elimination.
 *
 * The theorem requires:
 * 1. phi_wf_fn func - PHI instructions are well-formed
 * 2. func.fn_blocks <> [] - function has at least one block
 * 3. Either vs_prev_bb is set (non-entry), or we're at entry block
 *
 * The precondition about vs_prev_bb ensures we can use transform_block_result_equiv
 * for non-entry blocks. For entry blocks, the transform is identity because
 * phi_wf_fn requires entry blocks have no PHI with single origin.
 *
 * This theorem says: running the original and transformed function produces
 * equivalent results (same final state up to state_equiv).
 *)
Theorem phi_elimination_correct:
  !fuel (func:ir_function) s result.
    phi_wf_fn func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?result'. run_function fuel (transform_function func) s = result' /\
              result_equiv result result'
Proof
  (* Proof by induction on fuel *)
  Induct_on `fuel` >> rpt strip_tac
  >- (
    (* Base case: fuel = 0, vs_prev_bb <> NONE *)
    qexists_tac `run_function 0 (transform_function func) s` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  )
  >- (
    (* Base case: fuel = 0, at entry block *)
    qexists_tac `run_function 0 (transform_function func) s` >> simp[] >>
    gvs[Once run_function_def, result_equiv_def] >>
    simp[Once run_function_def, result_equiv_def]
  )
  >- (
    (* SUC fuel case: vs_prev_bb <> NONE *)
    qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
    simp[Once run_function_def] >> strip_tac >>
    simp[Once run_function_def, transform_function_def, lookup_block_transform] >>
    Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >> gvs[result_equiv_def] >>
    rename1 `lookup_block _ _ = SOME bb` >>
    `run_block (func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks)
               (transform_block (build_dfg_fn func) bb) s =
     run_block func (transform_block (build_dfg_fn func) bb) s`
    by metis_tac[run_block_fn_irrelevant] >>
    `(func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks) =
     transform_function func` by simp[transform_function_def, LET_DEF] >>
    pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
    `MEM bb func.fn_blocks` by metis_tac[lookup_block_MEM] >>
    `result_equiv (run_block func bb s) (run_block func (transform_block (build_dfg_fn func) bb) s)` by (
      irule transform_block_result_equiv >> simp[] >>
      fs[phi_wf_fn_def, LET_DEF] >> rpt conj_tac >>
      rpt strip_tac >> TRY (first_x_assum drule_all >> simp[]) >>
      simp[build_dfg_fn_well_formed]
    ) >>
    Cases_on `run_block func bb s` >> Cases_on `run_block func (transform_block (build_dfg_fn func) bb) s` >>
    gvs[result_equiv_def] >>
    TRY (`v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def]) >>
    Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
    (* Not halted - use run_function_state_equiv to bridge state_equiv *)
    `?r2. run_function fuel func v' = r2 /\ result_equiv (run_function fuel func v) r2` by (
      qspecl_then [`fuel`, `func`, `v`, `v'`, `run_function fuel func v`]
        mp_tac run_function_state_equiv >> simp[]
    ) >>
    irule result_equiv_trans >> qexists_tac `r2` >> simp[] >>
    (* Use IH - first prove v'.vs_prev_bb <> NONE *)
    `v'.vs_prev_bb <> NONE` by (
      drule run_block_ok_not_halted_sets_prev_bb >> simp[]
    ) >>
    first_x_assum (qspecl_then [`func`, `v'`] mp_tac) >>
    impl_tac >- simp[] >>
    strip_tac >>
    (* Prove result_equiv symmetry via case analysis *)
    Cases_on `run_function fuel func v'` >>
    Cases_on `run_function fuel (transform_function func) v'` >>
    gvs[result_equiv_def] >>
    metis_tac[state_equiv_sym]
  ) >>
  (* SUC fuel case: at entry block *)
  qpat_x_assum `run_function (SUC _) _ _ = _` mp_tac >>
  simp[Once run_function_def] >> strip_tac >>
  simp[Once run_function_def, transform_function_def, lookup_block_transform] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >> gvs[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  (* At entry block: use run_block_transform_identity since entry block has no PHI with single origin *)
  (* Normalize fn parameter *)
  `run_block (func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks)
             (transform_block (build_dfg_fn func) bb) s =
   run_block func (transform_block (build_dfg_fn func) bb) s`
  by metis_tac[run_block_fn_irrelevant] >>
  `(func with fn_blocks := MAP (transform_block (build_dfg_fn func)) func.fn_blocks) =
   transform_function func` by simp[transform_function_def, LET_DEF] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  (* Since s.vs_current_bb = (HD func.fn_blocks).bb_label and lookup succeeded, bb = HD func.fn_blocks *)
  (* From phi_wf_fn, entry block has no PHI with single origin, so transform is identity *)
  `run_block func (transform_block (build_dfg_fn func) bb) s = run_block func bb s` by (
    irule run_block_transform_identity >>
    rpt strip_tac >>
    (* First prove bb = HD func.fn_blocks *)
    `bb = HD func.fn_blocks` by (
      qpat_x_assum `lookup_block _ _ = _` mp_tac >>
      qpat_x_assum `_ = (HD _).bb_label` mp_tac >>
      Cases_on `func.fn_blocks` >> simp[lookup_block_def]
    ) >>
    fs[phi_wf_fn_def, LET_DEF] >>
    first_x_assum irule >> simp[] >>
    qexists_tac `idx` >> simp[]
  ) >>
  simp[] >>
  Cases_on `run_block func bb s` >> gvs[result_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
  (* Not halted - use IH *)
  (* v.vs_prev_bb <> NONE follows from run_block_ok_not_halted_sets_prev_bb *)
  qspecl_then [`func`, `bb`, `s`, `v`] assume_tac run_block_ok_not_halted_sets_prev_bb >>
  gvs[] >>
  first_x_assum (qspecl_then [`func`, `v`] mp_tac) >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Context-level Correctness
   ========================================================================== *)

(* TOP-LEVEL: Context-level correctness - transformation preserves semantics
   for all functions in a context. *)
Theorem phi_elimination_context_correct:
  !ctx fn_name fuel (func:ir_function) s result.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    phi_wf_fn func /\
    func.fn_blocks <> [] /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label) /\
    run_function fuel func s = result ==>
    ?func' result'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      run_function fuel func' s = result' /\
      result_equiv result result'
Proof
  rw[transform_context_def, MEM_MAP] >>
  qexists_tac `transform_function func` >>
  rw[] >- (
    qexists_tac `func` >> rw[]
  ) >- (
    rw[transform_function_def]
  ) >>
  qspecl_then [`fuel`, `func`, `s`, `run_function fuel func s`] mp_tac phi_elimination_correct >>
  simp[]
QED


(*
 * PHI Elimination Function-Level Correctness
 *
 * Uses block_sim_function_reachable from the simulation framework
 * to lift per-block simulation (phi_elim_block_sim) to function level.
 *
 * Single top-level theorem: phi_elimination_context_correct.
 *)

Theory phiCorrectnessProof
Ancestors
  phiBlock passSimulationProps passSimulationDefs execEquivParamProps
  venomExecSemantics venomInst stateEquiv stateEquivProps
  phiWellFormed phiTransform phiDefs list

(* Helper: transform_function matches function_map_transform shape *)
Theorem transform_function_is_function_map_transform:
  !fn. transform_function fn =
       function_map_transform (transform_block (dfg_build_function fn)) fn
Proof
  simp[transform_function_def, function_map_transform_def, LET_DEF]
QED

(* TOP-LEVEL: Context-level correctness.
 *
 * For any well-formed function in a context, the transformed context
 * contains a same-named function with equivalent execution semantics.
 *
 * Proof approach:
 *   1. Rewrite transform_function as function_map_transform
 *   2. irule block_sim_function_reachable
 *   3. Entry block: identity (no single-origin PHIs) via run_block_transform_identity
 *   4. Non-entry blocks: phi_elim_block_sim (guarded by vs_prev_bb)
 *   5. Wrap with transform_context membership (MEM_MAP)
 *)
Theorem phi_elimination_correct:
  !ctx fn_name fuel (func:ir_function) s.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_ir_fn func /\
    func.fn_blocks <> [] /\
    s.vs_inst_idx = 0 /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label)
  ==>
    ?func'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      lift_result (state_equiv {}) (execution_equiv {})
        (run_function fuel ctx func s)
        (run_function fuel ctx func' s)
Proof
  rpt gen_tac >>
  DISCH_TAC >>
  qexists_tac `transform_function func` >>
  `MEM func ctx.ctx_functions` by fs[] >>
  `func.fn_name = fn_name` by fs[] >>
  `wf_ir_fn func` by fs[] >>
  `func.fn_blocks <> []` by fs[] >>
  `s.vs_inst_idx = 0` by fs[] >>
  `phi_wf_fn func` by metis_tac[wf_ir_implies_phi_wf] >>
  fs[phi_wf_fn_def, LET_DEF] >>
  conj_tac >- (
    simp[transform_context_def, MEM_MAP] >>
    qexists_tac `func` >> simp[]) >>
  conj_tac >- simp[transform_function_def] >>
  simp[transform_function_is_function_map_transform] >>
  irule block_sim_function_pointwise_reachable >>
  simp[state_equiv_execution_equiv_valid_state_rel, transform_block_label,
       state_equiv_def, execution_equiv_def] >>
  (* Per-block simulation — only remaining goal *)
  rpt strip_tac >>
  Cases_on `s''.vs_prev_bb`
  >- ( (* prev_bb = NONE => bb = HD fn_blocks => entry block *)
    fs[] >>
    `!idx inst. get_instruction (HD func.fn_blocks) idx = SOME inst ==>
       phi_single_origin (dfg_build_function func) inst = NONE` by
      (rpt strip_tac >> res_tac) >>
    imp_res_tac run_block_transform_identity >>
    fs[] >>
    irule lift_result_refl >>
    simp[state_equiv_refl, execution_equiv_refl]) >>
  (* prev_bb = SOME _ => non-entry block *)
  irule phi_elim_block_sim >>
  fs[] >> rpt conj_tac >> rpt strip_tac >> res_tac
QED

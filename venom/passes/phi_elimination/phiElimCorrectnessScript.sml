(*
 * PHI Elimination Pass — Correctness Statement
 *
 * Single top-level theorem, built on the block simulation in proofs/phiBlockScript.sml.
 *)

Theory phiElimCorrectness
Ancestors
  passTransform phiTransform phiWellFormed venomWf sorting list
  phiBlock passSimulationProps passSimulationDefs execEquivParamProps venomExecSemantics venomInst stateEquiv stateEquivProps phiDefs passSimulationProofs

Theorem transform_function_is_function_map_transform[local]:
  !fn. transform_function fn =
       function_map_transform (transform_block (dfg_build_function fn)) fn
Proof
  simp[transform_function_def, function_map_transform_def, LET_DEF]
QED

(* After PHI elimination on a well-formed, PHI-elim-safe function, there exists a
   transformed function in the new context that produces execution-equivalent results
   (matching OK values, halts, reverts, and errors) under state equivalence.
   Proof: lift per-block simulation (phi_elim_run_block_lift_result) to function
   level via block_sim_function_pointwise_reachable. *)
Theorem phi_elim_pass_correct:
  !ctx fn_name fuel (func:ir_function) s.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_ir_fn func /\
    phi_elim_safe_fn func /\
    wf_function func /\
    fn_pseudos_prefix func /\
    func.fn_blocks <> [] /\
    s.vs_inst_idx = 0 /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label)
  ==>
    ?func'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (run_blocks fuel ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  rpt gen_tac >>
  DISCH_TAC >>
  qexists_tac `transform_function func` >>
  `MEM func ctx.ctx_functions` by fs[] >>
  `func.fn_name = fn_name` by fs[] >>
  `wf_ir_fn func` by fs[] >>
  `phi_elim_safe_fn func` by fs[] >>
  `wf_function func` by fs[] >>
  `fn_pseudos_prefix func` by fs[] >>
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
  (* Per-block simulation: real PHI-prefix/eval_phis simulation. *)
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `run_block fuel0 ctx0 bb st` >>
  qspecl_then [`func`, `bb`, `fuel0`, `ctx0`, `st`]
    mp_tac phi_elim_run_block_lift_result >>
  simp[] >>
  fs[wf_function_def, fn_pseudos_prefix_def] >>
  Cases_on `st.vs_prev_bb = NONE` >> fs[]
QED

(* ===== Obligations ===== *)

(* The set of block labels is unchanged by PHI elimination: no blocks are added
   or removed, only their instructions may change. *)
Theorem phi_elim_preserves_fn_labels:
  ∀fn. fn_labels (transform_function fn) = fn_labels fn
Proof
  rw[transform_function_def, LET_DEF, venomInstTheory.fn_labels_def,
     MAP_MAP_o, combinTheory.o_DEF, transform_block_label]
QED

(* A function has an entry block after PHI elimination iff it had one before. *)
Theorem phi_elim_preserves_fn_has_entry:
  ∀fn. fn_has_entry (transform_function fn) ⇔ fn_has_entry fn
Proof
  rw[transform_function_def, LET_DEF, venomWfTheory.fn_has_entry_def]
QED

(* Instruction IDs remain unique after PHI elimination when they were unique
   before. *)
Theorem phi_elim_preserves_fn_inst_ids_distinct:
  ∀fn. fn_inst_ids_distinct fn ⇒ fn_inst_ids_distinct (transform_function fn)
Proof
  rw[transform_function_def, LET_DEF, venomWfTheory.fn_inst_ids_distinct_def] >>
  metis_tac[transform_blocks_ids_perm, ALL_DISTINCT_PERM]
QED

(* After PHI elimination, every basic block still has its pseudo-instructions
   (PHI, LABEL) at the top, with no non-pseudo instructions before them. *)
Theorem phi_elim_preserves_fn_pseudos_prefix:
  ∀fn. fn_pseudos_prefix (transform_function fn)
Proof
  rw[transform_function_def, LET_DEF, venomWfTheory.fn_pseudos_prefix_def] >>
  gvs[MEM_MAP] >>
  metis_tac[transform_block_pseudos_prefix]
QED

(* SSA form is preserved: instruction outputs remain unique per function after
   PHI elimination. *)
Theorem phi_elim_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (transform_function fn)
Proof
  rw[transform_function_def, LET_DEF, venomWfTheory.ssa_form_def,
     venomInstTheory.fn_insts_def] >>
  metis_tac[transform_blocks_outputs_perm, ALL_DISTINCT_PERM]
QED

(* Every block successor in the transformed function is a valid block label:
   PHI elimination does not introduce dangling successor references. *)
Theorem phi_elim_preserves_fn_succs_closed:
  ∀fn. wf_function fn ⇒ fn_succs_closed (transform_function fn)
Proof
  rw[venomWfTheory.fn_succs_closed_def] >>
  gvs[transform_function_def, LET_DEF, MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  `bb_well_formed bb` by fs[venomWfTheory.wf_function_def] >>
  `bb_succs (transform_block (dfg_build_function fn) bb) = bb_succs bb` by
    metis_tac[transform_block_succs] >>
  `MEM succ (bb_succs bb)` by fs[] >>
  `MEM succ (fn_labels fn)` by
    (fs[venomWfTheory.wf_function_def, venomWfTheory.fn_succs_closed_def] >>
     metis_tac[]) >>
  fs[venomInstTheory.fn_labels_def, MAP_MAP_o, combinTheory.o_DEF,
     transform_block_label]
QED

(* The composite well-formedness property (distinct labels, entry block,
   well-formed blocks, successor closure, distinct instruction IDs) is preserved
   by PHI elimination. *)
Theorem phi_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (transform_function fn)
Proof
  rw[venomWfTheory.wf_function_def]
  >- metis_tac[phi_elim_preserves_fn_labels]
  >- metis_tac[phi_elim_preserves_fn_has_entry]
  >- (gvs[transform_function_def, LET_DEF, MEM_MAP] >>
      metis_tac[transform_block_well_formed])
  >- (`wf_function fn` by simp[venomWfTheory.wf_function_def] >>
      metis_tac[phi_elim_preserves_fn_succs_closed])
  >- (`fn_inst_ids_distinct fn` by simp[] >>
      metis_tac[phi_elim_preserves_fn_inst_ids_distinct])
QED

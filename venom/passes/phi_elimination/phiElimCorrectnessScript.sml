(* PHI elimination preserves execution from a well-formed SSA entry state. *)
Theory phiElimCorrectness
Ancestors
  phiTransform phiOrigins phiDefs venomWf o1PassContract unitShapeDefs
  stateEquiv venomExecSemantics sorting list phiPrefixExecution phiOriginValues

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

Theorem phi_run_blocks_correct[local]:
  !fuel ctx fn s0 s.
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
  EVERY (\i. i.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
  fn_entry_label fn = SOME s0.vs_current_bb /\ s0.vs_vars = FEMPTY /\
  source_entry_reachable ctx fn s0 s ==>
  run_blocks fuel ctx fn s = run_blocks fuel ctx (transform_function fn) s
Proof
  Induct >> rpt gen_tac
  >- simp[run_blocks_def] >>
  strip_tac >>
  simp[run_blocks_unfold, transform_function_def, lookup_block_transform] >>
  namedCases_on `lookup_block s.vs_current_bb fn.fn_blocks` ["", "bb"] >> simp[] >>
  `pseudos_prefix bb` by
    (fs[venomWfTheory.fn_pseudos_prefix_def] >>
     metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  `run_block fuel ctx bb s = run_block fuel ctx (transform_block (dfg_build_function fn) bb) s` by
    (irule phi_run_block_correct >> metis_tac[]) >>
  simp[] >>
  namedCases_on `run_block fuel ctx (transform_block (dfg_build_function fn) bb) s`
    ["t", "t", "reason t", "vals t", "e"] >> simp[] >>
  Cases_on `t.vs_halted` >> simp[] >>
  qpat_x_assum `!ctx fn s0 s. _`
    (qspecl_then [`ctx`, `fn`, `s0`, `t`] mp_tac) >>
  simp[transform_function_def] >>
  disch_then irule >> metis_tac[source_entry_reachable_step]
QED

(* Origins use variable identity.  A sole origin must be available strictly
   before the PHI block: an entry-to-block path avoiding its definition would
   provide another incoming origin.  Entry PHIs and edges into the entry block
   are excluded by the pipeline's existing entry invariants. *)
Theorem phi_elim_pass_correct:
  !fuel ctx (func:ir_function) s.
    wf_function func /\
    fn_inst_wf func /\
    wf_ssa func /\
    fn_pseudos_prefix func /\
    first_block_no_preds func /\
    first_block_no_phi func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    s.vs_vars = FEMPTY
  ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx func s)
      (run_blocks fuel ctx (transform_function func) s)
Proof
  rpt strip_tac >>
  `run_blocks fuel ctx func s = run_blocks fuel ctx (transform_function func) s` by
    (irule phi_run_blocks_correct >>
     fs[o1PassContractTheory.first_block_no_phi_def] >> qexists `s` >>
     simp[source_entry_reachable_seed]) >>
  simp[] >> Cases_on `run_blocks fuel ctx (transform_function func) s` >>
  simp[lift_result_def, state_equiv_def, execution_equiv_def]
QED

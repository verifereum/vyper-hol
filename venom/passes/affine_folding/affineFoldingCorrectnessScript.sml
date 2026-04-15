Theory affineFoldingCorrectness
Ancestors
  affineFoldingProofs
  venomWf
  passSimulationProps
  affineFoldingDefs
  passSimulationDefs
  venomInst

Libs
  BasicProvers

(* ===== Structural properties of af_rewrite_inst ===== *)

Theorem af_rewrite_inst_preserves_id[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    result.inst_id = inst.inst_id
Proof
  simp[af_rewrite_inst_def, vi_base_def, vi_offset_def,
       af_extract_val_lit_def, af_extract_sub_val_lit_def] >>
  rpt gen_tac >> rpt (PURE_CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

Theorem af_rewrite_inst_preserves_outputs[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    result.inst_outputs = inst.inst_outputs
Proof
  simp[af_rewrite_inst_def, vi_base_def, vi_offset_def,
       af_extract_val_lit_def, af_extract_sub_val_lit_def] >>
  rpt gen_tac >> rpt (PURE_CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

Theorem af_rewrite_inst_not_terminator[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    ~is_terminator result.inst_opcode
Proof
  simp[af_rewrite_inst_def, vi_base_def, vi_offset_def,
       af_extract_val_lit_def, af_extract_sub_val_lit_def] >>
  rpt gen_tac >> rpt (PURE_CASE_TAC >> gvs[]) >>
  rw[] >> gvs[is_terminator_def]
QED

Theorem af_rewrite_inst_not_phi[local]:
  !dfg vi inst result.
    af_rewrite_inst dfg vi inst = SOME result ==>
    result.inst_opcode <> PHI
Proof
  simp[af_rewrite_inst_def, vi_base_def, vi_offset_def,
       af_extract_val_lit_def, af_extract_sub_val_lit_def] >>
  rpt gen_tac >> rpt (PURE_CASE_TAC >> gvs[]) >> rw[] >> gvs[]
QED

(* ===== Per-instruction structural properties ===== *)

Theorem af_transform_inst_id[local]:
  !dfg vi inst.
    (af_transform_inst dfg vi inst).inst_id = inst.inst_id
Proof
  rw[af_transform_inst_def] >>
  EVERY_CASE_TAC >> rw[] >>
  imp_res_tac af_rewrite_inst_preserves_id >> rw[]
QED

Theorem af_transform_inst_outputs[local]:
  !dfg vi inst.
    (af_transform_inst dfg vi inst).inst_outputs = inst.inst_outputs
Proof
  rw[af_transform_inst_def] >>
  EVERY_CASE_TAC >> rw[] >>
  imp_res_tac af_rewrite_inst_preserves_outputs >> rw[]
QED

Theorem af_transform_inst_terminator[local]:
  !dfg vi inst.
    is_terminator inst.inst_opcode ==>
    af_transform_inst dfg vi inst = inst
Proof
  rw[af_transform_inst_def] >>
  Cases_on `inst.inst_outputs = []` >> simp[] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  simp[af_rewrite_inst_def]
QED

Theorem af_transform_inst_not_terminator[local]:
  !dfg vi inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (af_transform_inst dfg vi inst).inst_opcode
Proof
  rw[af_transform_inst_def] >>
  EVERY_CASE_TAC >> rw[] >>
  imp_res_tac af_rewrite_inst_not_terminator >> rw[]
QED

Theorem af_transform_inst_phi[local]:
  !dfg vi inst.
    inst.inst_opcode = PHI ==>
    (af_transform_inst dfg vi inst).inst_opcode = PHI
Proof
  rw[af_transform_inst_def]
QED

Theorem af_transform_inst_not_phi[local]:
  !dfg vi inst.
    inst.inst_opcode <> PHI ==>
    (af_transform_inst dfg vi inst).inst_opcode <> PHI
Proof
  rw[af_transform_inst_def] >>
  EVERY_CASE_TAC >> rw[] >>
  imp_res_tac af_rewrite_inst_not_phi >> rw[]
QED

(* ===== Transform equals function_map_transform ===== *)

Theorem af_transform_eq_fmt[local]:
  !dfg vi fn.
    fn with fn_blocks :=
      MAP (af_transform_block dfg vi) fn.fn_blocks =
    function_map_transform
      (block_map_transform (af_transform_inst dfg vi)) fn
Proof
  rw[function_map_transform_def, block_map_transform_def,
     af_transform_block_def, ir_function_component_equality,
     listTheory.MAP_EQ_f]
QED

(* ===== Obligations ===== *)

Theorem af_preserves_ssa_form:
  !fn. wf_function fn /\ ssa_form fn ==> ssa_form (af_transform_function fn)
Proof
  rw[af_transform_function_def] >>
  ONCE_REWRITE_TAC[af_transform_eq_fmt] >>
  irule map_transform_preserves_ssa >>
  rw[af_transform_inst_id, af_transform_inst_outputs]
QED

Theorem af_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (af_transform_function fn)
Proof
  rw[af_transform_function_def] >>
  ONCE_REWRITE_TAC[af_transform_eq_fmt] >>
  irule map_transform_preserves_wf >>
  rw[af_transform_inst_id, af_transform_inst_terminator,
     af_transform_inst_not_terminator,
     af_transform_inst_phi, af_transform_inst_not_phi]
QED

(* Affine folding preserves function execution semantics.
   Preconditions are well-formedness properties trivially satisfied by the
   venom pipeline (SSA, structural, lattice consistency, no INVOKE). *)
Theorem af_transform_function_correct:
  !fuel ctx fn s.
    (* SSA uniqueness: each variable defined at most once *)
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    (* Structural well-formedness *)
    fn_inst_wf fn /\
    (* Lattice soundness for initial state *)
    vi_alist_sound (af_compute_fn_var_info fn) s /\
    (* Per-instruction lattice consistency (from FOLDL + SSA) *)
    (!inst. MEM inst (fn_insts fn) ==>
       vi_entry_consistent (af_compute_fn_var_info fn) inst) /\
    (* SSA: output variable not in operands *)
    (!inst out_var. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] ==>
       ~MEM (Var out_var) inst.inst_operands) /\
    (* SSA: no cross-variable base references to output *)
    (!inst out_var v entry. MEM inst (fn_insts fn) /\
       inst.inst_outputs = [out_var] /\
       ALOOKUP (af_compute_fn_var_info fn) v = SOME entry /\
       v <> out_var /\ vi_base entry = SOME (Var out_var) ==> F) /\
    (* No INVOKE instructions (affine folding is intra-procedural) *)
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (* Each instruction has 0 or 1 outputs *)
    (!inst. MEM inst (fn_insts fn) ==>
       inst.inst_outputs = [] \/
       ?out_var. inst.inst_outputs = [out_var]) /\
    (* Bidirectional operand reachability *)
    (!inst st. MEM inst (fn_insts fn) ==>
       ((!v. MEM (Var v) inst.inst_operands ==> FLOOKUP st.vs_vars v <> NONE) <=>
        (!v. MEM (Var v) (af_transform_inst (dfg_build_function fn)
               (af_compute_fn_var_info fn) inst).inst_operands ==>
             FLOOKUP st.vs_vars v <> NONE))) ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (af_transform_function fn) s)
Proof
  ACCEPT_TAC af_transform_function_correct_proof
QED

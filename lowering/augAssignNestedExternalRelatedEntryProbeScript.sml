(* Bounded runtime-entry audit for the actual External slice. *)
Theory augAssignNestedExternalRelatedEntryProbe
Ancestors
  augAssignNestedExternalPremises augAssignNestedNormalizedProbe
  augAssignNestedExternalEntryProbe stmtSimDefs exprLoweringProps loweringPosts
  compileEnv venomState vyperInterpreter
Libs finite_mapLib computeLib supportedEvalLib

val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset

Definition nested_external_runtime_entry_def:
  nested_external_runtime_entry = nested_valid_start with
    <|vs_current_bb := "fn_probe"; vs_inst_idx := 3|>
End

Theorem nested_external_runtime_position:
  ~nested_external_runtime_entry.vs_halted /\
  nested_external_runtime_entry.vs_current_bb = "fn_probe" /\
  nested_external_runtime_entry.vs_inst_idx = 3 /\
  nested_external_runtime_entry.vs_allocas = FEMPTY /\
  nested_external_runtime_entry.vs_alloca_next = 0
Proof
  EVAL_TAC
QED

Theorem nested_external_runtime_state_rel:
  state_rel nested_external_entry_fn nested_external_slice_cenv nested_external_cx
    nested_premise_es nested_external_runtime_entry
Proof
  rewrite_tac[state_rel_def] >>
  CONV_TAC (RESTR_EVAL_CONV [``nested_external_unit``,
    ``storage_agree``, ``accounts_agree``, ``transient_agree``]) >>
  simp[combinTheory.UPDATE_def, vyperStateTheory.find_var_decl_by_name_def,
    accountsRelPropsTheory.storage_agree_refl,
    accountsRelPropsTheory.accounts_agree_refl,
    accountsRelPropsTheory.transient_agree_refl]
QED

Theorem nested_external_runtime_ret_pc:
  ret_pc_ok nested_external_slice_cenv nested_external_slice_start
    nested_external_runtime_entry
Proof
  rewrite_tac[ret_pc_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem nested_external_runtime_local_reserved:
  local_ptrs_reserved nested_external_slice_cenv nested_external_slice_start
Proof
  EVAL_TAC >> simp[]
QED

Theorem nested_external_runtime_allocation_local:
  alloca_inv nested_external_runtime_entry /\
  immutable_alloca_sep nested_external_entry_fn nested_external_slice_cenv
    nested_external_cx nested_premise_es nested_external_runtime_entry /\
  immutable_base_zero nested_external_slice_cenv nested_external_runtime_entry /\
  (!inst n base sz.
    MEM inst (fn_insts nested_external_entry_fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP nested_external_runtime_entry.vs_allocas inst.inst_id = SOME (base,sz) ==>
    sz = w2n n)
Proof
  rewrite_tac[immutable_alloca_sep_def, immutable_base_zero_def] >>
  CONV_TAC (RESTR_EVAL_CONV [``nested_external_unit``]) >> simp[]
QED


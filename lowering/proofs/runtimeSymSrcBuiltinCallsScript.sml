Theory runtimeSymSrcBuiltinCalls
Ancestors
  runtimeSymSrcAbiCalls runtimeSymSrcAbiEncode runtimeSymSrcAbiDecode
  runtimeSymSrcAbiWrappers runtimeSymSrcSystemCreate runtimeSymSrcCallStaging
  runtimeSymSrcGeneratorContracts stackPlanTypes

(* The preparation families export unconditional preservation facts.  Import
   them together here; only default-return staging needs a cross-family
   decoder hypothesis, discharged below at the ABI boundary. *)
Theorem runtime_sym_default_return_path:
  runtime_sym_env ce /\ ~is_label_operand buf /\ ~is_label_operand result /\
  ~is_label_operand def /\ ~is_label_operand addr /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_default_return_path ce rt dt buf result def addr skip mn mx info s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  drule_at (Pat `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_default_return_path_cond >>
  simp[] >> impl_tac
  >- (rpt strip_tac >>
      drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
        runtime_sym_abi_decode_to_buf >> simp[is_label_operand_def]) >>
  simp[]
QED

Theorem runtime_sym_abi_contract:
  runtime_sym_abi_clauses
Proof
  rewrite_tac[runtime_sym_abi_clauses_def] >> rpt conj_tac
  >- metis_tac[runtime_sym_lower_abi_encode]
  >- metis_tac[runtime_sym_lower_abi_decode] >>
  metis_tac[runtime_sym_store_abi_tuple]
QED

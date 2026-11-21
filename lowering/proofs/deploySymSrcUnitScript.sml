(* The deployment unit's source-side static facts, for the asm_opt_finalizer
 * case of e2e_deploy_correctness (used by e2eDeployCorrectness).
 *
 * TOP-LEVEL: lower_vyper_deploy_unit_sym_src_ok.
 *)
Theory deploySymSrcUnit
Ancestors
  deploySymSrcInstructions deploySymSrcData deploySymSrcHistory
  o1LabelFlowSourceBoundary ctorDeployDefs deployEntryLayout
  e2eProducers codegenSymRel compileVyper list context vyperTypeContract constSubstCorrect

(* The deployment unit's source-side static facts: no CODESIZE, CODECOPY
   only from runtime_begin, no code_end label yet, a byte-only data segment,
   and runtime_begin among its headers. *)


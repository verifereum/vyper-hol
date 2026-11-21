(* The runtime unit's source-side static facts, for the optimizer case of
   the top theorems (consumed by e2eAsmOpt).

   The unit-level runtime source facts are consumed by the runtime
   correctness proofs.
 *)
Theory runtimeSymSrcUnit
Ancestors
  runtimeSymSrcInstructions runtimeSymSrcData o1LabelFlowSourceBoundary
  e2eProducers codegenSymRel compileVyper runtimeLabelReadiness vyperTypeContract constSubstCorrect

(* The runtime unit's source-side static facts: no CODESIZE, CODECOPY only
   from runtime_begin, no code_end label yet, and a byte-only data segment
   (empty under Linear dispatch). *)


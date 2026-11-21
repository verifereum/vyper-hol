(* The runtime unit's source-side static facts, for the optimizer case of
   the top theorems (consumed by e2eAsmOpt).

   TOP-LEVEL: lower_vyper_runtime_unit_sym_src_ok.
 *)
Theory runtimeSymSrcUnit
Ancestors
  runtimeSymSrcInstructions runtimeSymSrcData o1LabelFlowSourceBoundary
  e2eProducers codegenSymRel compileVyper runtimeLabelReadiness vyperTypeContract constSubstCorrect

(* The runtime unit's source-side static facts: no CODESIZE, CODECOPY only
   from runtime_begin, no code_end label yet, and a byte-only data segment
   (empty under Linear dispatch). *)


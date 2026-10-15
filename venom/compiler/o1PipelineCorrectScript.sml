(*
 * The three planned O1 producers, exactly PLAN §5.8 S4-S6.
 * These are AUTHORIZED PLANNED ADMISSIONS, NOT certified correctness results.
 * No generic pass_correct/observable_result_equiv composition is claimed:
 * DFT has the F25 abort weakening and the executed pipeline has the F26 gaps.
 * No compiler hook or final-unit check is changed to obtain output shape.
 *)
Theory o1PipelineCorrect
Ancestors
  unitTransformDefs unitShapeDefs venomPipelineDriver venomPassSchedule
  contextCodegenRel stackPlanGen venomCompilerTypes venomState words

(* This is the compiler's existing O1 hook, with all three checks K T.
 * Naming it does not change compile_vyper or its literal pipeline hooks. *)
Definition o1_pipeline_def:
  o1_pipeline rpolicy unit =
    run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec unit
End

(* ===== S4: semantic forward simulation ===== *)

(* PLANNED ADMISSION S4 -- Milestone 3.
 * Proof idea: follow the actual driver/callee-first walk and executed passes
 * under o1_source_unit_ok, carrying raw frontier safety. Preserve success
 * observables and requests from the same initial outcome supply. Handle DFT
 * assertion hoisting with unit_result_rel's abort weakening (F25); repair the
 * concrete pipeline/pass gaps of F26, not the stronger old pass contract. *)
Theorem run_venom_pipeline_correct:
  !rpolicy unit out vs.
    o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ o1_initial_state_ok vs /\
    raw_unit_memory_ok unit.cu_context vs
    ==>
    checked_unit_transform_correct o1_pipeline rpolicy unit vs
Proof
  cheat
QED

(* ===== S5: output codegen memory obligations ===== *)

(* PLANNED ADMISSION S5 -- Milestone 5.
 * Proof idea: transport below-frontier raw memory safety through O1 allocation
 * and concretization, then use the generated context-plan spill intervals.
 * Construct an invariant at actual post-PHI instruction sites, including
 * incremented ordinary continuations, terminator entries, INVOKE callee
 * entries and aggregate returns; prove reads/writes avoid every live spill
 * region and each successful step preserves its bytes. *)
Theorem o1_pipeline_memory_obligations:
  !rpolicy unit out cp vs.
    o1_pipeline rpolicy unit = SOME out /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    o1_source_unit_ok unit /\ o1_initial_state_ok vs /\
    raw_unit_memory_ok unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp
    ==>
    ?Inv. codegen_memory_obligations Inv out.po_unit.cu_context cp /\
          codegen_reachability_package Inv out.po_unit.cu_context vs
Proof
  cheat
QED

(* ===== S6: output shape without new compiler checks ===== *)

(* PLANNED ADMISSION S6 -- Milestone 3.
 * Proof idea: prove each actually dispatched pass, pruning, label mapping and
 * callee-first driver preserves the output-only shape restrictions. Track
 * entry order/no parameters/no RET, legal labels and opaque GAS/return-PC
 * uses, while allowing the FMP/RET forms introduced in internal functions.
 * Raw-only restrictions are not asserted of the output. *)
Theorem run_venom_pipeline_output_shape:
  !rpolicy unit out.
    o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit
    ==> unit_shape_ok out.po_unit
Proof
  cheat
QED

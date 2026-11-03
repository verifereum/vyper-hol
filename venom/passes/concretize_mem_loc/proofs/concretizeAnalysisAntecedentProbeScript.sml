(* Audit of the bounded examples: no complete stage counterexample claimed. *)
Theory concretizeAnalysisAntecedentProbe
Ancestors concretizeAnalysisBoundaryProbe o1PassContract
Libs wordsLib

Theorem boundary_loop_entry_mismatch:
  fn_entry_label boundary_loop <> SOME boundary_loop.fn_name
Proof
  EVAL_TAC
QED

Theorem boundary_late_entry_mismatch:
  fn_entry_label boundary_late <> SOME boundary_late.fn_name
Proof
  EVAL_TAC
QED

Theorem boundary_loop_not_stage_shape:
  ~o1_ctx_shape boundary_ctx
Proof
  simp[o1_ctx_shape_def, boundary_ctx_def,
       venomInstTheory.mk_venom_context_def, o1_fn_shape_def,
       unitShapeDefsTheory.fn_shape_ok_def, boundary_loop_entry_mismatch]
QED

Theorem boundary_late_not_stage_shape:
  ~o1_ctx_shape boundary_late_ctx
Proof
  simp[o1_ctx_shape_def, boundary_late_ctx_def,
       venomInstTheory.mk_venom_context_def, o1_fn_shape_def,
       unitShapeDefsTheory.fn_shape_ok_def, boundary_late_entry_mismatch]
QED

(* Diagnostic branch conclusion (not a universal theorem):
   The checked examples in concretizeAnalysisBoundaryProbe have no missing
   base and no destructive sharing at the pass's actual fuel.  Moreover the
   two multi-block examples fail the exact o1_ctx_shape antecedent, as proved
   above.  The straight-line forward reference errors before any read.

   Unresolved universal boundary for a positive proof:
   - Under the exact stage premises and at each frame_reachable active memory
     access with source provenance G, the production-fuel bp_analyze_fuel
     result must cover that allocation base (and bound the concrete offset
     when the abstract offset is SOME).  SSA output uniqueness alone does
     not establish def_available_at, nor has convergence been proved here.
   - Production-fuel MemLiveness must record interference whenever two
     source allocation instances must coexist, including imported observed
     callee metadata, so their emitted intervals cannot overlap.
   - A stable result or termination of either finite iterator has not been
     shown universally.  The zero-fuel return is not a convergence check.
   These obligations must be proved or falsified before relocation/frame
   simulation.  The probes justify neither a new hypothesis nor a change
   to frozen definitions, and are not a verified stage counterexample.
*)

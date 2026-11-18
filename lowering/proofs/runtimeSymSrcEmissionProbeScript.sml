(* Generic instruction predicates suffice: reuse state_insts rather than
   introduce a second compiler-state invariant.  These boundaries include
   finalized blocks and separately packaged internal functions. *)
Theory runtimeSymSrcEmissionProbe
Ancestors
  loweringPackageInsts
  loweringShapeDefs vyperCompiler compileEnv list venomInst venomState

Theorem runtime_sym_new_block:
  state_insts (SND (new_block label st)) = state_insts st
Proof
  simp[state_insts_def, all_blocks_def, new_block_def, MAP_APPEND,
       FLAT_APPEND, APPEND_ASSOC]
QED

Theorem runtime_sym_new_block_result:
  new_block l s = (u,s') ==> state_insts s' = state_insts s
Proof
  metis_tac[runtime_sym_new_block, pairTheory.SND]
QED

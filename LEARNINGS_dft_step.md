# LEARNINGS_dft_step

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1.3' tags=bottom_inv,FUNPOW,non-SSA,termination
shape: Need final scheduled instruction id without SSA/topological compatibility
pattern: Reuse dftWf.funpow_preserves_bottom_inv: it only requires id distinctness, no dependency targeting the terminal id, eda_wf, and initial process provenance. Combine with schedule_entry_stack_empty rather than schedule_all_visited. Normalize square budget with rewrite_tac[EXP_2] before applying stack boundary.
works_when: unspecified
evidence:
- source:venom/passes/dft/proofs/dftNonSsaScript.sml:schedule_last_id
- tool_output:TO_dft_step-20261102T123913Z_m0144_t001

## L0002 scope='C1.4' tags=guarded-flip,EVERY,FUNPOW,predicate
shape: Transport an instruction predicate through dft_block without SSA
pattern: Use dftNonSsa.dft_block_pred: EVERY P input plus P(flip i) only for original non-pseudo flippable instructions whose sorted children differ. It encapsulates dfs_pred_state step/FUNPOW reasoning. dft_block_inst_shape discharges the exceptional ADD case with add_label_children_sorted.
works_when: unspecified
evidence:
- source:venom/passes/dft/proofs/dftNonSsaScript.sml:dft_block_pred
- source:venom/passes/dft/proofs/dftShapeScript.sml:dft_block_inst_shape
- tool_output:TO_dft_step-20261102T123913Z_m0285_t001

## L0003 scope='C1.5' tags=provenance,special-opcode,operands,source
shape: Need source instructions and opaque-value instruction preservation
pattern: dftShape.dft_block_instruction_source handles all output instructions including pseudos, not merely non-pseudos. dft_block_special_source gives exact input membership for opaque producers/propagators/consumers and entry/return classes; flip_operands_operand_mem transports any operand membership. Reuse existing flip id/output facts.
works_when: unspecified
evidence:
- source:venom/passes/dft/proofs/dftShapeScript.sml:dft_block_instruction_source
- source:venom/passes/dft/proofs/dftShapeScript.sml:dft_block_special_source
- tool_output:TO_dft_step-20261102T123913Z_m0300_t001

## L0004 scope='C1.6' tags=provenance,disjunction,opaque_use,copy_phi_var
shape: Transport whole-function opaque-use restrictions after deletion and guarded flipping
pattern: First transport copy_phi_var by rule induction using exact membership for seed/ASSIGN/PHI instructions. Keep source provenance disjunction intact with qx_choose_then + CONJUNCTS_THEN assume_tac. Operand membership transfers from the flip; original opacity permits only nonflippable use instructions, so provenance collapses to exact equality.
works_when: Output instructions are originals or guarded flips, seeds and copies cannot be flipped, and use-allowed opcodes are nonflippable.
evidence:
- source:venom/compiler/o1DftStepScript.sml:dft_shape_opaque_use
- tool_output:TO_dft_step-20261102T123913Z_m0447_t001

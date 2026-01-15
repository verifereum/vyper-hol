# Passes

Port of `vyper/venom/passes/*` (definitions only).

Directories:
- `algebraic_optimization/`
- `assign_elimination/`
- `base_pass/`
- `branch_optimization/`
- `cfg_normalization/`
- `common_subexpression_elimination/`
- `concretize_mem_loc/`
- `dead_store_elimination/`
- `dft/`
- `float_allocas/`
- `function_inliner/`
- `literals_codesize/`
- `load_elimination/`
- `lower_dload/`
- `mem2var/`
- `memmerging/`
- `phi_elimination/`
- `remove_unused_variables/`
- `revert_to_assert/`
- `sccp/`
- `single_use_expansion/`

Build:
- `Holmake` (from this directory or via the top-level pipeline)

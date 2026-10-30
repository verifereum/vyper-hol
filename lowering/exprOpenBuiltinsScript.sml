(*
 * compile_expr keeps its block open: builtins
 *
 * TOP-LEVEL:
 *   compile_*_open — arithmetic builtins, block/blob hashes, precompiles,
 *                    slice, uint2str, empty, and list/array membership
 *)

Theory exprOpenBuiltins
Ancestors
  exprOpenPrimitives exprOpenTerminals exprLowering compileEnv context emitHelper
  venomInst builtinSimple builtinMath builtinMisc builtinBytes builtinStrings

Theorem compile_neg_open:
  !v ty sa r sb.
    compile_neg v ty sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def]) >>
  strip_tac >> drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_invert_open:
  !v ty cenv sa r sb.
    compile_invert v ty cenv sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_invert_def] >>
  strip_tac >> drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_builtin_abs_open:
  !v sa r sb.
    compile_builtin_abs v sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_builtin_abs_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 6 (pairarg_tac >> simp[]) >> strip_tac >>
  drule compile_select_open >> simp[]
QED

Theorem compile_pow_mod256_open:
  !a b sa r sb.
    compile_pow_mod256 a b sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_pow_mod256_def] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_addmod_open:
  !a b c sa r sb.
    compile_addmod a b c sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_addmod_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_mulmod_open:
  !a b c sa r sb.
    compile_mulmod a b c sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_mulmod_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_as_wei_value_int_open:
  !v scale signed sa r sb.
    ~block_is_terminated sa /\
    compile_as_wei_value_int v scale signed sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_as_wei_value_int_def] >>
  IF_CASES_TAC >- (simp[comp_return_def] >> metis_tac[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 7 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_blockhash_open:
  !v sa r sb.
    compile_blockhash v sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_blockhash_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 7 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_blobhash_open:
  !v sa r sb.
    compile_blobhash v sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_blobhash_def] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_ecrecover_open:
  !h v r s sa op sb.
    compile_ecrecover h v r s sa = (op,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_ecrecover_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 7 (pairarg_tac >> simp[]) >>
  ntac 6 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_ecadd_points_open:
  !a b sa op sb.
    compile_ecadd_points a b sa = (op,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_ecadd_points_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 7 (pairarg_tac >> simp[]) >>
  ntac 7 (pairarg_tac >> simp[]) >>
  ntac 7 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_ecmul_point_open:
  !p scalar sa op sb.
    compile_ecmul_point p scalar sa = (op,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_ecmul_point_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 7 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_slice_calldata_open:
  !start len size sa r sb.
    compile_slice_calldata start len size sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_slice_calldata_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> rename1 `compile_slice_out_buf _ _ = (bufs,cs)` >>
  PairCases_on `bufs` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_uint2str_open:
  !v digits size sa r sb.
    compile_uint2str v digits size sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_uint2str_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 6 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule new_block_open >> simp[]
QED

Theorem compile_zero_words_open:
  !buf n sa u sb.
    ~block_is_terminated sa /\ compile_zero_words buf n sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  Induct_on `n` >- simp[compile_zero_words_def, comp_return_def] >>
  rpt gen_tac >>
  simp[compile_zero_words_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_builtin_empty_complex_open:
  !size bs sa r sb.
    compile_builtin_empty_complex size bs sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_builtin_empty_complex_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> Cases_on `bs` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >- (drule emit_void_terminated >> simp[is_terminator_def]) >>
  irule compile_zero_words_open >> goal_assum (drule_at Any) >>
  drule compile_alloc_buffer_open >> simp[]
QED

Theorem compile_list_membership_in_open:
  !needle xs sa r sb.
    ~block_is_terminated sa /\ compile_list_membership_in needle xs sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `xs` >- (simp[compile_list_membership_in_def, comp_return_def] >> metis_tac[]) >>
  rename1 `compile_list_membership_in needle (x::rest)` >> Cases_on `rest` >>
  simp[compile_list_membership_in_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_list_membership_notin_open:
  !needle xs sa r sb.
    ~block_is_terminated sa /\ compile_list_membership_notin needle xs sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `xs` >- (simp[compile_list_membership_notin_def, comp_return_def] >> metis_tac[]) >>
  rename1 `compile_list_membership_notin needle (x::rest)` >> Cases_on `rest` >>
  simp[compile_list_membership_notin_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_array_membership_loop_open:
  !needle arr len elem offset load is_in sa r sb.
    compile_array_membership_loop needle arr len elem offset load is_in sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_array_membership_loop_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 8 (pairarg_tac >> simp[]) >>
  ntac 7 (pairarg_tac >> simp[]) >> Cases_on `is_in` >>
  simp[comp_return_def] >> strip_tac >> gvs[]
  >- (drule new_block_open >> simp[]) >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_var_array_membership_open:
  !cenv needle arr ty is_in sa r sb.
    compile_var_array_membership cenv needle arr ty is_in sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_var_array_membership_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  drule compile_array_membership_loop_open >> simp[]
QED

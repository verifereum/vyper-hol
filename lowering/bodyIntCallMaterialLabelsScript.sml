(* Label boundaries for return and parameter materialization. *)
Theory bodyIntCallMaterialLabels
Ancestors
  bodyIntCallContextLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  bodyIntCallLabels emitHelperProps emitHelper moduleLowering stmtLowering compileEnv list pred_set

Theorem compiler_block_tail_load_tuple_elements:
  !tys off. compiler_block_tail (compile_load_tuple_elements cenv src tys off)
Proof
  Induct >> simp[compile_load_tuple_elements_def, compiler_block_tail_primitives] >>
  rpt gen_tac >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compile_load_tuple_elements_label_bounds:
  !tys off st v out.
  compile_load_tuple_elements cenv src tys off st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  Induct >- (simp[compile_load_tuple_elements_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  ntac 2 gen_tac >> rewrite_tac[compile_load_tuple_elements_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  ntac 2 (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
          >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_preserves_reservation >> rpt gen_tac >> strip_tac >>
      first_assum drule_all >> simp[]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_internal_return:
  compiler_block_tail (compile_internal_return cenv ret_val pc nreturns ret_ty src_ty tys buf)
Proof
  rewrite_tac[compile_internal_return_def, comp_ignore_bind_def] >>
  Cases_on `nreturns > 0` >> Cases_on `ret_val` >> Cases_on `buf` >> Cases_on `tys = []` >>
  simp[compiler_block_tail_primitives] >>
  (irule compiler_block_tail_bind >>
   simp[compiler_block_tail_load_tuple_elements, compiler_block_tail_store_memory,
        compiler_block_tail_primitives])
QED

Theorem compile_internal_return_label_bounds:
  compile_internal_return cenv ret_val pc nreturns ret_ty src_ty tys buf st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  map_every qid_spec_tac [`out`, `v`, `st`] >>
  ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  rewrite_tac[compile_internal_return_def, comp_ignore_bind_def] >>
  Cases_on `nreturns > 0` >> Cases_on `ret_val` >> Cases_on `buf` >> Cases_on `tys = []` >>
  simp[compiler_label_hoare_context_primitives] >>
  (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
   >- (irule compiler_label_hoare_preserves_reservation >> rpt gen_tac >> strip_tac >>
       metis_tac[compile_load_tuple_elements_label_bounds, compile_store_memory_label_bounds]) >>
   simp[compiler_label_hoare_context_primitives])
QED

Theorem compiler_block_tail_internal_param_decls:
  !params idx. compiler_block_tail (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def, compiler_block_tail_primitives] >>
  rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac[compile_internal_param_decls_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compile_internal_param_decls_label_bounds:
  !params idx st v out.
  compile_internal_param_decls params idx st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  Induct >- (simp[compile_internal_param_decls_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  ntac 2 gen_tac >> PairCases_on `h` >>
  rewrite_tac[compile_internal_param_decls_def] >>
  ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_preserves_reservation >> rpt gen_tac >> strip_tac >>
      first_assum drule_all >> simp[]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_materialize_internal_params:
  !params cenv. compiler_block_tail (materialize_internal_params cenv params)
Proof
  Induct >> simp[materialize_internal_params_def, compiler_block_tail_primitives] >>
  rpt gen_tac >> PairCases_on `h` >>
  rename1 `materialize_internal_params cenv ((name, stack, arg)::params)` >>
  Cases_on `stack` >> simp[materialize_internal_params_def, LET_THM, comp_ignore_bind_def] >>
  Cases_on `FLOOKUP cenv.ce_vars name` >> simp[] >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >> Cases_on `loc` >> simp[] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem materialize_internal_params_label_bounds:
  !params cenv st v out.
  materialize_internal_params cenv params st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  Induct >- (simp[materialize_internal_params_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  ntac 2 gen_tac >> PairCases_on `h` >>
  rename1 `materialize_internal_params cenv ((name, stack, arg)::params)` >>
  ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  Cases_on `stack` >> simp[materialize_internal_params_def, LET_THM, comp_ignore_bind_def]
  >- (Cases_on `FLOOKUP cenv.ce_vars name` >> simp[]
      >- (irule compiler_label_hoare_preserves_reservation >> rpt gen_tac >> strip_tac >>
          first_assum drule_all >> simp[]) >>
      rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >> Cases_on `loc` >> simp[] >>
      rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
           >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
           gen_tac >> BETA_TAC) >>
      irule compiler_label_hoare_preserves_reservation >> rpt gen_tac >> strip_tac >>
      first_assum drule_all >> simp[]) >>
  irule compiler_label_hoare_preserves_reservation >> rpt gen_tac >> strip_tac >>
  first_assum drule_all >> simp[]
QED

Theorem compiler_block_tail_internal_return_from_env:
  compiler_block_tail (compile_internal_return_from_env cenv ty src_ty valop rpc)
Proof
  rewrite_tac[compile_internal_return_from_env_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `cenv.ce_return_buf` >> simp[compiler_block_tail_primitives] >>
      rename1 `cenv.ce_return_buf = SOME loc` >> Cases_on `loc` >>
      simp[compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, compiler_block_tail_internal_return]
QED

Theorem compile_internal_return_from_env_label_bounds:
  compile_internal_return_from_env cenv ty src_ty valop rpc st = (v,out) /\ compile_state_ok st ==>
  compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
  bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  map_every qid_spec_tac [`out`, `v`, `st`] >>
  ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
  rewrite_tac[compile_internal_return_from_env_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `cenv.ce_return_buf` >> simp[compiler_label_hoare_typed_primitives] >>
      rename1 `cenv.ce_return_buf = SOME loc` >> Cases_on `loc` >>
      simp[compiler_label_hoare_typed_primitives] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_internal_return_label_bounds]
QED

(* Context/materialization coverage, reconciling the selected-callee audit in
   bodyIntCallLabelFrame:

   bodyIntCallContextLabels exports both block-tail framing and the raw
   state-ok/counter/bound-label triple for every context compiler reachable
   from runtime expression/statement helpers: pointer load/store, allocation,
   fixed/dynamic memory copy, word-copy and the storage/transient wrappers,
   code/immutable/calldata loads, zeroing, byte offsets and bytestring access,
   immutable copy/store, ensure/slot-to-memory, all five typed-copy actions,
   store_memory, store_transient, log topics, and dynamic-array storage copy.
   The pure context value/location selectors are not compiler actions.

   Excluded context compilers: compile_fixed_region_with_id is used only by
   the constructor immutable-base branches in moduleLowering; the selected
   runtime internal callee has is_ctor_context = F. The iload/gep-to-memory
   helpers are called only by compile_load_immutable_ctor, which has no caller
   in the expression/statement/internal-function definition cone. Nonreentrant
   lock/unlock are eliminated by the supported function header (~nr).

   This theory covers the actual contiguous-prefix prologue helpers
   compile_internal_param_decls and materialize_internal_params, and the
   return helpers compile_load_tuple_elements, compile_internal_return and
   compile_internal_return_from_env. The legacy compile_internal_params has
   no caller in compile_internal_function; it is not required by this cone.

   Remaining obligations are consumers, not certificates obtained merely
   from these builds: recursive expression/materialize_vv and argument/field
   traversal, ABI/external-call/builtin helpers, statement/local declaration
   traversal, and the selected internal-function wrapper must compose these
   interfaces. Their control flow and projected comp_get reads remain in the
   expression and statement components of the label-locality development.
   In particular this coverage makes no claim that supported bodies exclude
   external calls, ABI operations, Send, Pop, or supported builtin actions. *)

(* Bounded recursive-interface diagnostic, not a normalization correctness theorem. *)
Theory typedNormalizeContractProbe
Ancestors
  typedCopyAgreement typedNormalizeDynarrayLoop typedNormalizeLoop
  typedNormalizeContinuation typedNormalizeFields typedNormalizeFrame
  compileEnv emitHelper venomInst list arithmetic
  typedNormalizeArrayRepresentation typedNormalizeFieldRepresentation
  vyperTypeArgFits vyperTypeSystem exprSimBufferStore

(* The compiler equation alone does not imply operand freshness: at this
   legal word compiler input the first result overwrites the destination.
   The repaired array callbacks exclude this input by explicitly guarding
   operand freshness, the child prefix and the actual exit certificate. *)
Theorem normalize_callback_alias_code[local]:
  is_word_type dt /\ sc.cs_next_var = k /\
  compile_store_memory_typed ce (Var ("%" ++ toString k)) dt src st sc = ((),ec) ==>
  ec.cs_current_insts = sc.cs_current_insts ++
    [mk_inst sc.cs_next_id MLOAD [src] ["%" ++ toString k];
     mk_inst (sc.cs_next_id+1) MSTORE
       [Var ("%" ++ toString k); Var ("%" ++ toString k)] []]
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
    emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC]
QED

(* Recursive-contract inventory (diagnostic only; no definition/axiom).

   Candidate store contract, universally quantified over ce, tenv, dt, st,
   TVD, TVS, v, dst, src, sa, sb, fn, ctx, s, a, b:
     metadata acyclic; evaluate_type tenv dt/st = SOME TVD/TVS;
     metadata sizes agree with type_memory_size; type_widens_to tenv st dt;
     value_has_type TVS v; val_in_memory TVS v a s.memory;
     compile_store_memory_typed ce dst dt src st sa = ((),sb);
     fn_has_code sa sb fn; src/dst evaluate to n2w a/n2w b;
     both operand variable names not_fresh_at sa;
     nonhalted at (sa.current_bb,LENGTH sa.current_insts);
     phi_prefix_length sa.current_insts = 0;
     real no-PHI block certificate at sb.current_bb;
     disjoint padded source/destination windows of type_memory_bytes ce st/dt;
     window ends <= s.alloca_next and strictly below dimword(:256).
   Conclusion: exists t, mem_cont_sim ctx fn s t, nonhalted at sb endpoint,
     val_in_memory TVD v b t.memory; exterior of destination window unchanged;
     old-register equality at sa; exact state projection preserving every
     field except memory, variables, current/previous BB and instruction index.
   Field companion: same state/code/operand/frame contract for DT/ST lists,
     offsets d0/s0, projected semantic types TS/TD and projected values VS/VD;
     each child pair widens, each source slot represented, and cumulative
     disjoint windows bounded; conclusion all destination slots represented.
   Nominal companion uses identical named fields, metadata sizes and ALOOKUP.
   Induction: compile_store_memory_typed_ind (five mutually recursive phases),
     not induction on sa. contextScript termination measure is destination
     type_rank times three, with +1 list/array phases. Universal runtime and
     compiler states must remain in each IH.

   Branch mapping:
   word: normalize_word_window_cont; source-to-destination semantic word
     transport is separate (its input representation already uses TVD).
   bytes: normalize_bytestring_window_cont after existing
     bytestring_val_in_memory_transfer; value typing transported by
     type_widens_to_value_has_type; padded runtime length bound still needed.
   static fast: type_widens_to_static_identity plus existing copy/window frame;
     equal size alone is not representation identity.
   dynamic fast: typed_dynarray_equal_cont, identical element types;
     runtime length/header reconstruction and destination capacity from typing.
   static loop: typed_sarray_compiler_cont with Src j addr m =
     val_in_memory TVS_elem (EL j values) addr m, and analogous D/TV D_elem;
     sparse arrays instead use the existing kvs_in_memory lookup interface.
   dynamic loop: typed_dynarray_compiler_cont with the same indexed predicates,
     actual n = runtime length, data base a+32/b+32; n <= src_cap <= dst_cap.
     val_in_memory_mem_agree + val_wf and size agreement give slot locality.
     abi_encoder_array_slot_bound gives slot bounds; disjoint enclosing windows
     give child disjointness. Strict global ends imply child n2w addresses
     do not wrap, independently of the arbitrary callback runtime state u.
   tuples: normalize_tuple_fields_memory_run with tuple_in_memory_EL,
     widening at EL, cumulative source/destination sizes; reassemble tuple.
   structs: normalize_nominal_struct_fields_memory_run; identical struct type
     from type_widens_to_struct; metadata lookup coherence required explicitly.
   invalid/fallback: eliminate through evaluated supported type and acyclic
     metadata, or use already validated layout identity, never assume them safe.

   Structural interface audit after callback repair:
   A. Static and dynamic compiler callbacks still quantify arbitrary sc/ec,
      but now guard both operand names not_fresh_at sc and sc prefix zero.
      These match the candidate IH's structural entry premises exactly.
      Actual child layout supplies the guards when the callback is used.
   B. Both array callbacks now require a real lookup_block certificate at ec,
      with phi_prefix_length zero. Actual backedge blocks supply it; code
      containment alone is never used to infer PHI freedom or membership.
   C. Tuple and nominal-field callbacks carry the same entry/exit guards.
      normalize_tuple_fields_run maintains compiler-prefix zero in its Inv.
      normalize_fields_suffix_entry transports the enclosing real terminal
      certificate backwards across the remaining field suffix using cs_extends
      plus the checked PHI-safe compiler family. This includes empty tails
      and zero offsets; it never infers membership from an empty fragment.
      Nominal structs reduce to this same traversal using checked lookup and
      stored-size agreement, so need no separate structural suffix theorem.
   D. Reassembly/typing obligations remain: dense and sparse array traversal,
      semantic destination representations after widening, padded-size bounds,
      tuple and struct metadata coherence. Existing projection and widening
      lemmas supply paths, not a checked full recursive contract.
   The repaired callbacks expose the candidate IH's structural premises;
   semantic IH instantiation/reassembly is still a separate obligation.
   This audit is not recursive normalization or a proof of the frozen task.
*)

(* Consumer check: legal widening discharges the explicit sparse-default
   bridge. The general equality is already arg_type_fits_default_value. *)
Theorem normalize_sparse_widening_reconstruction:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV stv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  (!j. j < n ==>
    val_in_memory dtv
      (case ALOOKUP kvs j of SOME v => v | NONE => default_value stv)
      (b + j * type_memory_size dtv) m) ==>
  val_in_memory (ArrayTV dtv (Fixed n)) (ArrayV (SArrayV kvs)) b m
Proof
  strip_tac >>
  `default_value stv = default_value dtv` by
    (gvs[type_widens_to_def] >>
     metis_tac[cj 1 arg_type_fits_default_value]) >>
  drule normalize_sparse_typed_keys >> strip_tac >>
  irule normalize_sparse_destination_memory >>
  reverse conj_tac >- simp[] >> qexists_tac `stv` >> simp[]
QED

(* The bytes leaf can choose the actual length witness from typed memory;
   no arbitrary modular preimage of the length word is used. *)
Theorem normalize_bytestring_typed_window_bounds:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p s.vs_memory /\
  val_wf tv v /\ p + type_memory_size tv <= s.vs_alloca_next /\
  d + type_memory_size tv <= s.vs_alloca_next /\
  type_memory_size tv < dimword (:256) ==>
  ?len. mload p s = n2w len /\
    32 + 32 * word_size len < dimword (:256) /\
    p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
    d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
    val_footprint tv v <= 32 + 32 * word_size len
Proof
  strip_tac >> drule_all buffer_typed_bytestring_header >> strip_tac >>
  `val_store_size tv v <= type_memory_size tv` by
    metis_tac[exprSimTheory.val_store_size_le] >>
  `val_footprint tv v <= val_store_size tv v` by
    metis_tac[exprSimTheory.val_footprint_le_store_size] >>
  qexists_tac `len` >> simp[] >> decide_tac
QED

(* Semantic audit after C1.3.16/17 (no recursive theorem asserted here).

   Checked branch interfaces:
   - Word: compileEnv.type_widens_to_word forces syntax equality;
     normalize_word_window_cont then consumes destination typing/memory.
   - Bytes: valueCopyBytes.bytestring_val_in_memory_transfer changes the
     semantic type; buffer_typed_bytestring_header chooses the actual length.
     normalize_bytestring_typed_window_bounds above supplies every padded
     runtime read/write bound of normalize_bytestring_window_cont when its
     input representation is at that type. Widening must transfer typing and
     supply both padded enclosing windows; it cannot use just payload length.
   - Static bulk: type_widens_to_static_identity and
     typed_static_fast_evaluated_identity (typedNormalizeStaticRigidity)
     remove the false equal-size-implies-equal-representation inference.
   - Arrays: elems_in_memory_EL/intro are the dense indexed equivalence;
     normalize_sparse_memory_index and normalize_sparse_typed_keys handle
     sparse key uniqueness/domain. normalize_sparse_widening_reconstruction
     above discharges the source/destination default gap from actual legal
     element widening, using arg_type_fits_default_value. Dynamic rebuilding
     uses normalize_dynamic_destination_memory; type_widens_to_dynamic_array
     supplies capacity order, with runtime length obtained from value typing.
   - Fields: normalize_tuple_memory_index and normalize_fields_memory_index
     reconstruct ordered lists; normalize_tuple_compiler_offsets and
     normalize_fields_compiler_offsets consume LIST_REL size agreement.
     make_struct_fields_map_consistent supplies ordered names/types, not just
     lookup agreement. evaluated StructTV fields use evaluate_types and ZIP;
     type_memory_size correspondence comes from checked_return_frame_metadata.
     Full nominal child instantiation is not asserted by those equations alone.

   Important newly located reusable S1 infrastructure:
   typedMemoryCopyTheory was built during this audit. Its
   compile_store_memory_typed_run is admission-free (the source checks tags
   of every exported theorem at theory end) and covers recursive typed stores.
   typed_copy_rank_entry handles all recursion phases by destination type_rank.
   typed_copy_sarray_representation, typed_copy_dynarray_reconstruct,
   typed_copy_tuple_cursor/fields_cursor, typed_copy_default_widening and
   typed_copy_struct_fields_producer are existing semantic paths to reuse.
   typed_copy_elems_indexed and typed_copy_sarray_indexed overlap the recently
   built semantic reconstruction boundaries; do not introduce further variants.
   This S1 theorem gives the final memory, frames, endpoint and run refinement,
   NOT mem_cont_sim or safety of intermediate reads. Thus it is not the missing
   S3 proof, but a new integration strategy should reuse its semantic contracts.

   Proposed S3 contract remains the universally quantified candidate above,
   with val_wf at both source/destination added explicitly, value typing at both
   types, metadata ordered type consistency and per-field size/distinctness.
   Its source memory/window, operand freshness, nonhalted endpoint, and
   source val_wf come from the expression boundary/stmt_state_rel. Destination
   typing follows type_widens_to_value_has_type; destination val_wf and strict
   word-address windows must be checked at the normalization allocation site,
   NOT assumed to follow merely from s.vs_alloca_next. Metadata size/acyclicity
   comes from initial_return_frame_metadata and same_frame_return_metadata.
   Child runtime, entry/exit certificates, prefix zero and old operands are
   already universally guarded by the repaired loop/field callbacks.
   Remaining integration: attach semantic child IHs/locality and padded slot
   bounds to all five actual compiler phases, discharge destination val_wf,
   and align nominal evaluated fields and metadata under recursive tenv deletion.
   No fallback branch may be discarded without evaluated-type/typing evidence.
   Return producer discharge and the full recursive S3 continuation are still
   unproved. The checked S1 recursive result is a strategy input, not a reason
   to start the frozen theorem or silently treat final-state frames as safety.
*)

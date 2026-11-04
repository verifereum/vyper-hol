(* Bounded recursive-interface diagnostic, not a normalization correctness theorem. *)
Theory typedNormalizeContractProbe
Ancestors
  typedCopyAgreement typedNormalizeDynarrayLoop typedNormalizeLoop
  typedNormalizeContinuation typedNormalizeFields typedNormalizeFrame
  compileEnv emitHelper venomInst list arithmetic

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

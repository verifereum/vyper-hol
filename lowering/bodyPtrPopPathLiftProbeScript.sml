Theory bodyPtrPopPathLiftProbe
Ancestors bodyPtrPopSpatialSplit exprSimPop valueEncoding valueEncodingProps
  bodyPtrDefs vyperState loweringPosts

(* One enclosing dynamic owner. This checks the local split's address interface;
   it does not claim robustness of the containing value or history framing. *)
Theorem pop_singleton_containing_store_probe:
  vs <> [] /\ elems_val_wf vs tv /\
  w2n (a:bytes32) = p + 32 /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  val_in_memory (ArrayTV (ArrayTV tv (Dynamic cap)) (Dynamic outer_cap))
    (ArrayV (DynArrayV [ArrayV (DynArrayV vs)])) p s.vs_memory /\
  t = ((mstore (w2n a) (n2w (LENGTH vs - 1)) s)
    with vs_inst_idx := SUC s.vs_inst_idx) ==>
  val_in_memory (ArrayTV (ArrayTV tv (Dynamic cap)) (Dynamic outer_cap))
    (ArrayV (DynArrayV [ArrayV (DynArrayV (FRONT vs))])) p t.vs_memory
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (FRONT vs))) (w2n a) mem` by
    (rpt strip_tac >> irule pop_shortened_owner_robust_store >>
     simp[] >> qexistsl_tac [`s`, `tn`] >> gvs[]) >>
  `val_in_memory (ArrayTV tv (Dynamic cap))
    (ArrayV (DynArrayV (FRONT vs))) (w2n a) t.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  gvs[val_in_memory_def] >>
  simp[mstore_mem_word_at_disjoint]
QED

(* Path-lifting interface audit (not additional assumed theorems).

   Offsets: loweringPosts.mem_step_offset_def / mem_path_offset_def use
   capacity bounds for arrays; successful evaluate_subscripts is needed for
   live-index bounds. exprSimProps.mem_path_offset_sound supplies both the
   leaf type and k + type_memory_size leaf <= type_memory_size root.

   Source: vyperState.assign_subscripts_def recurses through integer array
   indices and struct fields. array_set_index (vyperValueOperation) updates
   DynArrayV via TAKE/DROP and SArrayV via sparse key replacement, but rejects
   TupleV. Thus a successful assignment or mutable_place_path is essential;
   a successful tuple read and offset alone do not imply replacement exists.
   exprSimPopNestedLocalPath.assign_subscripts_replace_readback already gives
   existence and same-path readback for typed mutable paths. Do not duplicate.

   Representation: valueEncoding.val_in_memory_def expands arrays to a header
   and elems_in_memory, sparse arrays to kvs plus represented defaults, tuples
   to tuple_in_memory and structs to fields_in_memory. In particular sparse
   absent keys require framing their default values, not just listed keys.
   exprSimAggregateEncoding.elems_in_memory_EL / intro and
   normalizationPrefixPtr.robust_dynarray_assemble are the array interfaces.

   Proposed reusable lifting boundary:
     well_formed_type_value rt, value_has_type rt root, val_wf rt root,
     evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)),
     assign_subscripts rt root path (Replace (ArrayV (DynArrayV (FRONT vs))))
       = INL updated,
     mem_path_offset rt path = SOME (k,ArrayTV tv (Dynamic cap)),
     vs <> [], elems_val_wf vs tv, w2n dst = base + k,
     robust representation of root at base in s under tn.t_mem,
     t = mstore at dst of LENGTH vs - 1 (with PC increment)
   should imply robust representation of updated at base under unchanged tn,
   and robust LAST vs at base+k+32+(LENGTH vs-1)*type_memory_size tv.
   No unexplained sibling separation belongs in this consumer statement.

   Remaining one-step robust obligations (this probe only checks the concrete
   endpoint for a singleton outer array): derive robust selected-child
   extraction and frame the outer header under arbitrary allowed dirty-memory
   perturbations. For outer child i != j at b_i = base+32+i*stride,
   robust_val_in_memory_exterior_frame applies with writes=[b_j,b_j+32),
   provided val_wf child_i and
     !x. b_i <= x /\ x < b_i + val_footprint etv child_i ==>
         ~(b_j <= x /\ x < b_j+32).
   val_footprint_le, 32 <= stride for a dynamic-array element, and fixed
   strides supply this separation; mstore_memory_frame supplies byte equality.
   This is not separation of historical owners, whose capacity windows can
   overlap. pop_retained_forest supplies none of the required reachable
   nonselected-owner compatibility, nor representation for an opaque-history
   owner selected by a mutation outside Q. Those remain separate obligations.
*)

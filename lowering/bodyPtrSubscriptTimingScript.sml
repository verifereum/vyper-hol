(* Source-timing probes, not counterexamples to the frozen pointer theorem. *)
Theory bodyPtrSubscriptTiming
Ancestors
  vyperInterpreter vyperState exprSimDefs

Theorem pop_two_local_result:
  FST (pop_place cx (MemoryPlace "x" [])
    (st with scopes := [FEMPTY |+ ("x",
      <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 2);
        value := ArrayV (DynArrayV [IntV 7; IntV 0]); popped := []|>)])) =
  INL (PlaceR (MemoryPlace "x" [ValueSubscript (IntV 1)]))
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem nested_mapping_not_vv_admissible:
  ~expr_vv_res_ok (INL (HashMapRef F 0w (BaseT (UintT 256))
                        (Type (BaseT (UintT 256)))))
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem pop_two_local_read:
  FST (bind (pop_place cx (MemoryPlace "x" [])) (read_result cx)
    (st with scopes := [FEMPTY |+ ("x",
      <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 2);
        value := ArrayV (DynArrayV [IntV 7; IntV 0]); popped := []|>)])) =
  INL (IntV 0)
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem pop_two_local_current_base:
  FST (bind (pop_place cx (MemoryPlace "x" []))
    (\r. read_place cx (MemoryPlace "x" []))
    (st with scopes := [FEMPTY |+ ("x",
      <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 2);
        value := ArrayV (DynArrayV [IntV 7; IntV 0]); popped := []|>)])) =
  INL (ArrayV (DynArrayV [IntV 7]))
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem subscript_pop_two_local:
  FST (eval_expr cx
    (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Dynamic 2)) "x")
      (Pop (BaseT (UintT 256)) (NameTarget "x")))
    (st with scopes := [FEMPTY |+ ("x",
      <|assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Dynamic 2);
        value := ArrayV (DynArrayV [IntV 7; IntV 0]); popped := []|>)])) =
  INL (PlaceR (MemoryPlace "x" [ValueSubscript (IntV 0)]))
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

(* Consumer-validation matrix (C1.7.3).
   Actual source prefix: eval_expr_def, Subscript clause, is
     bind (eval_expr cx base) (\res.
       bind (eval_expr cx idx) (\ir.
         bind (read_result cx ir) (\v.
           select_result cx (expr_type base) res (ValueSubscript v))))
   Base failure: no index or select; needs the error_eval_result certificate
   for gas_outcome_ptr_bind and expr_exit transport, not a normal frame.
   Index/read failure: no select; needs bind_eval_result and error_value
   certificate lifting, not child representation. These certificates remain
   integration obligations; this diagnostic does not certify them.

   Tuple/struct: compiler skips index execution using literal_int_index.
   Source still evaluates idx. Need typing-derived literal index purity and
   gas observation correspondence before replacing it by a constant offset.
   The ADD edge and child full-buffer layout are separate unresolved outputs.

   Array: compiler runs compile_expr base, then lower_value idx, THEN loads
   dynamic length and checks bounds. Source select_result on a PlaceR reads
   the CURRENT place (extend_place_def), not its old value. Timing agrees in
   the checked local x[x.pop()] example: popped index = 0, current base [7],
   result is x[0]. The old base [7;0] is not preserved. In contrast Value v
   is captured and select_result uses v directly. For an owned allocation,
   expr_post_operand_kept requires local-disjointness; vv_at may instead
   choose its local_val_at alternative. That alternative is not a generic
   place-pointer relation. Needed current-place boundary, still unresolved:
     vv_post ... res (LocatedValue bt p) t0 /\ index normal post ... t ==>
     place_ptr_rel cenv cx t res w (SOME p.ptr_location) vt
   where vt is the base's source value_type, with eval_operand p.ptr_operand t = SOME w, followed by current-state
   read_result/representation and the child's ptr_vv_ok/ptr_buf_ok.
   No theorem here asserts that implication: vv_holds/vv_at describe values,
   not source-place identity. ghost_inv_local_representation supplies the
   current root's bytes only AFTER its identity/address is established.
   expr_sim_ptr_captured_ptr_covers supplies unchanged address/provenance,
   clean taint and allocation coverage only, not this missing identity.

   Mapping: compiler runs lower_value key, optional bytestring hash, then
   scratch MSTORE/MSTORE/SHA3. Nested mapping base is HashMapRef; its source
   extension returns another HashMapRef or a StoragePlace (extend_place_def).
   The checked rejection by expr_vv_res_ok means the base's vv judgment
   cannot be called with gas_admissible ... expr_vv_res_ok for a successful
   HashMapRef. A specialized mapping prefix is needed or this admissibility
   premise must be derived some other way; operand induction alone does not
   supply it. ptr_vv_ok_nonmemory does not require read_result, but vv_holds
   and the operand execution boundary still do. This is an explicit gap.

   Restrictions: expr_body_pre_def DOES NOT require supported_expr. Its
   no-EVM-run, typing, width, allocation and internal-call conditions do not
   exclude a local Pop merely because supported_effect_expr excludes it.
   Thus the supportedExprs local-Pop rejection cannot close this frame gap.
   No full counterexample to subscript_expr_ptr_ok has been established.

   Gas reset: gas_outcome_ptr_bind_normal continues at
     (mid with gas_obs := [], t, G1, tn1), not (mid,t,G1,tn1).
   C1.7.2 can be instantiated at that reset state only after recovering
   stmt_state_rel, ghost_inv and gas_admissible there; reset transport and
   both exempt-certificate lifts are still required for full prefix bind.
*)

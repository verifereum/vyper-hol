(* Post-interface probe only. Updating provenance here makes no assertion
   about reachability of the updated ghost along the original RHS path. *)
Theory augAssignPtrAddPostProbe
Ancestors
  augAssignPtrProvenanceProbe augAssignPtrScalarWitnessProbe bodyPtrDefs
  exprLowering compileEnv context emitHelper finite_map ptrDiscipline venomInst

Theorem uint256_safe_add_sequence:
  compile_safe_add x y (BaseT (UintT 256)) =
  comp_bind (emit_op ADD [x; y]) (\res.
    comp_bind (emit_op LT [res; x]) (\lt_res.
      comp_bind (emit_op ISZERO [lt_res]) (\ok.
        comp_ignore_bind (emit_void ASSERT [ok]) (comp_return res))))
Proof
  simp[compile_safe_add_def, type_bits_def, is_signed_type_def]
QED

Theorem ghost_inv_tag_fresh_result:
  ghost_inv d cenv cx ee G tn t /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa rhs /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) ==>
  ghost_inv d cenv cx ee (G |+ (rhs, site)) tn t
Proof
  strip_tac >>
  `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     p <> rhs` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[ghost_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `p <> rhs` by metis_tac[] >>
      first_x_assum (drule_then strip_assume_tac) >>
      gvs[ptr_covers_def, FLOOKUP_UPDATE]) >>
  simp[] >> Cases_on `d` >> fs[return_buf_ptr_def] >>
  PairCases_on `x` >> fs[return_buf_ptr_def] >>
  `x <> rhs` by metis_tac[] >>
  fs[ptr_covers_def, FLOOKUP_UPDATE]
QED

Theorem ghost_kept_tag_fresh_result:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ~not_fresh_at sa rhs ==>
  ghost_kept cenv es sa G0 tn0 s0 (G |+ (rhs, site)) tn
Proof
  simp[ghost_kept_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* Tagging a fresh result preserves ghost_inv and ghost_kept, but no longer
   preserves the word ptr_val_ok post: that post now requires provenance NONE. *)

Theorem tagged_fresh_result_breaks_add_guard:
  FLOOKUP G left = NONE /\ left <> rhs /\ result <> left ==>
  ~access_ok lo
    (step_prov PG (G |+ (rhs, site))
      (mk_inst addid ADD [Var left; Var rhs] [result]) u)
    fn (mk_inst guardid LT [Var result; Var left] [out]) s
Proof
  strip_tac >> irule clean_add_guard_obstruction >>
  simp[FLOOKUP_UPDATE]
QED

(* The former tagged local-name post probe is excluded by ptr_val_ok_word:
   a tagged RHS cannot retain the normal word postcondition. *)

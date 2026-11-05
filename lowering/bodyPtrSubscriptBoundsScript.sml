(* Diagnostic for the scalar bounds-check interface: cleanliness does not
   imply absence of pointer provenance for an unsigned comparison. *)
Theory bodyPtrSubscriptBounds
Ancestors
  ptrSafeRun ptrDiscipline venomInst finite_map bodyPtrDefs
  exprLowering emitHelper compileEnv emitHelperProps

Theorem bounds_lt_requires_provenance_compatibility:
  x <> y ==>
  ~access_ok 0 (FEMPTY |+ (x,(0,32))) func
    (mk_inst id LT [Var x; Var y] [out]) s
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[access_ok_def] >>
  disch_then (mp_tac o CONJUNCT2) >>
  disch_then (qspecl_then [`x`, `y`] mp_tac) >>
  simp[mk_inst_def, FLOOKUP_UPDATE]
QED

(* A general producer boundary: non-pointer-producing instructions kill
   provenance for every output, regardless of the incoming ghost map. *)
Theorem step_prov_output_none:
  out_prov PG G inst t = NONE /\ MEM x inst.inst_outputs ==>
  FLOOKUP (step_prov PG G inst t) x = NONE
Proof
  strip_tac >> Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem mload_output_provenance_none:
  inst.inst_opcode = MLOAD /\ MEM x inst.inst_outputs ==>
  FLOOKUP (step_prov PG G inst t) x = NONE
Proof
  strip_tac >> irule step_prov_output_none >> simp[out_prov_def]
QED

Theorem word_ptr_val_ok_does_not_exclude_provenance:
  is_word_type ty /\ op_taint tn (Var x) = {} ==>
  ptr_val_ok cx ty v (Var x) (FEMPTY |+ (x,site)) tn s /\
  op_prov (FEMPTY |+ (x,site)) (Var x) = SOME site
Proof
  simp[ptr_val_ok_def, op_prov_def, FLOOKUP_UPDATE]
QED

Theorem emitted_operand_reserved:
  emit_op opc ops sa = (Var out,sb) ==>
  not_fresh_at sb out /\
  (!p. not_fresh_at sa p ==> p <> out)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
  strip_tac >> gvs[]
QED

(* Audit of the actual consumer (compile_array_subscript_def):
   - A static length is Lit, so access_ok's two-variable comparison clause
     is vacuous, even if the index happens to have provenance.
   - A dynamic length is a fresh MLOAD result. Its provenance is NONE by
     mload_output_provenance_none. For distinct variable operands the LT
     clause therefore requires the index variable's provenance to be NONE.
   - ptr_val_ok and expr_post do not supply that property for word indices.
     ghost_inv constrains PtrVar locals, not the provenance of all scalars.
     Scalar Name is not a direct stack passthrough: compile_name_vv returns
     a place, and unwrap_value loads it. The MLOAD case kills provenance,
     but this does not yet establish a theorem for arbitrary word indices
     (notably ADD/SUB, ASSIGN/PHI, and internal-call outputs).
   - Needed reservation premise at suffix entry is
       !x. idx_op = Var x \/ len_op = Var x ==> not_fresh_at sa x.
     lower_value_word_shape (exprWordOperand) supplies the index half at
     index exit under its typing premises. Monotonicity transports it past
     the length read; emitted_operand_reserved supplies the new length.
     The optional SLT must preserve both inputs; each subsequent emit must
     preserve earlier temporaries until their last use. No numerical
     framing alone supplies this reservation property.
   Missing consumer invariant: provenance-free arbitrary word-index output,
   together with its preservation through the intervening length MLOAD.
   This is an interface gap, NOT a counterexample to the frozen theorem. *)

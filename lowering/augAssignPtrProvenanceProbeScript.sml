(* Diagnostic probes only: these do not assert reachability from a source RHS. *)
Theory augAssignPtrProvenanceProbe
Ancestors
  augAssignPtrInterfaces bodyPtrDefs ptrDiscipline venomInst finite_map
  exprLowering context emitHelper compileEnv list

Theorem comparison_one_provenance_fails:
  FLOOKUP G r = SOME site /\ FLOOKUP G l = NONE ==>
  ~access_ok lo G fn (mk_inst id LT [Var r; Var l] [out]) s
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `access_ok _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [access_ok_def, mk_inst_def, instruction_accessors]) >>
  qpat_x_assum `!u w. _` (qspecl_then [`r`, `l`] mp_tac) >>
  fs[FLOOKUP_DEF]
QED

(* A tagged word cannot satisfy the strengthened ptr_val_ok word post.
   The standalone obstruction below deliberately omits that postcondition. *)

Theorem clean_add_guard_obstruction:
  FLOOKUP G left = NONE /\ FLOOKUP G right = SOME site /\ result <> left ==>
  ~access_ok lo
    (step_prov PG G (mk_inst addid ADD [Var left; Var right] [result]) u)
    fn (mk_inst guardid LT [Var result; Var left] [out]) s
Proof
  strip_tac >> irule comparison_one_provenance_fails >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* A word local is never unwrapped to its existing pointer variable: the
   actual compiler loads it. Thus an arbitrary tagged local pointer is not
   a reachable witness to the abstract guard obstruction above. *)
Theorem local_word_rhs_is_load:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar ptr_op sz) /\ is_word_type ty ==>
  comp_bind (compile_name_vv cenv ty name) (unwrap_value cenv) = emit_op MLOAD [ptr_op]
Proof
  simp[compile_name_vv_def, unwrap_value_def, comp_bind_def, comp_return_def,
       mk_ptr_def, compile_ptr_load_def, FUN_EQ_THM]
QED

Theorem load_result_has_no_provenance:
  MEM opc [MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==>
  op_prov (step_prov PG G (mk_inst id opc [src] [tmp]) u) (Var tmp) = NONE
Proof
  simp[MEM] >> strip_tac >> gvs[step_prov_def, out_prov_def, set_prov_def,
    mk_inst_def, op_prov_def, FLOOKUP_DRESTRICT]
QED

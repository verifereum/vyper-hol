Theory concretizeLayoutCalleeRoots
Ancestors concretizeLayoutArgumentRoots concretizeLayoutParameterRoots
  frameRelocationCleanOperands frameRelocationGuardedValues
  frameRelocationGhostCopy frameResolvedOrigins frameRelocationOpaque
  venomExecSemantics venomState ptrDiscipline finite_map list

Definition clean_resolved_root_def:
  clean_resolved_root L entry (x:bytes32) y <=>
    case entry of
      NONE => x = y
    | SOME (tok,(b,sz)) => x - n2w b = y - n2w (L tok)
End

(* Missing annotations are scalar roots, matching PARAM provenance. *)
Definition resolved_parameter_entry_def:
  resolved_parameter_entry rp i = if i < LENGTH rp then EL i rp else NONE
End

Theorem resolved_parameter_entry_empty[simp]:
  resolved_parameter_entry [] i = NONE
Proof
  simp[resolved_parameter_entry_def]
QED

Theorem resolved_parameter_entry_bound[simp]:
  i < LENGTH rp ==> resolved_parameter_entry rp i = EL i rp
Proof
  simp[resolved_parameter_entry_def]
QED

Theorem resolved_parameter_entry_unbound[simp]:
  ~(i < LENGTH rp) ==> resolved_parameter_entry rp i = NONE
Proof
  simp[resolved_parameter_entry_def]
QED

Theorem parameter_roots_empty_annotations[simp]:
  parameter_roots (\i x y. clean_resolved_root L
    (resolved_parameter_entry [] i) x y) xs xs
Proof
  simp[parameter_roots_def, clean_resolved_root_def]
QED

Theorem parameter_roots_bounded_annotations:
  LENGTH rp = LENGTH xs ==>
  (parameter_roots (\i x y. clean_resolved_root L
    (resolved_parameter_entry rp i) x y) xs ys <=>
   parameter_roots (\i x y. clean_resolved_root L (EL i rp) x y) xs ys)
Proof
  simp[parameter_roots_def, resolved_parameter_entry_def]
QED

Theorem decoded_invoke_argument_clean:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name,ops) /\ MEM op ops ==>
  op_taint tn op = {} /\ (!v. op = Var v ==> ~retpc_var fn v)
Proof
  simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[]
  >- (irule taint_ok_operand_exclusion >>
      qexistsl_tac [`fn`, `inst`, `s`] >> simp[]) >>
  `MEM (Var v) inst.inst_operands` by simp[] >>
  drule_all disciplined_retpc_operand_use >> simp[]
QED

Theorem argument_value_clean_root:
  argument_value Opaque L rv tn op x y /\ op_taint tn op = {} /\
  (!v. op = Var v ==> ~Opaque v) ==>
  clean_resolved_root L (resolved_op rv op) x y
Proof
  Cases_on `op` >> simp[argument_value_def, resolved_op_def,
    clean_resolved_root_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP rv s` >>
  gvs[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
      clean_resolved_root_def]
  >- metis_tac[word_agree_except_empty] >>
  PairCases_on `x'` >> gvs[]
QED

Theorem disciplined_invoke_roots:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name,ops) /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) Rmem Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operands ops s = SOME args ==>
  ?args'. eval_operands ops t = SOME args' /\
    parameter_roots (\i x y. clean_resolved_root L
      (EL i (MAP (resolved_op rv) ops)) x y) args args'
Proof
  rpt strip_tac >> drule_all argument_roots_evaluation >> strip_tac >>
  qexists_tac `args'` >> simp[] >>
  fs[parameter_roots_def] >> rpt strip_tac >>
  `i < LENGTH ops` by simp[] >>
  `MEM (EL i ops) ops` by (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  drule_all decoded_invoke_argument_clean >> strip_tac >>
  simp[EL_MAP] >> irule argument_value_clean_root >>
  qexistsl_tac [`retpc_var fn`, `tn`] >> simp[]
QED

Theorem disciplined_invoke_setup_roots:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name,ops) /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) Rmem Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME sc /\ ~NULL target.fn_blocks ==>
  ?args' tc. eval_operands ops t = SOME args' /\
    setup_callee target args' t = SOME tc /\
    parameter_roots (\i x y. clean_resolved_root L
      (EL i (MAP (resolved_op rv) ops)) x y) sc.vs_params tc.vs_params
Proof
  rpt strip_tac >> drule_all disciplined_invoke_roots >> strip_tac >>
  drule_all parameter_roots_setup_callee >> strip_tac >> metis_tac[]
QED

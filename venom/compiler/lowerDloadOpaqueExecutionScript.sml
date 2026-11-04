Theory lowerDloadOpaqueExecution
Ancestors
  unitShapeDefs execEquivParamBase venomExecSemantics venomInst
  contextCodegenRel list lowerDloadReturnBoundary lowerDloadOrdinaryExecution
  finite_map pred_set venomState lowerDloadPairedBoundary
  lowerDloadOwnership ptrDiscipline

(* Opaque return-PC values cannot be observed by ordinary instructions. *)
Theorem ld_retpc_observable_operand:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode <> ASSIGN /\ i.inst_opcode <> PHI /\
  ~MEM i.inst_opcode [RET; RETFMP; DRET] /\
  MEM (Var x) i.inst_operands ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]
QED

(* Only the final operand is permitted to carry an opaque return token. *)
Theorem ld_retpc_return_front:
  opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  MEM i.inst_opcode [RET; RETFMP; DRET] /\
  MEM (Var x) (FRONT i.inst_operands) ==> ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  `i.inst_operands <> []` by (strip_tac >> gvs[]) >>
  `MEM (Var x) i.inst_operands` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> rpt strip_tac >>
  gvs[GSYM SNOC_APPEND, FRONT_SNOC]
QED

(* Contraposition of the seeded closure: a nonopaque output of a copy
   cannot have obtained its value from an opaque input.  The seed is
   arbitrary, so the same interface also covers opaque gas variables. *)
Theorem ld_copy_nonopaque_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [Var y] /\ MEM x i.inst_outputs /\
  ~copy_phi_var origin fn x ==> ~copy_phi_var origin fn y
Proof
  metis_tac[copy_phi_var_assign]
QED

Theorem ld_phi_nonopaque_selected_input:
  MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  resolve_phi prev i.inst_operands = SOME (Var y) /\
  MEM x i.inst_outputs /\ ~copy_phi_var origin fn x ==>
  ~copy_phi_var origin fn y
Proof
  strip_tac >> strip_tac >>
  `MEM (Var y) i.inst_operands` by metis_tac[resolve_phi_MEM] >>
  metis_tac[copy_phi_var_phi]
QED

Theorem ld_nonopaque_operands_clean:
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!op. MEM op ops ==> (!v. op = Var v ==> v IN V /\ ~retpc_var fn v) /\
    ld_op_prov AG op = NONE /\ op_taint tn op = {}) ==>
  eval_operands ops s = eval_operands ops t
Proof
  strip_tac >> irule ld_owned_operands_clean >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_ret_front_equal:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM i (fn_insts fn) /\
  i.inst_opcode = RET /\ FDOM AG SUBSET fn_pv P fn /\ taint_ok fn tn i s /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) ==>
  eval_operands (FRONT i.inst_operands) s =
  eval_operands (FRONT i.inst_operands) t
Proof
  strip_tac >> irule ld_nonopaque_operands_clean >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >>
  `MEM op i.inst_operands` by
    (Cases_on `i.inst_operands = []` >- gvs[] >>
     metis_tac[APPEND_FRONT_LAST, MEM_APPEND]) >>
  drule_all ld_ret_operand_scalar >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[ld_retpc_return_front, MEM]
QED

(* Whole-support definedness is deliberately independent of owned values. *)
Theorem ld_supported_operand_defined:
  s.vs_labels = t.vs_labels /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!v. op = Var v ==> v IN V) ==>
  (eval_operand op s = NONE <=> eval_operand op t = NONE)
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem ld_supported_operands_defined:
  !ops. s.vs_labels = t.vs_labels /\
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    (!v. MEM (Var v) ops ==> v IN V) ==>
    (eval_operands ops s = NONE <=> eval_operands ops t = NONE)
Proof
  Induct >- simp[eval_operands_def] >>
  rpt strip_tac >> simp[eval_operands_def] >>
  `eval_operand h s = NONE <=> eval_operand h t = NONE` by
    (irule ld_supported_operand_defined >> simp[] >>
     qexists_tac `V` >> metis_tac[MEM]) >>
  `eval_operands ops s = NONE <=> eval_operands ops t = NONE` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >> gvs[] >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >> gvs[]
QED

(* Updating a variable outside the tracked support needs no value relation. *)
Theorem ld_owned_vars_update_supported:
  ld_owned_vars V E AG AH tn un s t /\
  (out IN V ==> ld_owned_value E ps pt Ms Mt x y) ==>
  ld_owned_vars V E (ld_set_prov AG [out] ps) (ld_set_prov AH [out] pt)
    (tn with t_var := set_var_taint tn.t_var [out] Ms)
    (un with t_var := set_var_taint un.t_var [out] Mt)
    (update_var out x s) (update_var out y t)
Proof
  Cases_on `out IN V`
  >- metis_tac[ld_owned_vars_update] >>
  simp[ld_owned_vars_def, update_var_def] >> rpt strip_tac >>
  `v <> out` by metis_tac[] >>
  gvs[update_var_def, lookup_var_def, op_taint_def, set_var_taint_def,
      ld_set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `ps` >> Cases_on `pt` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_lookup_defined_update:
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  !v. v IN V ==>
    (lookup_var v (update_var out x s) = NONE <=>
     lookup_var v (update_var out y t) = NONE)
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED


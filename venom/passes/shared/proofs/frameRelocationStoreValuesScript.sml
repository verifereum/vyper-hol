Theory frameRelocationStoreValues
Ancestors frameRelocationStoreDemand frameRelocationGuardedValues
  frameRelocationOpaque ptrDiscipline memLocDefs pointerConfinedDefs
  frameRelocationLocal frameRelocationValues frameRelocationGhostCopy
  venomState venomExecSemantics finite_map list pred_set words

Theorem mstore_value_origin_free:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) ==>
  !v. opv = Var v ==> FLOOKUP rv v = NONE
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `v IN fn_pv P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `opd = Var v` >> gvs[]
QED

Theorem guarded_masked_operand:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> ~Opaque v /\ FLOOKUP rv v = NONE) /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ word_agree_except (op_taint tn op) x y
Proof
  strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, op_taint_def]
  >- simp[word_agree_except_def]
  >- (`variable_domains s t` by metis_tac[local_rel_domains] >>
      `?y. lookup_var s' t = SOME y` by
        (qpat_x_assum `variable_domains s t` mp_tac >>
         simp[variable_domains_def] >>
         disch_then (qspec_then `s'` mp_tac) >>
         Cases_on `lookup_var s' t` >> simp[]) >>
      qexists_tac `y` >> simp[] >>
      `guarded_bytes Opaque rv tn s' x y` by metis_tac[local_rel_bytes] >>
      gvs[guarded_bytes_def, copy_bytes_def, op_taint_def]) >>
  simp[word_agree_except_def]
QED

Theorem joint_relocation_demand_mstore_value_byte:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ o1_fn_shape C fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  eval_operand opv t = SOME valueT /\ k < 32 /\
  joint_relocation_demand lo positions q0 es qs (SUC c) (w2n dst+k) z ==>
  EL k (word_to_bytes value T) = EL k (word_to_bytes valueT T)
Proof
  strip_tac >>
  `!v. opv = Var v ==> ~retpc_var fn v /\ FLOOKUP rv v = NONE` by
    (rpt strip_tac
     >- (spose_not_then assume_tac >>
         `MEM (Var v) inst.inst_operands` by simp[] >>
         drule_all disciplined_retpc_operand_use >> simp[]) >>
     drule_all mstore_value_origin_free >> simp[]) >>
  `?y. eval_operand opv t = SOME y /\
       word_agree_except (op_taint tn opv) value y` by
    (irule guarded_masked_operand >> metis_tac[]) >>
  `k NOTIN op_taint tn opv` by
    (irule joint_relocation_demand_mstore_lane_clean >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
     goal_assum (drule_at (Pat `EL _ es = _`)) >>
     metis_tac[]) >>
  gvs[word_agree_except_def]
QED

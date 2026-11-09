Theory lowerDloadPtrStoreCommon
Ancestors
  lowerDloadPtrRegion
  lowerDloadPtrRel lowerDloadPtrAffine ptrDiscipline venomExecSemantics
  venomState venomInst codegenRel memLocDefs pointerConfinedDefs
  list pred_set arithmetic words finite_map

Theorem dload_store_payload:
  (i.inst_opcode = MSTORE \/ i.inst_opcode = MSTORE8 \/ i.inst_opcode = ISTORE) /\
  i.inst_operands = [a;v] /\ MEM i (fn_insts f) /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f ==>
  op_prov G v = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `!u. v = Var u ==> u NOTIN fn_pv P f` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> rpt strip_tac >>
     qpat_x_assum `!v'. _` (qspec_then `u` mp_tac) >>
     gvs[] >> Cases_on `a = Var u` >> gvs[]) >>
  Cases_on `v` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem dload_store_region:
  (((i.inst_opcode = MSTORE \/ i.inst_opcode = ISTORE) /\ len = 32) \/
   (i.inst_opcode = MSTORE8 /\ len = 1)) /\
  i.inst_operands = [a;v] /\
  eval_operand a s = SOME x /\ eval_operand v s = SOME val /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  dload_live_layout lo sf tf fs /\
  dload_value_word fs {} (op_prov G a) q x y ==>
  (w2n x = w2n y /\ w2n x + len <= lo) \/
  (?owner id b c n d. dload_live_site fs owner id b c n /\
    w2n x = b+d /\ w2n y = c+d /\ d+len <= n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(lo < w2n x + len \/ op_prov G a <> NONE) ==>
    ?u b sz. a = Var u /\ FLOOKUP G u = SOME (b,sz) /\
      b <= w2n x /\ w2n x + len <= b + sz` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[access_ok_def, source_memory_write_ranges_def,
         fixed_source_write_range_def, mem_write_ops_def] >> metis_tac[]) >>
  irule dload_value_contained_region >>
  conj_tac >- metis_tac[] >>
  qexistsl [`op_prov G a`,`q`] >> simp[] >>
  strip_tac >>
  `?u b sz. a = Var u /\ FLOOKUP G u = SOME (b,sz) /\
    b <= w2n x /\ w2n x + len <= b+sz` by metis_tac[ADD_COMM] >>
  gvs[op_prov_def] >> metis_tac[]
QED

Theorem dload_istore_footprint:
  istore off value s =
    s with <|vs_memory := (mstore off value s).vs_memory;
             vs_immutables := s.vs_immutables |+ (off,value)|>
Proof
  simp[istore_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem key_taint_update:
  key_taint (key_update X key m) k =
    if k = key then m INTER {b | b < 32} else key_taint X k
Proof
  rw[key_taint_def, key_update_def, EXTENSION] >> metis_tac[]
QED

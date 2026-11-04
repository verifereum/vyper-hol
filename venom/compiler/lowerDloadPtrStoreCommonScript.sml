Theory lowerDloadPtrStoreCommon
Ancestors
  lowerDloadPtrRel lowerDloadPtrAffine ptrDiscipline venomExecSemantics
  venomState venomInst codegenRel memLocDefs pointerConfinedDefs
  list pred_set arithmetic words finite_map

Theorem dload_store_payload:
  (i.inst_opcode = MSTORE \/ i.inst_opcode = MSTORE8) /\
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
  ((i.inst_opcode = MSTORE /\ len = 32) \/
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
  qpat_x_assum `_ \/ _` kall_tac >>
  Cases_on `op_prov G a`
  >- (Cases_on `q` >>
      gvs[dload_value_word_def, word_agree_except_bits] >>
      disj1_tac >> conj_tac
      >- (simp[fcpTheory.CART_EQ] >> metis_tac[]) >>
      spose_not_then assume_tac >>
      `lo < w2n x + len` by decide_tac >>
      `?u b sz. a = Var u /\ FLOOKUP G u = SOME (b,sz)` by
        metis_tac[ADD_COMM] >>
      gvs[op_prov_def]) >>
  PairCases_on `x'` >>
  qpat_x_assum `(_ \/ _) ==> _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[op_prov_def] >>
  Cases_on `q` >> gvs[dload_value_word_def] >>
  PairCases_on `x'` >> gvs[dload_pointer_word_def] >>
  `dload_pointer_word fs (b,sz) (x'0,sz) x
     (x - n2w b + n2w x'0)` by
    (simp[dload_pointer_word_def] >> metis_tac[]) >>
  `w2n x <= b+sz` by decide_tac >>
  drule_all dload_pointer_word_interval >> strip_tac >>
  disj2_tac >> qexistsl [`owner`,`id`,`b`,`x'0`,`sz`,`w2n x-b`] >>
  simp[] >> decide_tac
QED

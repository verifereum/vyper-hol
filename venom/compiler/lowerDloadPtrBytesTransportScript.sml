Theory lowerDloadPtrBytesTransport
Ancestors
  lowerDloadPtrMemoryWrite lowerDloadPtrRel lowerDloadPtrExpansionTransport
  codegenRel memLocDefs ptrDiscipline
  pointerConfinedDefs list pred_set words arithmetic finite_map

Theorem dloadbytes_destination_region:
  i.inst_opcode = DLOADBYTES /\
  i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME x /\ eval_operand off s = SOME a /\
  eval_operand sz s = SOME z /\
  access_ok lo G fn i s /\ ~in_revert_forward fn s /\
  dload_live_layout lo sf tf fs /\
  dload_value_word fs {} (op_prov G dst) q x y ==>
  w2n z = 0 \/
  (w2n x = w2n y /\ w2n x + w2n z <= lo) \/
  (?owner id b c n d.
    dload_live_site fs owner id b c n /\
    w2n x = b+d /\ w2n y = c+d /\ d+w2n z <= n)
Proof
  strip_tac >> Cases_on `w2n z = 0` >- gvs[] >>
  gvs[access_ok_def, source_memory_write_ranges_def,
      sized_source_write_range_def, mem_write_ops_def] >>
  qpat_x_assum `!off len. _` kall_tac >>
  Cases_on `op_prov G dst`
  >- (Cases_on `q` >>
      gvs[dload_value_word_def, word_agree_except_bits] >>
      disj1_tac >> conj_tac
      >- (simp[fcpTheory.CART_EQ] >> metis_tac[]) >>
      spose_not_then assume_tac >>
      `lo < w2n x + w2n z` by decide_tac >>
      qpat_x_assum `lo < _ ==> _` drule >>
      strip_tac >> gvs[op_prov_def]) >>
  PairCases_on `x'` >>
  qpat_x_assum `(_ ==> _) ==> _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[op_prov_def] >>
  Cases_on `q` >> gvs[dload_value_word_def] >>
  PairCases_on `x'` >> gvs[dload_pointer_word_def] >>
  `dload_pointer_word fs (b,sz') (x'0,sz') x
     (x - n2w b + n2w x'0)` by
    (simp[dload_pointer_word_def] >> metis_tac[]) >>
  `w2n x <= b+sz'` by decide_tac >>
  drule_all dload_pointer_word_interval >> strip_tac >>
  disj2_tac >> qexistsl [`owner`,`id`,`b`,`x'0`,`sz'`,`w2n x-b`] >>
  simp[] >> decide_tac
QED

Theorem dloadbytes_memory_match_clean_write:
  i.inst_opcode = DLOADBYTES /\
  i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME x /\ eval_operand off s = SOME a /\
  eval_operand sz s = SOME z /\
  access_ok lo G fn i s /\ ~in_revert_forward fn s /\
  dload_live_layout lo sf tf fs /\
  dload_value_word fs {} (op_prov G dst) q x y /\
  dload_memory_match lo fs tn un s t /\ LENGTH bs = w2n z ==>
  dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF {p | w2n x <= p /\ p < w2n x + LENGTH bs})
    (un with t_mem := un.t_mem DIFF {r | w2n y <= r /\ r < w2n y + LENGTH bs})
    (write_memory_with_expansion (w2n x) bs s)
    (write_memory_with_expansion (w2n y) bs t)
Proof
  strip_tac >> drule_all dloadbytes_destination_region >>
  strip_tac
  >- (irule dload_memory_match_clean_write >> simp[]) >>
  irule dload_memory_match_clean_write_region >>
  metis_tac[]
QED

Theorem dloadbytes_scalar_clean:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s ==>
  op_prov G off = NONE /\ op_prov G sz = NONE /\
  op_taint tn off = {} /\ op_taint tn sz = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `!v. MEM (Var v) [off;sz] ==> v NOTIN fn_pv P fn` by
    (gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `v` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >>
     Cases_on `dst = Var v` >> gvs[FILTER] >>
     Cases_on `sz = Var v` >> gvs[] >>
     Cases_on `off = Var v` >> gvs[]) >>
  conj_tac
  >- (Cases_on `off` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `sz` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem dloadbytes_scalar_equal:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s /\ dload_vars_match fs V G H tn un s t /\
  s.vs_labels = t.vs_labels /\
  (!v. off = Var v ==> v IN V) /\ (!v. sz = Var v ==> v IN V) /\
  (eval_operand off s = NONE <=> eval_operand off t = NONE) /\
  (eval_operand sz s = NONE <=> eval_operand sz t = NONE) ==>
  eval_operand off s = eval_operand off t /\
  eval_operand sz s = eval_operand sz t
Proof
  strip_tac >> drule_all dloadbytes_scalar_clean >> strip_tac >>
  conj_tac >> irule scalar_operand_equal >> simp[] >>
  qexistsl [`G`,`H`,`V`,`fs`,`tn`,`un`] >> simp[]
QED

Theorem dloadbytes_common_payload:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s /\ dload_vars_match fs V G H tn un s t /\
  s.vs_labels = t.vs_labels /\
  (!v. off = Var v ==> v IN V) /\ (!v. sz = Var v ==> v IN V) /\
  (eval_operand off s = NONE <=> eval_operand off t = NONE) /\
  (eval_operand sz s = NONE <=> eval_operand sz t = NONE) /\
  s.vs_data_section = t.vs_data_section /\ code_layout_valid t /\
  eval_operand (Label "code_end") t = SOME e /\
  eval_operand off s = SOME a /\ eval_operand sz s = SOME z /\
  w2n a + w2n e < dimword (:256) ==>
  eval_operand off t = SOME a /\ eval_operand sz t = SOME z /\
  TAKE (w2n z) (DROP (w2n (a+e)) t.vs_code ++ REPLICATE (w2n z) 0w) =
  TAKE (w2n z) (DROP (w2n a) s.vs_data_section ++ REPLICATE (w2n z) 0w)
Proof
  strip_tac >> drule_all dloadbytes_scalar_equal >> strip_tac >>
  gvs[] >> drule_all dload_code_data_padded_slice >> simp[]
QED

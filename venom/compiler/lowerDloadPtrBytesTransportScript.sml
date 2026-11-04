Theory lowerDloadPtrBytesTransport
Ancestors
  lowerDloadPtrMemoryWrite lowerDloadPtrRel lowerDloadPtrExpansionTransport
  lowerDloadPtrAggregate lowerDloadPtrCall
  venomExecSemantics venomState codegenRel memLocDefs ptrDiscipline
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

Theorem dloadbytes_state_ghost:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  i.inst_outputs = [] /\ eval_operand dst s = SOME x /\
  eval_operand off s = SOME a /\ eval_operand sz s = SOME z ==>
  step_inst_base i s = OK (write_memory_with_expansion (w2n x)
    (TAKE (w2n z) (DROP (w2n a) s.vs_data_section ++ REPLICATE (w2n z) 0w)) s) /\
  step_prov PG G i (write_memory_with_expansion (w2n x)
    (TAKE (w2n z) (DROP (w2n a) s.vs_data_section ++ REPLICATE (w2n z) 0w)) s) = G /\
  step_taint i s (write_memory_with_expansion (w2n x)
    (TAKE (w2n z) (DROP (w2n a) s.vs_data_section ++ REPLICATE (w2n z) 0w)) s) tn =
    tn with t_mem := tn.t_mem DIFF {j | w2n x <= j /\ j < w2n x + w2n z}
Proof
  strip_tac >>
  simp[step_inst_base_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  simp[step_taint_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, range_bytes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, mem_write_ops_def, written_taint_def,
       FLOOKUP_DEF, write_memory_with_expansion_def,
       taint_component_equality] >>
  simp[DRESTRICT_UNIV, EXTENSION] >> metis_tac[]
QED

Theorem dloadbytes_codecopy_boundary:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  i.inst_outputs = [] /\ eval_operand dst s = SOME x /\
  eval_operand off s = SOME a /\ eval_operand sz s = SOME z /\
  access_ok lo G fn i s /\ ~in_revert_forward fn s /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [tdst;src;tsz] /\
  c.inst_outputs = [] /\ eval_operand tdst t = SOME y /\
  eval_operand src t = SOME b /\ eval_operand tsz t = SOME z /\
  step_inst_base c t = OK t1 /\
  dload_value_word fs {} (op_prov G dst) (op_prov H tdst) x y /\
  bs = TAKE (w2n z) (DROP (w2n a) s.vs_data_section ++ REPLICATE (w2n z) 0w) /\
  bs = TAKE (w2n z) (DROP (w2n b) t.vs_code ++ REPLICATE (w2n z) 0w) ==>
  ?s1. step_inst_base i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH (step_prov PG G i s1)
      (step_prov PH H c t1) (step_taint i s s1 tn)
      (step_taint c t t1 un) s1 t1 cs ds
Proof
  strip_tac >> drule_all dloadbytes_state_ghost >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  drule_all dload_codecopy_state_ghost >>
  disch_then (qspecl_then [`un`,`PH`,`H`] strip_assume_tac) >>
  qexists_tac `write_memory_with_expansion (w2n x) bs s` >>
  conj_tac >- metis_tac[] >>
  `LENGTH bs = w2n z` by simp[LENGTH_TAKE_EQ] >>
  `dload_memory_match lo fs
    (tn with t_mem := tn.t_mem DIFF {p | w2n x <= p /\ p < w2n x + LENGTH bs})
    (un with t_mem := un.t_mem DIFF {p | w2n y <= p /\ p < w2n y + LENGTH bs})
    (write_memory_with_expansion (w2n x) bs s)
    (write_memory_with_expansion (w2n y) bs t)` by
    (irule dloadbytes_memory_match_clean_write >>
     conj_tac >- metis_tac[dload_boundary_layout] >>
     conj_tac >- metis_tac[dload_boundary_memory] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `dload_memory_match _ _ _ _ (write_memory_with_expansion _ _ _) _` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n x) payload s` >>
  fs[dload_boundary_core_def] >>
  conj_tac
  >- (gvs[dload_table_stack_def] >> gen_tac >> Cases_on `k`
      >- (qpat_x_assum `!k. k < _ ==> _ /\ _ /\ _` (qspec_then `0` mp_tac) >>
          simp[write_memory_with_expansion_def]) >>
      qpat_x_assum `!k. k < _ ==> _ /\ _ /\ _` (qspec_then `SUC n` mp_tac) >>
      simp[write_memory_with_expansion_def]) >>
  fs[write_memory_with_expansion_def, dload_vars_match_def, lookup_var_def,
     dload_shared_store_def, dload_equal_environment_def,
     venom_state_component_equality, op_taint_def] >>
  metis_tac[]
QED

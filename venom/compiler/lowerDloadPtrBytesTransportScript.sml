Theory lowerDloadPtrBytesTransport
Ancestors
  lowerDloadPtrMemoryWrite lowerDloadPtrRel lowerDloadPtrExpansionTransport
  lowerDloadPtrAggregate lowerDloadPtrCall lowerDloadPtrPhase lowerDloadDefs instIdxIndep
  lowerDloadPtrBlockEntry
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

Theorem dloadbytes_codecopy_safety:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  i.inst_outputs = [] /\ c.inst_opcode = CODECOPY /\
  c.inst_operands = [dst;src;sz] /\ c.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\ taint_ok f tn i s /\
  dload_live_layout lo sf tf fs /\ dload_vars_match fs V G H tn un s t /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  op_taint un src = {} /\
  (eval_operand src t <> NONE ==> eval_operand off s <> NONE) ==>
  access_ok lo H g c t /\ taint_ok g un c t
Proof
  strip_tac >>
  `!op. MEM op [dst;off;sz] ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!op. MEM op [dst;off;sz] ==> op_taint un op = op_taint tn op` by
    (rpt strip_tac >> Cases_on `op` >>
     gvs[op_taint_def, dload_vars_match_def] >> metis_tac[]) >>
  `!op. MEM op [dst;off;sz] ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule dload_matched_operand_defined >> simp[] >>
     qexistsl [`G`,`H`,`V`,`fs`,`tn`,`un`] >> simp[] >> metis_tac[]) >>
  `(!v. off = Var v ==> v IN V) /\ (!v. sz = Var v ==> v IN V)` by
    (gvs[] >> metis_tac[]) >>
  `eval_operand sz s = eval_operand sz t` by
    (metis_tac[dloadbytes_scalar_equal, MEM]) >>
  conj_tac
  >- (simp[access_ok_def, contextCodegenRelTheory.source_memory_read_ranges_def, mem_read_ops_def] >>
      simp[source_memory_write_ranges_def, sized_source_write_range_def,
           mem_write_ops_def] >>
      Cases_on `eval_operand dst t` >> simp[] >>
      Cases_on `eval_operand src t` >> simp[] >>
      Cases_on `eval_operand sz t` >> simp[] >>
      `eval_operand dst s <> NONE /\ eval_operand off s <> NONE` by
        metis_tac[MEM, optionTheory.NOT_SOME_NONE] >>
      Cases_on `eval_operand dst s` >> gvs[] >>
      Cases_on `eval_operand off s` >> gvs[] >>
      rename1 `eval_operand dst s = SOME sx` >>
      rename1 `eval_operand dst t = SOME ty` >>
      rename1 `eval_operand sz t = SOME zz` >>
      `dload_value_word fs {} (op_prov G dst) (op_prov H dst) sx ty` by
        (metis_tac[dload_matched_operand]) >>
      rpt strip_tac >>
      `w2n zz <> 0` by simp[] >>
      `((lo < w2n sx + w2n zz \/ op_prov G dst <> NONE) ==>
         ?b n. op_prov G dst = SOME (b,n) /\
               b <= w2n sx /\ w2n sx + w2n zz <= b+n)` by
        (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
         simp[access_ok_def, source_memory_write_ranges_def,
              sized_source_write_range_def, mem_write_ops_def,
              contextCodegenRelTheory.source_memory_read_ranges_def] >>
         rpt strip_tac >> gvs[op_prov_def] >> metis_tac[]) >>
      `?b n. op_prov H dst = SOME (b,n) /\
         b <= w2n ty /\ w2n ty + w2n zz <= b+n` by
        (qpat_x_assum `dload_live_layout _ _ _ _` mp_tac >>
         qpat_x_assum `dload_value_word _ _ _ _ _ _` mp_tac >>
         qpat_x_assum `lo < _ \/ _ <> NONE ==> _` mp_tac >>
         qpat_x_assum `op_prov H dst = NONE ==> _` mp_tac >>
         qpat_x_assum `w2n zz <> 0` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         irule dload_value_access_containment >> simp[] >>
         goal_assum (drule_at Any) >> simp[] >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      Cases_on `dst` >> gvs[op_prov_def] >> metis_tac[]) >>
  simp[taint_ok_def, contextCodegenRelTheory.source_memory_read_ranges_def] >> metis_tac[MEM]
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

Theorem dloadbytes_two_step_boundary:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\ a.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var cv;sz] /\ c.inst_outputs = [] /\
  cv NOTIN V /\ dst <> Var cv /\ sz <> Var cv /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s /\ access_ok lo G fn i s /\ ~in_revert_forward fn s /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  dload_prefix_match fuel Ct PH [a;c] 2 t H un t2 H2 un2 ==>
  ?s1. step_inst fuel C i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH (step_prov PG G i s1) H2
      (step_taint i s s1 tn) un2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) t2 cs ds
Proof
  strip_tac >>
  `?v1 v2 t1 H1 un1.
    step_inst fuel Ct a t = OK v1 /\
    t1 = v1 with vs_inst_idx := SUC t.vs_inst_idx /\
    H1 = step_prov PH H a v1 /\ un1 = step_taint a t v1 un /\
    step_inst fuel Ct c t1 = OK v2 /\
    t2 = v2 with vs_inst_idx := SUC t1.vs_inst_idx /\
    H2 = step_prov PH H1 c v2 /\ un2 = step_taint c t1 v2 un1` by
    (qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     `2 = SUC (SUC 0)` by decide_tac >>
     pop_assum (fn th => pure_rewrite_tac[th]) >>
     simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
     gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
     metis_tac[]) >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `step_inst_base a t = OK v1 /\ step_inst_base c t1 = OK v2` by
    (qpat_x_assum `step_inst _ _ c _ = _` mp_tac >>
     qpat_x_assum `step_inst _ _ a _ = _` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `?ox e. eval_operand off t = SOME ox /\
    eval_operand (Label "code_end") t = SOME e /\ v1 = update_var cv (ox+e) t` by
    (qpat_x_assum `step_inst_base _ _ = _` kall_tac >>
     qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `?y z. eval_operand dst t = SOME y /\ eval_operand sz t = SOME z` by
    (qpat_x_assum `step_inst_base c t1 = OK v2` mp_tac >>
     simp[step_inst_base_def, AllCaseEqs()] >> strip_tac >>
     gvs[eval_op_inst_idx] >>
     Cases_on `dst` >> Cases_on `sz` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  suspend "scalar_inputs"
QED

Resume dloadbytes_two_step_boundary[scalar_inputs]:
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t.vs_labels /\ s.vs_data_section = t.vs_data_section /\
   code_layout_valid t` by
    (qpat_x_assum `code_layout_valid s` mp_tac >>
     drule dload_boundary_environment >>
     rpt (pop_assum kall_tac) >>
     simp[dload_equal_environment_def, venom_state_component_equality, code_layout_valid_def] >>
     metis_tac[]) >>
  `!op. MEM op [dst;off;sz] ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule dload_matched_operand_defined >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `(!v. off = Var v ==> v IN V) /\ (!v. sz = Var v ==> v IN V)` by
    (gvs[] >> metis_tac[]) >>
  `(eval_operand off s = NONE <=> eval_operand off t = NONE) /\
   (eval_operand sz s = NONE <=> eval_operand sz t = NONE)` by simp[] >>
  `eval_operand off s = SOME ox /\ eval_operand sz s = SOME z` by
    (drule_all dloadbytes_scalar_equal >> simp[] >> metis_tac[]) >>
  `?x. eval_operand dst s = SOME x` by
    (Cases_on `eval_operand dst s` >> gvs[] >> metis_tac[]) >>
  `w2n ox + w2n e < dimword (:256)` by
    (qpat_x_assum `dload_offset_ok _ _ _ _` mp_tac >>
     qpat_x_assum `code_layout_valid t` mp_tac >>
     qpat_x_assum `code_layout_valid s` mp_tac >>
     qpat_x_assum `eval_operand (Label "code_end") t = _` mp_tac >>
     qpat_x_assum `eval_operand off s = _` mp_tac >>
     qpat_x_assum `s.vs_data_section = _` mp_tac >>
     drule dload_boundary_environment >>
     qpat_x_assum `i.inst_opcode = _` mp_tac >>
     qpat_x_assum `i.inst_operands = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[dload_equal_environment_def, venom_state_component_equality,
          dload_offset_ok_def, code_layout_valid_def, eval_operand_def] >>
     rpt strip_tac >> gvs[] >> fs[dimword_def, LESS_MOD] >> metis_tac[]) >>
  `dload_boundary_core lo fs V Ws PG PH G H1 tn un1 s v1 cs ds` by
    (qpat_assum `H1 = _` SUBST1_TAC >> qpat_assum `un1 = _` SUBST1_TAC >>
     irule dload_boundary_core_add_temporary >> metis_tac[]) >>
  `dload_boundary_core lo fs V Ws PG PH G H1 tn un1 s t1 cs ds` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s v1 _ _`
      (mp_then Any mp_tac dload_boundary_core_index_update) >>
     disch_then (qspecl_then [`SUC t.vs_inst_idx`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
  suspend "paired_copy"
QED

Resume dloadbytes_two_step_boundary[paired_copy]:
  `eval_operand dst t1 = SOME y /\ eval_operand (Var cv) t1 = SOME (ox+e) /\
   eval_operand sz t1 = SOME z /\ t1.vs_code = t.vs_code` by
    (Cases_on `dst` >> Cases_on `sz` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `op_taint tn dst = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> strip_tac >>
     first_x_assum (qspec_then `dst` mp_tac) >> simp[]) >>
  `dload_vars_match fs V G H1 tn un1 s t1` by metis_tac[dload_boundary_vars] >>
  `s.vs_labels = t1.vs_labels` by
    (qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s t1 _ _`
      (mp_then Any mp_tac dload_boundary_environment) >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!v. dst = Var v ==> v IN V` by (gvs[] >> metis_tac[]) >>
  `dload_value_word fs {} (op_prov G dst) (op_prov H1 dst) x y` by
    (qpat_assum `op_taint tn dst = {}` (fn th =>
       once_rewrite_tac[GSYM th]) >>
     irule dload_matched_operand >> simp[] >>
     qexistsl [`V`,`s`,`t1`,`un1`] >> gvs[]) >>
  `TAKE (w2n z) (DROP (w2n ox) s.vs_data_section ++ REPLICATE (w2n z) 0w) =
   TAKE (w2n z) (DROP (w2n (ox+e)) t1.vs_code ++ REPLICATE (w2n z) 0w)` by
    (drule_all dload_code_data_padded_slice >> simp[]) >>
  qmatch_asmsub_abbrev_tac `payload = TAKE (w2n z) (DROP (w2n (ox+e)) t1.vs_code ++ _)` >>
  `payload = TAKE (w2n z) (DROP (w2n ox) s.vs_data_section ++ REPLICATE (w2n z) 0w)` by
    simp[Abbr `payload`] >>
  drule_all dloadbytes_codecopy_boundary >> strip_tac >>
  suspend "indexed_finish"
QED

Resume dloadbytes_two_step_boundary[indexed_finish]:
  qexists_tac `s1` >>
  conj_tac >- simp[step_inst_non_invoke] >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s1 v2 _ _`
    (mp_then Any mp_tac dload_boundary_core_index_update) >>
  disch_then (qspecl_then [`SUC t1.vs_inst_idx`,`SUC s.vs_inst_idx`] mp_tac) >>
  qpat_x_assum `H2 = _` SUBST1_TAC >>
  qpat_x_assum `un2 = _` SUBST1_TAC >>
  qpat_x_assum `t2 = _` SUBST1_TAC >>
  simp[]
QED

Finalise dloadbytes_two_step_boundary

Theorem dloadbytes_two_step_lookup:
  i.inst_opcode = DLOADBYTES /\ i.inst_outputs = [] /\
  a.inst_opcode = ADD /\ a.inst_outputs = [cv] /\
  c.inst_opcode = CODECOPY /\ c.inst_outputs = [] /\
  step_inst fuel C i s = OK s1 /\
  dload_prefix_match fuel Ct PH [a;c] 2 t H un t2 H2 un2 ==>
  (!v. lookup_var v s1 = lookup_var v s) /\
  (!v. v <> cv ==> lookup_var v t2 = lookup_var v t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ i _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `2 = SUC (SUC 0)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  simp[lookup_var_def, write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem dloadbytes_supply_boundary:
  lower_dload_inst_supply supply i = (xs,next) /\
  fresh_ir_var supply = (cv,supply1) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  cv NOTIN V /\ dst <> Var cv /\ sz <> Var cv /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i (fn_insts fn) /\ fn_ptr_ok P fn /\ FDOM G SUBSET fn_pv P fn /\
  taint_ok fn tn i s /\ access_ok lo G fn i s /\ ~in_revert_forward fn s /\
  code_layout_valid s /\ dload_offset_ok C fn i s /\
  dload_prefix_match fuel Ct PH xs 2 t H un t2 H2 un2 ==>
  ?s1. step_inst fuel C i s = OK s1 /\
    dload_boundary_core lo fs V Ws PG PH (step_prov PG G i s1) H2
      (step_taint i s s1 tn) un2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) t2 cs ds /\
    (!v. lookup_var v s1 = lookup_var v s) /\
    (!v. v <> cv ==> lookup_var v t2 = lookup_var v t)
Proof
  strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >>
  Cases_on `fresh_inst_id supply1` >> simp[] >>
  rename1 `fresh_inst_id supply1 = (add_id,supply2)` >>
  Cases_on `fresh_inst_id supply2` >> simp[] >> strip_tac >> gvs[] >>
  suspend "supply_finish"
QED

Resume dloadbytes_supply_boundary[supply_finish]:
  drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
    dloadbytes_two_step_boundary >> simp[] >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`i`,`fn`,`P`,`C`] mp_tac) >> simp[] >>
  impl_tac >- metis_tac[] >>
  strip_tac >> qexists_tac `s1` >> simp[] >>
  drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
    dloadbytes_two_step_lookup >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[]
QED

Finalise dloadbytes_supply_boundary

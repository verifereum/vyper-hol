Theory lowerDloadPtrCopiedSafety
Ancestors lowerDloadPtrRegion lowerDloadPtrRel lowerDloadPtrCompare lowerDloadPtrDynamicSupport
  lowerDloadPtrMCopy lowerDloadPtrLog lowerDloadPtrDelegateInterfaces
  lowerDloadPtrCallBuffers lowerDloadPtrCreate lowerDloadPtrCopy lowerDloadPtrBytesTransport
  lowerDloadPtrRetpcClean lowerDloadPtrJointScalar lowerDloadPtrTerminal lowerDloadPtrForward lowerDloadPtrJointNext lowerDloadDefs ptrDiscipline
  venomExecSemantics venomState venomInst lowerDloadSupplyProofs rich_list finite_map words list pred_set
  contextCodegenRel codegenRel memLocDefs pointerConfinedDefs arithmetic
  lowerDloadPtrAggregate lowerDloadPtrSupport lowerDloadPtrCall o1PassContract
  unitShapeDefs venomWf

Theorem dload_matched_defined_provenance:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> v IN V) /\ eval_operand op t <> NONE ==>
  (op_prov G op = NONE <=> op_prov H op = NONE)
Proof
  strip_tac >>
  `eval_operand op s <> NONE` by metis_tac[dload_matched_operand_defined] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >> gvs[] >>
  drule_all dload_matched_operand >>
  Cases_on `op_prov G op` >> Cases_on `op_prov H op` >>
  simp[dload_value_word_def]
QED

Theorem dload_copied_compare_access:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\ access_ok lo G f i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!v. v IN FDOM H ==> lookup_var v t <> NONE) /\
  (i.inst_opcode = LT \/ i.inst_opcode = GT \/ i.inst_opcode = EQ) /\
  i.inst_operands = [Var u; Var w] /\ (u IN FDOM H \/ w IN FDOM H) ==>
  ?b sz x y. FLOOKUP H u = SOME (b,sz) /\ FLOOKUP H w = SOME (b,sz) /\
    0 < sz /\ eval_operand (Var u) t = SOME x /\
    eval_operand (Var w) t = SOME y /\
    b <= w2n x /\ w2n x <= b+sz /\ b <= w2n y /\ w2n y <= b+sz
Proof
  strip_tac >>
  `u IN V /\ w IN V` by metis_tac[MEM] >>
  `!v. v IN V /\ v IN FDOM H ==> v IN FDOM G` by
    (rpt strip_tac >>
     `eval_operand (Var v) t <> NONE` by
       metis_tac[eval_operand_def] >>
     `op_prov G (Var v) = NONE <=> op_prov H (Var v) = NONE` by
       (drule dload_matched_defined_provenance >>
        disch_then (qspec_then `Var v` mp_tac) >> simp[]) >>
     gvs[op_prov_def, FLOOKUP_DEF]) >>
  `u IN FDOM G \/ w IN FDOM G` by metis_tac[] >>
  qpat_x_assum `access_ok lo G f i s` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  `eval_operand (Var u) t <> NONE /\ eval_operand (Var w) t <> NONE` by
    (gvs[dload_vars_match_def, eval_operand_def] >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
  Cases_on `eval_operand (Var u) t` >>
  Cases_on `eval_operand (Var w) t` >> gvs[] >>
  rename1 `eval_operand (Var u) t = SOME xu` >>
  rename1 `eval_operand (Var w) t = SOME yw` >>
  `dload_value_word fs (op_taint tn (Var u))
    (FLOOKUP G u) (FLOOKUP H u) x xu /\
   dload_value_word fs (op_taint tn (Var w))
    (FLOOKUP G w) (FLOOKUP H w) y yw` by
    (gvs[dload_vars_match_def, eval_operand_def] >> metis_tac[]) >>
  Cases_on `FLOOKUP H u` >> Cases_on `FLOOKUP H w` >>
  gvs[dload_value_word_def] >>
  rename1 `FLOOKUP H u = SOME pu` >>
  rename1 `FLOOKUP H w = SOME pw` >>
  PairCases_on `pu` >> PairCases_on `pw` >>
  metis_tac[dload_pointer_word_comparisons]
QED

Theorem dload_copied_fixed_read_range[local]:
  (i.inst_opcode = MLOAD \/ i.inst_opcode = ILOAD) /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b sz. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,sz) /\ b<=z /\ z+len<=b+sz)
Proof
  strip_tac >>
  (Cases_on `i.inst_operands` >> gvs[source_memory_read_ranges_def] >>
  rename1 `i.inst_operands = off::rest` >>
  Cases_on `rest` >> gvs[] >>
  Cases_on `eval_operand off t` >> gvs[] >>
  rename1 `eval_operand off t = SOME yt` >>
  `eval_operand off s <> NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `eval_operand off s` >> gvs[] >>
  rename1 `eval_operand off s = SOME xs` >>
  `op_taint tn off = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `dload_value_word fs {} (op_prov G off) (op_prov H off) xs yt` by
    (drule dload_matched_operand >>
     disch_then (qspecl_then [`yt`,`xs`,`off`] mp_tac) >> simp[] >> metis_tac[]) >>
  `((lo < w2n xs + 32 \/ op_prov G off <> NONE) ==>
    ?b n. op_prov G off = SOME (b,n) /\
      b <= w2n xs /\ w2n xs + 32 <= b+n)` by
    (gvs[access_ok_def, source_memory_read_ranges_def, mem_read_ops_def] >>
     strip_tac >> first_x_assum drule_all >> strip_tac >>
     gvs[op_prov_def] >> metis_tac[]) >>
  conj_tac
  >- (drule_all dload_value_contained_region >> metis_tac[w2n_11]) >>
  `((lo < w2n yt + 32 \/ op_prov H off <> NONE) ==>
    ?b n. op_prov H off = SOME (b,n) /\
      b <= w2n yt /\ w2n yt + 32 <= b+n)` by
    (match_mp_tac (Q.INST [`p` |-> `op_prov G off`, `x` |-> `xs`]
       dload_value_access_containment) >> simp[] >> metis_tac[]) >>
  simp[mem_read_ops_def] >> rpt strip_tac >>
  `?b n. op_prov H off = SOME (b,n) /\
    b <= w2n yt /\ w2n yt + 32 <= b+n` by metis_tac[] >>
  Cases_on `off` >> gvs[op_prov_def] >> metis_tac[])
QED

Theorem dload_copied_pair_read_size[local]:
  (i.inst_opcode = RETURN \/ i.inst_opcode = REVERT \/ i.inst_opcode = SHA3) /\
  i.inst_operands = [off;sz] /\ MEM i (fn_insts f) /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f ==>
  op_prov G sz = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `!u. sz = Var u ==> u NOTIN fn_pv P f` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >> rpt strip_tac >>
     qpat_x_assum `!v. _` (qspec_then `u` mp_tac) >>
     gvs[] >> Cases_on `off = Var u` >> gvs[]) >>
  Cases_on `sz` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem dload_copied_pair_read_range[local]:
  (i.inst_opcode = RETURN \/ i.inst_opcode = REVERT \/ i.inst_opcode = SHA3) /\
  i.inst_operands = [off;sz] /\ MEM i (fn_insts f) /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_prov G sz = NONE` by metis_tac[dload_copied_pair_read_size] >>
  `op_taint tn sz = {} /\ op_taint tn off = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. sz = Var v ==> v IN V` by metis_tac[MEM] >>
  `eval_operand sz s = NONE <=> eval_operand sz t = NONE` by
    metis_tac[dload_matched_operand_defined] >>
  `eval_operand sz s = eval_operand sz t` by
    metis_tac[scalar_operand_equal] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  (gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
   Cases_on `eval_operand off t` >> gvs[] >>
   Cases_on `eval_operand sz t` >> gvs[] >>
   rename1 `eval_operand off t = SOME yt` >>
   `eval_operand off s <> NONE` by
     (drule dload_matched_operand_defined >>
      disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[]) >>
   Cases_on `eval_operand off s` >> gvs[] >>
   rename1 `eval_operand off s = SOME xs` >>
   `dload_value_word fs {} (op_prov G off) (op_prov H off) xs yt` by
     (drule dload_matched_operand >>
      disch_then (qspecl_then [`yt`,`xs`,`off`] mp_tac) >> simp[] >> metis_tac[]) >>
   rename1 `eval_operand sz t = SOME amount` >>
   `((lo < w2n xs + w2n amount \/ op_prov G off <> NONE) ==>
     ?b n. op_prov G off = SOME (b,n) /\
       b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
     (gvs[access_ok_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, mem_read_ops_def] >>
      strip_tac >> first_x_assum drule_all >> strip_tac >>
      gvs[op_prov_def] >> metis_tac[]) >>
   conj_tac
   >- (drule_all dload_value_contained_region >> metis_tac[w2n_11]) >>
   `((lo < w2n yt + w2n amount \/ op_prov H off <> NONE) ==>
     ?b n. op_prov H off = SOME (b,n) /\
       b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
     (match_mp_tac (Q.INST [`p` |-> `op_prov G off`, `x` |-> `xs`]
        dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
   simp[mem_read_ops_def] >> rpt strip_tac >>
   `?b n. op_prov H off = SOME (b,n) /\
     b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
   Cases_on `off` >> gvs[op_prov_def] >> metis_tac[ADD_COMM])
QED

Theorem dload_copied_mcopy_read_range[local]:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_prov G sz = NONE /\ op_taint tn src = {} /\ op_taint tn sz = {}` by
    metis_tac[dload_mcopy_size_clean] >>
  `!v. sz = Var v ==> v IN V` by metis_tac[MEM] >>
  `eval_operand sz s = NONE <=> eval_operand sz t = NONE` by
    metis_tac[dload_matched_operand_defined] >>
  `eval_operand sz s = eval_operand sz t` by metis_tac[scalar_operand_equal] >>
  `eval_operand dst s = NONE <=> eval_operand dst t = NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `eval_operand src s = NONE <=> eval_operand src t = NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `src` mp_tac) >> simp[] >> metis_tac[MEM]) >>
  gvs[source_memory_read_ranges_def] >>
  Cases_on `eval_operand dst t` >> gvs[] >>
  Cases_on `eval_operand src t` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >>
  Cases_on `eval_operand dst s` >> gvs[] >>
  Cases_on `eval_operand src s` >> gvs[] >>
  rename1 `eval_operand dst s = SOME xd` >>
  rename1 `eval_operand src t = SOME yt` >>
  rename1 `eval_operand src s = SOME xs` >>
  rename1 `eval_operand sz t = SOME amount` >>
  `dload_value_word fs {} (op_prov G src) (op_prov H src) xs yt` by
    (drule dload_matched_operand >>
     disch_then (qspecl_then [`yt`,`xs`,`src`] mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `((lo < w2n xs + w2n amount \/ op_prov G src <> NONE) ==>
    ?b n. op_prov G src = SOME (b,n) /\
      b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`dx` |-> `xd`, `sx` |-> `xs`]
       dload_mcopy_contained) >> simp[]) >>
  conj_tac
  >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
  `((lo < w2n yt + w2n amount \/ op_prov H src <> NONE) ==>
    ?b n. op_prov H src = SOME (b,n) /\
      b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`p` |-> `op_prov G src`, `x` |-> `xs`]
       dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
  simp[mem_read_ops_def] >> rpt strip_tac >>
  `?b n. op_prov H src = SOME (b,n) /\
    b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
  Cases_on `src` >> gvs[op_prov_def] >> metis_tac[ADD_COMM]
QED

Theorem dload_matched_operands_defined:
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) ops ==> v IN V) ==>
  (eval_operands ops s = NONE <=> eval_operands ops t = NONE)
Proof
  Induct_on `ops` >- simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand h s = NONE <=> eval_operand h t = NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `h` mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `eval_operands ops s = NONE <=> eval_operands ops t = NONE` by metis_tac[MEM] >>
  Cases_on `eval_operand h s` >> Cases_on `eval_operand h t` >>
  Cases_on `eval_operands ops s` >> Cases_on `eval_operands ops t` >>
  gvs[eval_operands_def]
QED

Theorem dload_copied_log_read_range[local]:
  i.inst_opcode = LOG /\ i.inst_operands = Lit tc::REVERSE (off::sz::ops) /\
  LENGTH ops = w2n tc /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_prov G sz = NONE /\ op_taint tn sz = {} /\ op_taint tn off = {}` by
    (drule_all dload_log_scalar_clean >> simp[MEM_REVERSE] >> metis_tac[MEM]) >>
  `!v. sz = Var v ==> v IN V` by metis_tac[MEM, MEM_REVERSE] >>
  `eval_operand sz s = NONE <=> eval_operand sz t = NONE` by
    metis_tac[dload_matched_operand_defined] >>
  `eval_operand sz s = eval_operand sz t` by metis_tac[scalar_operand_equal] >>
  `eval_operands ops s = NONE <=> eval_operands ops t = NONE` by
    (drule dload_matched_operands_defined >>
     disch_then (qspec_then `ops` mp_tac) >> simp[] >> metis_tac[MEM, MEM_REVERSE]) >>
  `eval_operand off s = NONE <=> eval_operand off t = NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[MEM, MEM_REVERSE]) >>
  drule_all log_read_ops >> strip_tac >>
  gvs[source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >>
  Cases_on `eval_operands ops t` >> gvs[] >>
  Cases_on `eval_operand off t` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >>
  Cases_on `eval_operands ops s` >> gvs[] >>
  Cases_on `eval_operand off s` >> gvs[] >>
  rename1 `eval_operand off t = SOME yt` >>
  rename1 `eval_operand off s = SOME xs` >>
  rename1 `eval_operand sz t = SOME amount` >>
  `dload_value_word fs {} (op_prov G off) (op_prov H off) xs yt` by
    (drule dload_matched_operand >>
     disch_then (qspecl_then [`yt`,`xs`,`off`] mp_tac) >> simp[] >> metis_tac[MEM, MEM_REVERSE]) >>
  `((lo < w2n xs + w2n amount \/ op_prov G off <> NONE) ==>
    ?b n. op_prov G off = SOME (b,n) /\
      b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
    (gvs[access_ok_def, source_memory_read_ranges_def,
         memory_range_of_operands_def, REVERSE_APPEND] >>
     strip_tac >> first_x_assum drule_all >> strip_tac >>
     gvs[op_prov_def] >> metis_tac[]) >>
  conj_tac
  >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
  `((lo < w2n yt + w2n amount \/ op_prov H off <> NONE) ==>
    ?b n. op_prov H off = SOME (b,n) /\
      b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`p` |-> `op_prov G off`, `x` |-> `xs`]
       dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
  rpt strip_tac >>
  `?b n. op_prov H off = SOME (b,n) /\
    b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
  Cases_on `off` >> gvs[op_prov_def] >> metis_tac[ADD_COMM]
QED

Theorem dload_copied_call_read_range[local]:
  ((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;value;off;sz;r;rs]) \/
   (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]) \/
   (i.inst_opcode = DELEGATECALL /\ i.inst_operands = [gas;addr;off;sz;r;rs])) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `op_prov G sz = NONE /\ op_taint tn sz = {}` by
    (Cases_on `i.inst_opcode = DELEGATECALL`
     >- (irule dload_delegate_scalar_safety >> gvs[] >> metis_tac[]) >>
     `op_prov G sz = NONE /\
       (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {})` by
       (irule dload_call_operand_safety >> gvs[] >> metis_tac[]) >>
     gvs[] >> metis_tac[MEM]) >>
  `op_taint tn off = {}` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> drule dload_matched_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand sz s = eval_operand sz t` by
    (irule scalar_operand_equal >> simp[] >> metis_tac[MEM]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  (gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  TRY (qpat_assum `i.inst_opcode = CALL`
    (fn _ => Cases_on `eval_operand value t` >> gvs[])) >>
  Cases_on `eval_operand gas t` >> gvs[] >>
  Cases_on `eval_operand addr t` >> gvs[] >>
  Cases_on `eval_operand r t` >> gvs[] >>
  Cases_on `eval_operand rs t` >> gvs[] >>
  Cases_on `eval_operand off t` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >>
  `eval_operand gas s <> NONE /\ eval_operand addr s <> NONE /\
   eval_operand r s <> NONE /\ eval_operand rs s <> NONE /\
   eval_operand off s <> NONE` by metis_tac[optionTheory.NOT_SOME_NONE] >>
  `i.inst_opcode = CALL ==> eval_operand value s <> NONE` by
    (strip_tac >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  TRY (qpat_assum `i.inst_opcode = CALL`
    (fn _ => Cases_on `eval_operand value s` >> gvs[])) >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr s` >> gvs[] >>
  Cases_on `eval_operand r s` >> gvs[] >>
  Cases_on `eval_operand rs s` >> gvs[] >>
  Cases_on `eval_operand off s` >> gvs[] >>
  rename1 `eval_operand off t = SOME yt` >>
  rename1 `eval_operand off s = SOME xs` >>
  rename1 `eval_operand sz t = SOME amount` >>
  `dload_value_word fs {} (op_prov G off) (op_prov H off) xs yt` by
    (drule dload_matched_operand >>
     disch_then (qspecl_then [`yt`,`xs`,`off`] mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `((lo < w2n xs + w2n amount \/ op_prov G off <> NONE) ==>
    ?b n. op_prov G off = SOME (b,n) /\
      b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
    (gvs[access_ok_def, source_memory_read_ranges_def,
         memory_range_of_operands_def, mem_read_ops_def] >>
     strip_tac >> first_x_assum drule_all >> strip_tac >>
     gvs[op_prov_def] >> metis_tac[]) >>
  (conj_tac
  >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
  `((lo < w2n yt + w2n amount \/ op_prov H off <> NONE) ==>
    ?b n. op_prov H off = SOME (b,n) /\
      b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`p` |-> `op_prov G off`, `x` |-> `xs`]
       dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
  simp[mem_read_ops_def] >> rpt strip_tac >>
  `?b n. op_prov H off = SOME (b,n) /\
    b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
  Cases_on `off` >> gvs[op_prov_def] >> metis_tac[ADD_COMM]))
QED

Theorem dload_copied_create_read_range[local]:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;salt])) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `op_prov G sz = NONE /\
   (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {}) /\
   tn.t_stor = {} /\ tn.t_trans = {}` by
    (irule dload_create_operand_safety >> simp[] >> metis_tac[]) >>
  `op_taint tn sz = {} /\ op_taint tn off = {}` by
    (gvs[] >> metis_tac[MEM]) >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> drule dload_matched_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand sz s = eval_operand sz t` by
    (irule scalar_operand_equal >> simp[] >> metis_tac[MEM]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  (gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
   Cases_on `eval_operand value t` >> gvs[] >>
   TRY (qpat_assum `i.inst_opcode = CREATE2`
     (fn _ => Cases_on `eval_operand salt t` >> gvs[])) >>
   Cases_on `eval_operand off t` >> gvs[] >>
   Cases_on `eval_operand sz t` >> gvs[] >>
   `eval_operand value s <> NONE /\ eval_operand off s <> NONE /\
    (i.inst_opcode = CREATE2 ==> eval_operand salt s <> NONE)` by
     (gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
   Cases_on `eval_operand value s` >> gvs[] >>
   TRY (qpat_assum `i.inst_opcode = CREATE2`
     (fn _ => Cases_on `eval_operand salt s` >> gvs[])) >>
   Cases_on `eval_operand off s` >> gvs[] >>
   rename1 `eval_operand off t = SOME yt` >>
   rename1 `eval_operand off s = SOME xs` >>
   rename1 `eval_operand sz t = SOME amount` >>
   `dload_value_word fs {} (op_prov G off) (op_prov H off) xs yt` by
     (drule dload_matched_operand >>
      disch_then (qspecl_then [`yt`,`xs`,`off`] mp_tac) >> simp[] >> metis_tac[MEM]) >>
   `((lo < w2n xs + w2n amount \/ op_prov G off <> NONE) ==>
     ?b n. op_prov G off = SOME (b,n) /\
       b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
     (gvs[access_ok_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, mem_read_ops_def] >>
      strip_tac >> first_x_assum drule_all >> strip_tac >>
      gvs[op_prov_def] >> metis_tac[]) >>
   conj_tac
   >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
   `((lo < w2n yt + w2n amount \/ op_prov H off <> NONE) ==>
     ?b n. op_prov H off = SOME (b,n) /\
       b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
     (match_mp_tac (Q.INST [`p` |-> `op_prov G off`, `x` |-> `xs`]
        dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
   simp[mem_read_ops_def] >> rpt strip_tac >>
   `?b n. op_prov H off = SOME (b,n) /\
     b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
   Cases_on `off` >> gvs[op_prov_def] >> metis_tac[ADD_COMM])
QED


Theorem dload_copied_read_range:
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  i.inst_opcode <> DRET /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_read_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_read_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_read_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_read_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `i.inst_opcode = MLOAD \/ i.inst_opcode = ILOAD`
  >- (irule dload_copied_fixed_read_range >> simp[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = RETURN \/ i.inst_opcode = REVERT \/ i.inst_opcode = SHA3`
  >- (`?off sz. i.inst_operands = [off;sz]` by
        (namedCases_on `i.inst_operands` ["", "off rest"] >>
         gvs[source_memory_read_ranges_def] >>
         namedCases_on `rest` ["", "sz tail"] >> gvs[] >>
         Cases_on `tail` >> gvs[]) >>
      drule_all dload_copied_pair_read_range >> simp[]) >>
  Cases_on `i.inst_opcode = MCOPY`
  >- (`?dst src sz. i.inst_operands = [dst;src;sz]` by
        (namedCases_on `i.inst_operands` ["", "dst rest"] >>
         gvs[source_memory_read_ranges_def] >>
         namedCases_on `rest` ["", "src tail"] >> gvs[] >>
         namedCases_on `tail` ["", "sz last"] >> gvs[] >>
         Cases_on `last` >> gvs[]) >>
      drule_all dload_copied_mcopy_read_range >> simp[]) >>
  Cases_on `i.inst_opcode = LOG`
  >- (`?tc rest. i.inst_operands = Lit tc::rest /\ LENGTH rest = w2n tc+2` by
        (namedCases_on `i.inst_operands` ["", "tc rest"] >>
         gvs[source_memory_read_ranges_def] >> Cases_on `tc` >> gvs[] >>
         Cases_on `LENGTH rest = w2n c + 2` >> gvs[]) >>
      drule log_tail_layout >> strip_tac >>
      `i.inst_operands = Lit tc::REVERSE (a::sz::ops)` by metis_tac[] >>
      drule_all dload_copied_log_read_range >> simp[]) >>
  Cases_on `i.inst_opcode = CALL`
  >- (`?gas addr value off sz r rs.
        i.inst_operands = [gas;addr;value;off;sz;r;rs]` by
        (namedCases_on `i.inst_operands` ["", "gas xs"] >> gvs[source_memory_read_ranges_def] >>
         namedCases_on `xs` ["", "addr ys"] >> gvs[] >>
         namedCases_on `ys` ["", "value zs"] >> gvs[] >>
         namedCases_on `zs` ["", "off ws"] >> gvs[] >>
         namedCases_on `ws` ["", "sz vs"] >> gvs[] >>
         namedCases_on `vs` ["", "r us"] >> gvs[] >>
         namedCases_on `us` ["", "rs tail"] >> gvs[] >>
         Cases_on `tail` >> gvs[]) >>
      Q.SUBGOAL_THEN
        `((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;value;off;sz;r;rs]) \/
          (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]) \/
          (i.inst_opcode = DELEGATECALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]))`
        assume_tac >- simp[] >>
      drule_all dload_copied_call_read_range >> simp[]) >>
  Cases_on `i.inst_opcode = STATICCALL \/ i.inst_opcode = DELEGATECALL`
  >- (`?gas addr off sz r rs. i.inst_operands = [gas;addr;off;sz;r;rs]` by
        (namedCases_on `i.inst_operands` ["", "gas xs"] >> gvs[source_memory_read_ranges_def] >>
         namedCases_on `xs` ["", "addr ys"] >> gvs[] >>
         namedCases_on `ys` ["", "off zs"] >> gvs[] >>
         namedCases_on `zs` ["", "sz ws"] >> gvs[] >>
         namedCases_on `ws` ["", "r us"] >> gvs[] >>
         namedCases_on `us` ["", "rs tail"] >> gvs[] >> Cases_on `tail` >> gvs[]) >>
      Q.SUBGOAL_THEN
        `((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;Lit 0w;off;sz;r;rs]) \/
          (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]) \/
          (i.inst_opcode = DELEGATECALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]))`
        assume_tac >- simp[] >>
      drule_all dload_copied_call_read_range >> simp[]) >>
  Cases_on `i.inst_opcode = CREATE`
  >- (`?value off sz. i.inst_operands = [value;off;sz]` by
        (namedCases_on `i.inst_operands` ["", "value xs"] >> gvs[source_memory_read_ranges_def] >>
         namedCases_on `xs` ["", "off ys"] >> gvs[] >>
         namedCases_on `ys` ["", "sz tail"] >> gvs[] >> Cases_on `tail` >> gvs[]) >>
      Q.SUBGOAL_THEN
        `((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
          (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;Lit 0w]))`
        assume_tac >- simp[] >>
      drule_all dload_copied_create_read_range >> simp[]) >>
  Cases_on `i.inst_opcode = CREATE2`
  >- (`?value off sz salt. i.inst_operands = [value;off;sz;salt]` by
        (namedCases_on `i.inst_operands` ["", "value xs"] >> gvs[source_memory_read_ranges_def] >>
         namedCases_on `xs` ["", "off ys"] >> gvs[] >>
         namedCases_on `ys` ["", "sz zs"] >> gvs[] >>
         namedCases_on `zs` ["", "salt tail"] >> gvs[] >> Cases_on `tail` >> gvs[]) >>
      Q.SUBGOAL_THEN
        `((i.inst_opcode = CREATE /\ i.inst_operands = [value;off;sz]) \/
          (i.inst_opcode = CREATE2 /\ i.inst_operands = [value;off;sz;salt]))`
        assume_tac >- simp[] >>
      drule_all dload_copied_create_read_range >> simp[]) >>
  Cases_on `i.inst_opcode` >> gvs[source_memory_read_ranges_def]
QED

Theorem dload_copied_fixed_write_range[local]:
  (i.inst_opcode = MSTORE \/ i.inst_opcode = MSTORE8 \/ i.inst_opcode = ISTORE) /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_write_ranges i t) ==>
  ?a. MEM (a,len) (source_memory_write_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_write_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b sz. mem_write_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,sz) /\ b<=z /\ z+len<=b+sz)
Proof
  strip_tac >>
  (namedCases_on `i.inst_operands` ["", "off rest"] >>
   gvs[source_memory_write_ranges_def] >>
   namedCases_on `rest` ["", "value tail"] >> gvs[] >>
   Cases_on `tail` >> gvs[] >>
   Cases_on `eval_operand off t` >>
   gvs[fixed_source_write_range_def] >>
   Cases_on `eval_operand value t` >> gvs[] >>
   rename1 `eval_operand off t = SOME yt` >>
   `eval_operand off s <> NONE /\ eval_operand value s <> NONE` by
     (conj_tac
      >- (drule dload_matched_operand_defined >>
          disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[]) >>
      drule dload_matched_operand_defined >>
      disch_then (qspec_then `value` mp_tac) >> simp[] >> metis_tac[]) >>
   Cases_on `eval_operand off s` >> Cases_on `eval_operand value s` >> gvs[] >>
   rename1 `eval_operand off s = SOME xs` >>
   `op_taint tn off = {}` by (gvs[taint_ok_def] >> metis_tac[]) >>
   `dload_value_word fs {} (op_prov G off) (op_prov H off) xs yt` by
     (drule dload_matched_operand >>
      disch_then (qspecl_then [`yt`,`xs`,`off`] mp_tac) >> simp[] >> metis_tac[]) >>
   `((lo < w2n xs + (if i.inst_opcode = MSTORE8 then 1 else 32) \/ op_prov G off <> NONE) ==>
      ?b n. op_prov G off = SOME (b,n) /\ b<=w2n xs /\ w2n xs+(if i.inst_opcode = MSTORE8 then 1 else 32)<=b+n)` by
     (gvs[access_ok_def, source_memory_write_ranges_def,
          fixed_source_write_range_def, mem_write_ops_def] >>
      strip_tac >> first_x_assum drule_all >> strip_tac >>
      gvs[op_prov_def] >> metis_tac[]) >>
   conj_tac
   >- (drule_all dload_value_contained_region >> simp[] >> metis_tac[w2n_11]) >>
   `((lo < w2n yt + (if i.inst_opcode = MSTORE8 then 1 else 32) \/ op_prov H off <> NONE) ==>
      ?b n. op_prov H off = SOME (b,n) /\ b<=w2n yt /\ w2n yt+(if i.inst_opcode = MSTORE8 then 1 else 32)<=b+n)` by
     (match_mp_tac (Q.INST [`p` |-> `op_prov G off`, `x` |-> `xs`]
        dload_value_access_containment) >> gvs[] >> metis_tac[]) >>
   simp[mem_write_ops_def] >> rpt strip_tac >>
   `?b n. op_prov H off = SOME (b,n) /\ b<=w2n yt /\ w2n yt+(if i.inst_opcode = MSTORE8 then 1 else 32)<=b+n` by (gvs[] >> metis_tac[]) >>
   Cases_on `off` >> gvs[op_prov_def] >> metis_tac[])
QED

Theorem dload_copied_mcopy_write_range[local]:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_write_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_write_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_write_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_write_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_prov G sz = NONE /\ op_taint tn dst = {} /\ op_taint tn sz = {}` by
    metis_tac[dload_mcopy_size_clean] >>
  `!v. sz = Var v ==> v IN V` by metis_tac[MEM] >>
  `eval_operand sz s = NONE <=> eval_operand sz t = NONE` by
    metis_tac[dload_matched_operand_defined] >>
  `eval_operand sz s = eval_operand sz t` by metis_tac[scalar_operand_equal] >>
  `eval_operand dst s = NONE <=> eval_operand dst t = NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `eval_operand src s = NONE <=> eval_operand src t = NONE` by
    (drule dload_matched_operand_defined >>
     disch_then (qspec_then `src` mp_tac) >> simp[] >> metis_tac[MEM]) >>
  gvs[source_memory_write_ranges_def, sized_source_write_range_def] >>
  Cases_on `eval_operand dst t` >> gvs[] >>
  Cases_on `eval_operand src t` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >>
  Cases_on `eval_operand dst s` >> gvs[] >>
  Cases_on `eval_operand src s` >> gvs[] >>
  rename1 `eval_operand src s = SOME sx` >>
  rename1 `eval_operand dst t = SOME yt` >>
  rename1 `eval_operand dst s = SOME xs` >>
  rename1 `eval_operand sz t = SOME amount` >>
  `dload_value_word fs {} (op_prov G dst) (op_prov H dst) xs yt` by
    (drule dload_matched_operand >>
     disch_then (qspecl_then [`yt`,`xs`,`dst`] mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `((lo < w2n xs + w2n amount \/ op_prov G dst <> NONE) ==>
    ?b n. op_prov G dst = SOME (b,n) /\
      b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`dx` |-> `xs`, `sx` |-> `sx`]
       dload_mcopy_contained) >> simp[]) >>
  conj_tac
  >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
  `((lo < w2n yt + w2n amount \/ op_prov H dst <> NONE) ==>
    ?b n. op_prov H dst = SOME (b,n) /\
      b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`p` |-> `op_prov G dst`, `x` |-> `xs`]
       dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
  simp[mem_write_ops_def] >> rpt strip_tac >>
  `?b n. op_prov H dst = SOME (b,n) /\
    b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
  Cases_on `dst` >> gvs[op_prov_def] >> metis_tac[ADD_COMM]
QED

Theorem dload_copied_external_write_range[local]:
  MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY;DLOADBYTES] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz] else [dst;off;sz]) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_write_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_write_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_write_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_write_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_prov G sz = NONE /\ op_taint tn dst = {} /\ op_taint tn sz = {}` by
    (Cases_on `i.inst_opcode = DLOADBYTES`
     >- (`op_prov G sz = NONE /\ op_taint tn sz = {}` by
           (gvs[] >> drule_all dloadbytes_scalar_clean >> simp[] >> metis_tac[]) >>
         gvs[taint_ok_def] >> metis_tac[]) >>
     `MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY]` by gvs[] >>
     drule_all external_copy_scalar_clean >> simp[] >> metis_tac[]) >>
  `!v. sz = Var v ==> v IN V` by
    (Cases_on `i.inst_opcode = EXTCODECOPY` >> gvs[] >> metis_tac[MEM]) >>
  `eval_operand sz s = NONE <=> eval_operand sz t = NONE` by
    metis_tac[dload_matched_operand_defined] >>
  `eval_operand sz s = eval_operand sz t` by metis_tac[scalar_operand_equal] >>
  `!op. MEM op i.inst_operands ==> (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> drule dload_matched_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `MEM i.inst_opcode _` strip_assume_tac >>
  (gvs[source_memory_write_ranges_def, sized_source_write_range_def] >>
   Cases_on `eval_operand addr t` >> gvs[] >>
   Cases_on `eval_operand dst t` >> gvs[] >>
   Cases_on `eval_operand off t` >> gvs[] >>
   Cases_on `eval_operand sz t` >> gvs[] >>
   `eval_operand dst s <> NONE /\ eval_operand off s <> NONE` by
     (conj_tac
      >- (qpat_x_assum `!op. _` (qspec_then `dst` mp_tac) >> simp[]) >>
      qpat_x_assum `!op. _` (qspec_then `off` mp_tac) >> simp[]) >>
   Cases_on `eval_operand dst s` >> Cases_on `eval_operand off s` >> gvs[] >>
   `i.inst_opcode = EXTCODECOPY ==> eval_operand addr s <> NONE` by
     (simp[] >> qpat_x_assum `!op. _` (qspec_then `addr` mp_tac) >> simp[]) >>
   Cases_on `eval_operand addr s` >> gvs[] >>
   (rename1 `eval_operand dst t = SOME yt` >>
   rename1 `eval_operand dst s = SOME xs` >>
   rename1 `eval_operand sz t = SOME amount` >>
   `dload_value_word fs {} (op_prov G dst) (op_prov H dst) xs yt` by
     (drule dload_matched_operand >>
      disch_then (qspecl_then [`yt`,`xs`,`dst`] mp_tac) >> simp[] >> metis_tac[MEM]) >>
   `((lo < w2n xs + w2n amount \/ op_prov G dst <> NONE) ==>
     ?b n. op_prov G dst = SOME (b,n) /\ b<=w2n xs /\ w2n xs+w2n amount<=b+n)` by
     (gvs[access_ok_def, source_memory_write_ranges_def,
          sized_source_write_range_def, mem_write_ops_def] >>
      Cases_on `eval_operand addr s` >> gvs[] >>
      strip_tac >> first_x_assum drule_all >> strip_tac >>
      gvs[op_prov_def] >> metis_tac[]) >>
   (conj_tac
   >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
   `((lo < w2n yt + w2n amount \/ op_prov H dst <> NONE) ==>
     ?b n. op_prov H dst = SOME (b,n) /\ b<=w2n yt /\ w2n yt+w2n amount<=b+n)` by
     (match_mp_tac (Q.INST [`p` |-> `op_prov G dst`, `x` |-> `xs`]
        dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
   simp[mem_write_ops_def] >> rpt strip_tac >>
   `?b n. op_prov H dst = SOME (b,n) /\ b<=w2n yt /\ w2n yt+w2n amount<=b+n` by metis_tac[ADD_COMM] >>
   Cases_on `dst` >> gvs[op_prov_def] >> metis_tac[ADD_COMM])))
QED

Theorem dload_copied_call_write_range[local]:
  ((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;value;off;sz;r;rs]) \/
   (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]) \/
   (i.inst_opcode = DELEGATECALL /\ i.inst_operands = [gas;addr;off;sz;r;rs])) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_write_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_write_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_write_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_write_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  `op_prov G rs = NONE /\ op_taint tn rs = {}` by
    (Cases_on `i.inst_opcode = DELEGATECALL`
     >- (irule dload_delegate_scalar_safety >> gvs[] >> metis_tac[]) >>
     `op_prov G rs = NONE /\
       (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {})` by
       (irule dload_call_operand_safety >> gvs[] >> metis_tac[]) >>
     gvs[] >> metis_tac[MEM]) >>
  `op_taint tn r = {}` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> drule dload_matched_operand_defined >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand rs s = eval_operand rs t` by
    (irule scalar_operand_equal >> simp[] >> metis_tac[MEM]) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  (gvs[source_memory_write_ranges_def] >>
  TRY (qpat_assum `i.inst_opcode = CALL`
    (fn _ => Cases_on `eval_operand value t` >> gvs[])) >>
  Cases_on `eval_operand gas t` >> gvs[] >>
  Cases_on `eval_operand addr t` >> gvs[] >>
  Cases_on `eval_operand r t` >> gvs[] >>
  Cases_on `eval_operand rs t` >> gvs[] >>
  Cases_on `eval_operand off t` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >>
  `eval_operand gas s <> NONE /\ eval_operand addr s <> NONE /\
   eval_operand r s <> NONE /\ eval_operand sz s <> NONE /\
   eval_operand off s <> NONE` by metis_tac[optionTheory.NOT_SOME_NONE] >>
  `i.inst_opcode = CALL ==> eval_operand value s <> NONE` by
    (strip_tac >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  TRY (qpat_assum `i.inst_opcode = CALL`
    (fn _ => Cases_on `eval_operand value s` >> gvs[])) >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr s` >> gvs[] >>
  Cases_on `eval_operand r s` >> gvs[] >>
  Cases_on `eval_operand sz s` >> gvs[] >>
  Cases_on `eval_operand off s` >> gvs[] >>
  rename1 `eval_operand r t = SOME yt` >>
  rename1 `eval_operand r s = SOME xs` >>
  rename1 `eval_operand rs t = SOME amount` >>
  `dload_value_word fs {} (op_prov G r) (op_prov H r) xs yt` by
    (drule dload_matched_operand >>
     disch_then (qspecl_then [`yt`,`xs`,`r`] mp_tac) >> simp[] >> metis_tac[MEM]) >>
  `((lo < w2n xs + w2n amount \/ op_prov G r <> NONE) ==>
    ?b n. op_prov G r = SOME (b,n) /\
      b <= w2n xs /\ w2n xs + w2n amount <= b+n)` by
    (gvs[access_ok_def, source_memory_write_ranges_def, mem_write_ops_def] >>
     strip_tac >> first_x_assum drule_all >> strip_tac >>
     gvs[op_prov_def] >> metis_tac[]) >>
  (conj_tac
  >- (drule_all dload_value_contained_region >> metis_tac[w2n_11, ADD_COMM]) >>
  `((lo < w2n yt + w2n amount \/ op_prov H r <> NONE) ==>
    ?b n. op_prov H r = SOME (b,n) /\
      b <= w2n yt /\ w2n yt + w2n amount <= b+n)` by
    (match_mp_tac (Q.INST [`p` |-> `op_prov G r`, `x` |-> `xs`]
       dload_value_access_containment) >> simp[] >> metis_tac[ADD_COMM]) >>
  simp[mem_write_ops_def] >> rpt strip_tac >>
  `?b n. op_prov H r = SOME (b,n) /\
    b <= w2n yt /\ w2n yt + w2n amount <= b+n` by metis_tac[ADD_COMM] >>
  Cases_on `r` >> gvs[op_prov_def] >> metis_tac[ADD_COMM]))
QED

Theorem dload_copied_write_range:
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  i.inst_opcode <> DRET /\
  dload_vars_match fs V G H tn un s t /\ s.vs_labels = t.vs_labels /\
  dload_live_layout lo sf tf fs /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  access_ok lo G f i s /\ taint_ok f tn i s /\ ~in_revert_forward f s /\
  MEM (z,len) (source_memory_write_ranges i t) /\ len <> 0 ==>
  ?a. MEM (a,len) (source_memory_write_ranges i s) /\
    ((a = z /\ a+len <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       a=b+d /\ z=c+d /\ d+len<=n)) /\
    ((lo < z+len \/ ?ops. mem_write_ops i = SOME ops /\
       op_prov H ops.iao_ofst <> NONE) ==>
     ?ops v b n. mem_write_ops i = SOME ops /\ ops.iao_ofst = Var v /\
       FLOOKUP H v = SOME (b,n) /\ b<=z /\ z+len<=b+n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `i.inst_opcode = MSTORE \/ i.inst_opcode = MSTORE8 \/ i.inst_opcode = ISTORE`
  >- (irule dload_copied_fixed_write_range >> simp[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = MCOPY`
  >- (`?dst src sz. i.inst_operands = [dst;src;sz]` by
        (namedCases_on `i.inst_operands` ["", "dst rest"] >>
         gvs[source_memory_write_ranges_def] >>
         namedCases_on `rest` ["", "src tail"] >> gvs[] >>
         namedCases_on `tail` ["", "sz last"] >> gvs[] >>
         Cases_on `last` >> gvs[]) >>
      drule_all dload_copied_mcopy_write_range >> simp[]) >>
  Cases_on `MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;DLOADBYTES]`
  >- (`?dst off sz. i.inst_operands = [dst;off;sz]` by
        (qpat_x_assum `MEM i.inst_opcode _` strip_assume_tac >>
         namedCases_on `i.inst_operands` ["", "dst rest"] >>
         gvs[source_memory_write_ranges_def] >>
         namedCases_on `rest` ["", "off tail"] >> gvs[] >>
         namedCases_on `tail` ["", "sz last"] >> gvs[] >>
         Cases_on `last` >> gvs[]) >>
      `MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY;DLOADBYTES]` by gvs[] >>
      `i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [Lit 0w;dst;off;sz] else [dst;off;sz])` by gvs[] >>
      drule_all dload_copied_external_write_range >> simp[]) >>
  Cases_on `i.inst_opcode = EXTCODECOPY`
  >- (`?addr dst off sz. i.inst_operands = [addr;dst;off;sz]` by
        (namedCases_on `i.inst_operands` ["", "addr rest"] >>
         gvs[source_memory_write_ranges_def] >>
         namedCases_on `rest` ["", "dst tail"] >> gvs[] >>
         namedCases_on `tail` ["", "off last"] >> gvs[] >>
         namedCases_on `last` ["", "sz fin"] >> gvs[] >>
         Cases_on `fin` >> gvs[]) >>
      `MEM i.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY;DLOADBYTES]` by simp[] >>
      `i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz] else [dst;off;sz])` by simp[] >>
      drule_all dload_copied_external_write_range >> simp[]) >>
  Cases_on `i.inst_opcode = CALL`
  >- (`?gas addr value off sz r rs.
        i.inst_operands = [gas;addr;value;off;sz;r;rs]` by
        (namedCases_on `i.inst_operands` ["", "gas xs"] >> gvs[source_memory_write_ranges_def] >>
         namedCases_on `xs` ["", "addr ys"] >> gvs[] >>
         namedCases_on `ys` ["", "value zs"] >> gvs[] >>
         namedCases_on `zs` ["", "off ws"] >> gvs[] >>
         namedCases_on `ws` ["", "sz vs"] >> gvs[] >>
         namedCases_on `vs` ["", "r us"] >> gvs[] >>
         namedCases_on `us` ["", "rs tail"] >> gvs[] >>
         Cases_on `tail` >> gvs[]) >>
      Q.SUBGOAL_THEN
        `((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;value;off;sz;r;rs]) \/
          (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]) \/
          (i.inst_opcode = DELEGATECALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]))`
        assume_tac >- simp[] >>
      drule_all dload_copied_call_write_range >> simp[]) >>
  Cases_on `i.inst_opcode = STATICCALL \/ i.inst_opcode = DELEGATECALL`
  >- (`?gas addr off sz r rs. i.inst_operands = [gas;addr;off;sz;r;rs]` by
        (namedCases_on `i.inst_operands` ["", "gas xs"] >> gvs[source_memory_write_ranges_def] >>
         namedCases_on `xs` ["", "addr ys"] >> gvs[] >>
         namedCases_on `ys` ["", "off zs"] >> gvs[] >>
         namedCases_on `zs` ["", "sz ws"] >> gvs[] >>
         namedCases_on `ws` ["", "r us"] >> gvs[] >>
         namedCases_on `us` ["", "rs tail"] >> gvs[] >> Cases_on `tail` >> gvs[]) >>
      Q.SUBGOAL_THEN
        `((i.inst_opcode = CALL /\ i.inst_operands = [gas;addr;Lit 0w;off;sz;r;rs]) \/
          (i.inst_opcode = STATICCALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]) \/
          (i.inst_opcode = DELEGATECALL /\ i.inst_operands = [gas;addr;off;sz;r;rs]))`
        assume_tac >- simp[] >>
      drule_all dload_copied_call_write_range >> simp[]) >>
  Cases_on `i.inst_opcode` >> gvs[source_memory_write_ranges_def]
QED

Theorem dload_copied_forward_guard:
  o1_ctx_shape C /\ MEM f C.ctx_functions /\
  dload_control_match q f g s t i [i] 0 /\ ir_supply_covers_fn q f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  in_revert_forward f s /\
  (source_memory_read_ranges i s <> [] \/ source_memory_write_ranges i s <> [] \/
   source_memory_read_ranges i t <> [] \/ source_memory_write_ranges i t <> []) ==>
  in_revert_forward g t
Proof
  strip_tac >>
  drule_all dload_control_cover_block >> strip_tac >>
  `?j. revert_forward_pair bb s.vs_inst_idx j \/
       revert_forward_pair bb j s.vs_inst_idx` by
    (gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  (drule_all lower_dload_block_supply_forward_pair >> strip_tac >>
   gvs[] >> simp[in_revert_forward_def, revert_forward_at_def] >> metis_tac[])
QED

Theorem dload_copied_about_to_revert:
  o1_ctx_shape C /\ MEM f C.ctx_functions /\
  dload_control_match q f g s t i [i] 0 /\ ir_supply_covers_fn q f /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  about_to_revert f i s ==> about_to_revert g i t
Proof
  strip_tac >>
  Cases_on `i.inst_opcode = REVERT` >- simp[about_to_revert_def] >>
  `i.inst_opcode = RETURNDATACOPY /\
   ?ri. active_inst f ri (s with vs_inst_idx := SUC s.vs_inst_idx) /\ ri.inst_opcode = REVERT` by
    (gvs[about_to_revert_def] >> metis_tac[]) >>
  drule_all dload_control_cover_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (fs[dload_control_match_def, active_inst_def] >>
     `lookup_block s.vs_current_bb f.fn_blocks = SOME bb'` by
       (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
     gvs[] >> simp[get_instruction_def]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME ri` by
    (qpat_x_assum `active_inst f ri _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb f.fn_blocks = SOME bb'` by
       (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
     gvs[] >> simp[get_instruction_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   SUC s.vs_inst_idx < LENGTH bb.bb_instructions /\
   i = EL s.vs_inst_idx bb.bb_instructions /\
   ri = EL (SUC s.vs_inst_idx) bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `lower_dload_inst_supply u i = ([i],u)` by
    (irule o1ContractLowerDloadTheory.lower_dload_inst_supply_special >> simp[]) >>
  `lower_dload_insts_supply bs (TAKE (SUC s.vs_inst_idx) bb.bb_instructions) = (pre ++ [i],u)` by
    (irule dload_insts_supply_prefix_emission >> simp[] >> metis_tac[]) >>
  `?ys. lower_dload_insts_supply bs bb.bb_instructions = (tb.bb_instructions,ys)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  `?ps v rest. lower_dload_insts_supply bs (TAKE (SUC s.vs_inst_idx) bb.bb_instructions) = (ps,v) /\
    lower_dload_insts_supply v (DROP (SUC (SUC s.vs_inst_idx)) bb.bb_instructions) = (rest,ys) /\
    tb.bb_instructions = ps ++ ri::rest` by
    (irule lower_dload_insts_supply_at_unchanged >> simp[] >> metis_tac[]) >>
  gvs[] >> simp[about_to_revert_def] >>
  qexists `EL (SUC s.vs_inst_idx) bb.bb_instructions` >> simp[] >>
  simp[active_inst_def] >> qexists `tb` >>
  `MEM tb g.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `tb.bb_label = t.vs_current_bb` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  simp[EL_APPEND, EL_CONS, arithmeticTheory.ADD1]
QED

Theorem dload_normal_copied_safety:
  o1_ctx_shape C /\ EVERY fn_shape_ok C'.ctx_functions /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g i t /\
  dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G H tn un s t cs ds /\
  dload_control_match q f g s t i [i] 0 /\ ir_supply_covers_fn q f /\
  (?q'. lower_dload_function_supply q f = (g,q')) /\
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES ==>
  access_ok lo H g i t /\ taint_ok g un i t
Proof
  strip_tac >>
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> metis_tac[]) >>
  `MEM f C.ctx_functions /\ FDOM G SUBSET fn_pv P f` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_tac o MATCH_MP frame_reachable_prov_supported) >>
     disch_then (qspec_then `P` mp_tac) >>
     impl_tac >- metis_tac[EVERY_MEM] >> simp[]) >>
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  drule dload_boundary_vars >> strip_tac >>
  drule dload_boundary_layout >> strip_tac >>
  drule dload_boundary_environment >> strip_tac >>
  `s.vs_labels = t.vs_labels` by
    (qpat_x_assum `dload_equal_environment s t` mp_tac >>
     rewrite_tac[dload_equal_environment_def] >>
     disch_then (mp_tac o AP_TERM ``\x:venom_state. x.vs_labels``) >> simp[]) >>
  conj_tac >- suspend "access" >> suspend "taint"
QED

Resume dload_normal_copied_safety[access]:
  `i.inst_opcode <> DRET` by
    (fs[o1_fn_shape_def, dretDesugarDefsTheory.no_dret_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]`
  >- (gvs[MEM] >> simp[access_ok_def, source_memory_read_ranges_def,
        source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def]) >>
  `!v. MEM (Var v) i.inst_operands ==>
     v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (`opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
     rpt strip_tac >> drule_all dload_original_nonopaque_operands >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     fs[fn_labels_def]) >>
  `!v. v IN FDOM H ==> lookup_var v t <> NONE` by
    (qpat_assum `frame_reachable vs C' ds PH H un g i t`
       (mp_tac o MATCH_MP dload_frame_prov_defined) >> simp[]) >>
  simp[access_ok_def] >> conj_tac
  >- (strip_tac >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> `~in_revert_forward f s` by
            metis_tac[dload_copied_forward_guard, MEM] >>
          drule_all dload_copied_write_range >> strip_tac >>
          fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >> `~in_revert_forward f s` by
        metis_tac[dload_copied_forward_guard, MEM] >>
      drule_all dload_copied_read_range >> strip_tac >>
      fs[arithmeticTheory.ADD_COMM]) >>
  rpt gen_tac >> strip_tac >> irule dload_copied_compare_access >>
  simp[] >> metis_tac[]
QED

Resume dload_normal_copied_safety[taint]:
  `EVERY fn_shape_ok C.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `!v. retpc_var f v ==> op_taint tn (Var v) = {}` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_tac o MATCH_MP dload_frame_retpc_clean) >> simp[]) >>
  `!v. retpc_var g v ==> op_taint un (Var v) = {}` by
    (qpat_assum `frame_reachable vs C' ds PH H un g i t`
       (mp_tac o MATCH_MP dload_frame_retpc_clean) >> simp[]) >>
  `retpc_var g = retpc_var f` by
    metis_tac[o1ContractLowerDloadTheory.lower_dload_function_supply_retpc_var] >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = op_taint un op` by
    (rpt strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
     rename1 `MEM (Var v) i.inst_operands` >>
     Cases_on `retpc_var f v`
     >- (fs[op_taint_def] >> metis_tac[]) >>
     `v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
       (simp[] >> metis_tac[lowerDloadPtrStaticTheory.fn_ir_vars_operand]) >>
     fs[dload_vars_match_def] >> metis_tac[]) >>
  `!b. i.inst_opcode = MUL /\ MEM b i.inst_operands /\
       op_taint tn b = {} ==> eval_operand b s = eval_operand b t` by
    (rpt strip_tac >>
     `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
     `!v. MEM (Var v) i.inst_operands ==>
        v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
       (rpt strip_tac >> irule dload_original_nonopaque_operands >>
        simp[] >> qexists `i` >> simp[MEM]) >>
     `op_prov G b = NONE` by
       (irule lowerDloadPtrScalarTheory.scalar_operand_no_prov >>
        simp[MEM] >> metis_tac[]) >>
     `eval_operand b s = NONE <=> eval_operand b t = NONE` by
       (irule dload_matched_operand_defined >> metis_tac[]) >>
     `!v. b = Var v ==>
        v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by metis_tac[] >>
     drule_all scalar_operand_equal >> simp[]) >>
  simp[taint_ok_def] >> conj_tac
  >- (rpt strip_tac >>
      `op_taint tn op <> {}` by metis_tac[] >>
      qpat_x_assum `taint_ok f tn i s` mp_tac >>
      simp[taint_ok_def] >> strip_tac >>
      first_x_assum (qspec_then `op` mp_tac) >> simp[] >>
      strip_tac >> gvs[] >> fs[MEM] >> metis_tac[]) >>
  reverse conj_tac
  >- (drule dload_boundary_shared_store >>
      simp[dload_shared_store_def] >> rpt strip_tac >> fs[taint_ok_def] >> metis_tac[]) >>
  suspend "memory"
QED

Resume dload_normal_copied_safety[memory]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     fs[fn_labels_def]) >>
  `~about_to_revert f i s` by metis_tac[dload_copied_about_to_revert] >>
  `~in_revert_forward f s` by
    (strip_tac >>
     `i.inst_opcode = RETURNDATACOPY \/ i.inst_opcode = REVERT` by
       (qpat_x_assum `in_revert_forward f s` mp_tac >>
        qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
        simp[dload_control_match_def, active_inst_def, in_revert_forward_def,
             revert_forward_at_def] >> rpt strip_tac >>
        `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
          (irule venomExecProofsTheory.MEM_lookup_block >> simp[]) >>
        gvs[revert_forward_pair_def, get_instruction_def]) >>
     gvs[about_to_revert_def, source_memory_read_ranges_def]) >>
  `i.inst_opcode <> DRET` by
    (fs[o1_fn_shape_def, dretDesugarDefsTheory.no_dret_def, EVERY_MEM] >> metis_tac[]) >>
  `~MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (strip_tac >> gvs[MEM, source_memory_read_ranges_def]) >>
  `!v. MEM (Var v) i.inst_operands ==>
     v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (`opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
     rpt strip_tac >> drule_all dload_original_nonopaque_operands >> simp[]) >>
  `len <> 0` by decide_tac >>
  drule_all dload_copied_read_range >> strip_tac >>
  drule dload_boundary_memory >> strip_tac >>
  `?j. a <= j /\ j < a+len /\ j IN tn.t_mem` by
    (Cases_on `a = off /\ a+len <= lo`
     >- (`i' < lo` by decide_tac >>
         `i' IN tn.t_mem` by metis_tac[dload_memory_match_def] >>
         qexists `i'` >> simp[] >> decide_tac) >>
     `?owner id b c n d. dload_live_site fs owner id b c n /\
        a=b+d /\ off=c+d /\ d+len<=n` by metis_tac[] >>
     `d + (i'-off) < n` by decide_tac >>
     `i' = c + (d + (i'-off))` by decide_tac >>
     `b + (d + (i'-off)) IN tn.t_mem` by
       metis_tac[dload_memory_match_def] >>
     qexists `b + (d + (i'-off))` >> simp[] >> decide_tac) >>
  fs[taint_ok_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise dload_normal_copied_safety

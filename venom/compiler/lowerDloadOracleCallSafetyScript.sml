(* Current-instruction range safety does not require successful execution. *)
Theory lowerDloadOracleCallSafety
Ancestors
  lowerDloadOracleCallAssembly lowerDloadSafetyAllocBounds
  lowerDloadSafetyAmbient lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  unitMemInv unitTransformDefs memLocDefs ptrDiscipline
  codegenRel contextCodegenRel venomExecSemantics venomInst
  finite_map pred_set list words arithmetic pair venomWf
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyWriteAssembly

Theorem ld_alloc_target_frontier:
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\ FLOOKUP A k = SOME (b,c,n) ==>
  c+n <= (HD frames).lf_tgt.vs_alloca_next
Proof
  strip_tac >> drule_all ld_slot_source_site >> strip_tac >>
  `ld_maps A (EL j frames)` by gvs[EVERY_EL] >>
  `FLOOKUP (EL j frames).lf_src.vs_allocas aid = SOME (b,n)` by
    gvs[ld_sites_def] >>
  `FLOOKUP (EL j frames).lf_tgt.vs_allocas aid = SOME (c,n)` by
    (gvs[ld_maps_def] >>
     qpat_x_assum `!aid b n. FLOOKUP _ aid = SOME (b,n) ==> ?c. _ /\ _`
       drule >> strip_tac >> gvs[]) >>
  `(j,aid,c,n) IN ld_sites frames F` by
    (simp[ld_sites_def] >> metis_tac[]) >>
  drule_all ld_global_bounds >> simp[]
QED

Theorem ld_oracle_call_range_transport:
  MEM (getops,ranges)
    [(mem_read_ops,source_memory_read_ranges);
     (mem_write_ops,source_memory_write_ranges)] /\
  MEM inst.inst_opcode [CALL;STATICCALL] /\
  (!op y. MEM op inst.inst_operands /\ eval_operand op t = SOME y ==>
     ?x. eval_operand op s = SOME x) /\
  (!i. MEM i (if inst.inst_opcode = CALL then [0;1;2;4;6]
             else [0;1;3;5]) ==>
     eval_operand (EL i inst.inst_operands) s =
     eval_operand (EL i inst.inst_operands) t) /\
  MEM (a,n) (ranges inst t) ==>
  ?ops x y. getops inst = SOME ops /\
    eval_operand ops.iao_ofst s = SOME x /\
    eval_operand ops.iao_ofst t = SOME y /\ a = w2n y /\
    MEM (w2n x,n) (ranges inst s)
Proof
  strip_tac >> gvs[] >>
  Cases_on `inst.inst_operands` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  rename1 `inst.inst_operands = g::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  rename1 `inst.inst_operands = g::ad::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  rename1 `inst.inst_operands = g::ad::v::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  rename1 `inst.inst_operands = g::ad::v::ao::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  rename1 `inst.inst_operands = g::ad::v::ao::az::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  rename1 `inst.inst_operands = g::ad::v::ao::az::ro::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  TRY (rename1 `inst.inst_operands = [g;ad;v;ao;az;ro]` >>
       suspend "static" >> NO_TAC) >>
  rename1 `inst.inst_operands = g::ad::v::ao::az::ro::rz::xs` >>
  Cases_on `xs` >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  suspend "call"
QED

Resume ld_oracle_call_range_transport[static]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  Cases_on `eval_operand g t` >> gvs[] >>
  Cases_on `eval_operand ad t` >> gvs[] >>
  Cases_on `eval_operand v t` >> gvs[memory_range_of_operands_def] >>
  Cases_on `eval_operand ao t` >> gvs[] >>
  Cases_on `eval_operand az t` >> gvs[] >>
  Cases_on `eval_operand ro t` >> gvs[] >>
  qpat_x_assum `!i. _` (fn th => map_every
    (fn i => mp_tac (Q.SPEC i th)) [`0`,`1`,`3`,`5`]) >>
  simp[EL] >> rpt strip_tac >>
  `?xv. eval_operand v s = SOME xv` by metis_tac[] >>
  `?xa. eval_operand az s = SOME xa` by metis_tac[] >>
  simp[mem_read_ops_def, mem_write_ops_def]
QED

Resume ld_oracle_call_range_transport[call]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  Cases_on `eval_operand g t` >> gvs[] >>
  Cases_on `eval_operand ad t` >> gvs[] >>
  Cases_on `eval_operand v t` >> gvs[] >>
  Cases_on `eval_operand ao t` >> gvs[memory_range_of_operands_def] >>
  Cases_on `eval_operand az t` >> gvs[] >>
  Cases_on `eval_operand ro t` >> gvs[] >>
  Cases_on `eval_operand rz t` >> gvs[] >>
  qpat_x_assum `!i. _` (fn th => map_every
    (fn i => mp_tac (Q.SPEC i th)) [`0`,`1`,`2`,`4`,`6`]) >>
  simp[EL] >> rpt strip_tac >>
  `?xa. eval_operand ao s = SOME xa` by metis_tac[] >>
  `?xr. eval_operand ro s = SOME xr` by metis_tac[] >>
  simp[mem_read_ops_def, mem_write_ops_def]
QED

Finalise ld_oracle_call_range_transport

Theorem ld_sync_oracle_call_raw:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL] ==>
  raw_mem_ok C fn inst t
Proof
  strip_tac >>
  `fn_shape_ok fn /\ fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ld_sync_access_ok, ld_sync_taint_ok] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `lo <= t.vs_alloca_next` by metis_tac[ld_sync_frontier_lower_bound] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= t.vs_alloca_next` by
    (rpt strip_tac >> drule_all ld_alloc_target_frontier >>
     drule ld_sync_active >> simp[]) >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    metis_tac[LESS_EQ_LESS_TRANS] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  `inst_wf inst` by
    (fs[venomWfTheory.fn_inst_wf_def, fn_insts_def,
        o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  `?g ad v ao az ro rz.
    (inst.inst_opcode = CALL /\ inst.inst_operands = [g;ad;v;ao;az;ro;rz]) \/
    (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [g;ad;ao;az;ro;rz])` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     pure_rewrite_tac[venomWfTheory.inst_wf_def] >>
     fs[MEM] >> gvs[] >> simp[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `!i. MEM i (if inst.inst_opcode = CALL then [0;1;2;4;6] else [0;1;3;5]) ==>
      eval_operand (EL i inst.inst_operands) s =
      eval_operand (EL i inst.inst_operands) t` by
    (rpt strip_tac >>
     `eval_operand (EL i inst.inst_operands) f.lf_src =
      eval_operand (EL i inst.inst_operands) f.lf_tgt` suffices_by metis_tac[] >>
     irule ld_oracle_call_scalar_equal >> gvs[] >> metis_tac[]) >>
  `!op y. MEM op inst.inst_operands /\ eval_operand op t = SOME y ==>
      ?x. eval_operand op s = SOME x` by
    (rpt strip_tac >>
     `?x. eval_operand op f.lf_src = SOME x` suffices_by metis_tac[] >>
     irule ld_write_operand_defined >> simp[] >> metis_tac[]) >>
  simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >> disj1_tac >>
  pure_rewrite_tac[inst_mem_below_frontier_def, EVERY_MEM] >>
  qx_gen_tac `r` >> PairCases_on `r` >> pure_rewrite_tac[UNCURRY] >>
  disch_tac >> Cases_on `r1 = 0` >- simp[] >> simp[] >>
  `?getops ranges. MEM (getops,ranges)
    [(mem_read_ops,source_memory_read_ranges);
     (mem_write_ops,source_memory_write_ranges)] /\
    MEM (r0,r1) (ranges inst t)` by
    (gvs[MEM_APPEND] >> metis_tac[MEM]) >>
  drule_all ld_oracle_call_range_transport >> strip_tac >>
  `MEM ops.iao_ofst inst.inst_operands` by
    (gvs[MEM, mem_read_ops_def, mem_write_ops_def]) >>
  `op_taint tn ops.iao_ofst = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl_tac [`fn`,`inst`,`s`] >> gvs[]) >>
  `?xx. eval_operand ops.iao_ofst f.lf_src = SOME xx /\
    (op_prov f.lf_H ops.iao_ofst = NONE ==> xx = y) /\
    (!a. op_prov f.lf_H ops.iao_ofst = SOME a ==>
         ld_wordrel A (SOME a) xx y)` by
    (irule ld_numeric_operand_observation >> simp[] >>
     conj_tac >- (qexists_tac `tn` >> simp[]) >>
     conj_tac >- (qexists_tac `inst` >> gvs[]) >>
     metis_tac[]) >>
  `xx = x` by metis_tac[optionTheory.SOME_11] >>
  ` (w2n x+r1 <= lo /\ y=x) \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n x=b+delta /\ w2n y=c+delta /\ delta+r1 <= sz)` by
    (`0 < r1` by decide_tac >>
     qpat_x_assum `MEM (getops,ranges) _`
       (strip_assume_tac o REWRITE_RULE [MEM, PAIR_EQ])
     >- (gvs[] >> drule_all ld_read_access_classified >> simp[]) >>
     gvs[] >> drule_all ld_write_access_classified >> simp[]) >>
  qpat_assum `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= _`
    imp_res_tac >>
  qpat_x_assum `r0 = w2n y` SUBST1_TAC >>
  pure_asm_rewrite_tac[] >> decide_tac
QED

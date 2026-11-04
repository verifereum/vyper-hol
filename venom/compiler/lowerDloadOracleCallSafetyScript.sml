(* Current-instruction range safety does not require successful execution. *)
Theory lowerDloadOracleCallSafety
Ancestors
  lowerDloadOracleCallAssembly lowerDloadSafetyAllocBounds
  lowerDloadSafetyAmbient lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  unitMemInv unitTransformDefs memLocDefs ptrDiscipline
  codegenRel contextCodegenRel venomExecSemantics venomInst
  finite_map pred_set list words arithmetic

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

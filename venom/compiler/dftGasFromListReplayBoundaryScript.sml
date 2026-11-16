Theory dftGasFromListReplayBoundary
Ancestors
  dftGasFromListRestore dftGasFromListTraceDefs gasOracleReplay list alist

(* State restoration commutations are already exported as gas_eval_operands,
   gas_setup_callee, gas_merge_callee, gas_adopt_return, gas_bind_outputs. *)

Theorem trace_agrees_append[simp]:
  trace_agrees orc (xs ++ ys) <=>
  trace_agrees orc xs /\ trace_agrees orc ys
Proof
  simp[trace_agrees_def, trace_gas_def, MAP_APPEND, FLAT_APPEND]
QED

Theorem trace_agrees_take:
  trace_agrees orc xs ==> trace_agrees orc (TAKE n xs)
Proof
  metis_tac[TAKE_DROP, trace_agrees_append]
QED

Theorem trace_agrees_cons:
  trace_agrees orc ((e,fn,inst,s)::xs) <=>
  (inst.inst_opcode = GAS ==>
    orc e = (case s.vs_gas_readings of [] => 0w | w::_ => w)) /\
  trace_agrees orc xs
Proof
  Cases_on `inst.inst_opcode = GAS` >>
  simp[trace_agrees_def, trace_gas_def, visit_gas_def]
QED

Theorem trace_agrees_nil[simp]:
  trace_agrees orc []
Proof
  simp[trace_agrees_def, trace_gas_def]
QED

Theorem trace_agrees_lookup_fill:
  !obs keys vals source target.
    ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT keys /\
    LENGTH keys = LENGTH vals /\
    EVERY (\(key,w).
      ALOOKUP obs key = NONE \/ ALOOKUP obs key = SOME w)
      (ZIP (keys,vals)) /\
    trace_gas source = ZIP (keys,vals) /\
    EVERY (\kw. MEM kw obs) (trace_gas target) ==>
    trace_agrees
      (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
        NONE => 0w | SOME w => w) source /\
    trace_agrees
      (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
        NONE => 0w | SOME w => w) target
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,vals)))` by fs[MAP_ZIP] >>
  fs[EVERY_MEM] >>
  conj_tac >> simp[trace_agrees_def, EVERY_MEM] >>
  qx_gen_tac `kw` >> Cases_on `kw` >>
  simp[] >> strip_tac >>
  rename1 `(case ALOOKUP (obs ++ ZIP (keys,vals)) key of
    NONE => 0w | SOME x => x) = w`
  >- (`ALOOKUP (ZIP (keys,vals)) key = SOME w` by
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
      qpat_x_assum `!kw. MEM kw (ZIP _) ==> _`
        (qspec_then `(key,w)` mp_tac) >> simp[] >> strip_tac >>
      simp[ALOOKUP_APPEND] >> metis_tac[])
  >> `MEM (key,w) obs` by metis_tac[] >>
  `ALOOKUP obs key = SOME w` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  simp[ALOOKUP_APPEND]
QED

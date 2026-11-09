Theory makeSsaCurrentRenameTrace
Ancestors
  makeSsaCurrentAllocation makeSsaDefs makeSsaCurrentProps
  makeSsaCurrentTokens venomInst list alist pair combin

(* An annotation carries the definition token and its immutable source owner.
   Each step records the actual concrete push, not an invented renaming. *)
Definition current_outputs_trace_def:
  (current_outputs_trace [] s rs H E names s' rs' H' E' <=>
    names = [] /\ s' = s /\ rs' = rs /\ H' = H /\ E' = E) /\
  (current_outputs_trace ((t,v)::anns) s rs H E names s' rs' H' E' <=>
    ?n ns s1 rs1.
      push_current_name s rs v = (rs1,s1,n) /\ names = n::ns /\
      current_outputs_trace anns s1 rs1 (H ++ [(t,v,n)]) ((v =+ t) E)
        ns s' rs' H' E')
End

Definition current_annotations_ok_def:
  current_annotations_ok V H anns <=>
    ALL_DISTINCT (MAP FST anns) /\
    EVERY (\(t,v). (!w. t <> CurrentDefault w) /\
      ~MEM t (MAP FST H) /\ MEM v V) anns
End

Theorem current_outputs_trace_projection:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  rename_current_outputs s rs (MAP SND anns) = (rs',s',names)
Proof
  Induct >> simp[current_outputs_trace_def, rename_current_outputs_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def, rename_current_outputs_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem current_annotations_tail:
  current_annotations_ok V H ((t,v)::anns) ==>
  current_annotations_ok V (H ++ [(t,v,n)]) anns
Proof
  simp[current_annotations_ok_def, MAP_APPEND, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  first_x_assum drule >> simp[] >> metis_tac[FST]
QED

Theorem current_outputs_trace_preserves:
  !anns s rs H E names s' rs' H' E' V.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V ==>
  current_allocation_consistent V H' s' rs' /\ current_env_realizes H' E' rs' V
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt gen_tac >> strip_tac >>
  `current_annotations_ok V (H ++ [(h0,h1,n)]) anns` by
    metis_tac[current_annotations_tail] >>
  `(!w. h0 <> CurrentDefault w) /\ ~MEM h0 (MAP FST H) /\ MEM h1 V` by
    fs[current_annotations_ok_def] >>
  `current_allocation_consistent V (H ++ [(h0,h1,n)]) s1 rs1` by
    (irule current_push_consistent >> metis_tac[]) >>
  `current_env_realizes (H ++ [(h0,h1,n)]) ((h1 =+ h0) E) rs1 V` by
    (irule current_push_env_realizes >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_outputs_trace_exists:
  !anns s rs H E rs' s' names.
  rename_current_outputs s rs (MAP SND anns) = (rs',s',names) ==>
  ?H' E'. current_outputs_trace anns s rs H E names s' rs' H' E'
Proof
  Induct >> simp[rename_current_outputs_def, current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[rename_current_outputs_def, current_outputs_trace_def] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`H'`, `E'`] >> metis_tac[]
QED

Theorem current_outputs_trace_history:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  ?tail. H' = H ++ tail
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `[(h0,h1,n)] ++ tail` >> simp[APPEND_ASSOC]
QED

Theorem current_outputs_trace_exit_env:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  E' = FOLDL (\env (t,v). (v =+ t) env) E anns
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem current_outputs_trace_names:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_annotations_ok V H anns ==>
  LIST_REL (\(t,v) n. current_token_name H' t = SOME n) anns names
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (drule current_outputs_trace_history >> strip_tac >> gvs[] >>
      irule current_token_name_append_stable >>
      irule current_token_name_new >> fs[current_annotations_ok_def]) >>
  first_x_assum irule >> metis_tac[current_annotations_tail]
QED

Definition current_inst_trace_def:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' <=>
    MAP SND anns = inst.inst_outputs /\
    ?names. current_outputs_trace anns s rs H E names s' rs' H' E' /\
    inst' = if inst.inst_opcode = PHI then inst with inst_outputs := names
      else inst with <| inst_operands := rename_current_operands rs inst.inst_operands;
                       inst_outputs := names |>
End

Theorem current_inst_trace_projection:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  rename_current_inst s rs inst = (rs',s',inst')
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  drule current_outputs_trace_projection >> simp[rename_current_inst_def] >>
  strip_tac >> gvs[] >> Cases_on `inst.inst_opcode = PHI` >> simp[]
QED

Theorem current_inst_trace_exists:
  MAP SND anns = inst.inst_outputs /\
  rename_current_inst s rs inst = (rs',s',inst') ==>
  ?H' E'. current_inst_trace anns inst s rs H E inst' s' rs' H' E'
Proof
  simp[rename_current_inst_def] >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `?H' E'. current_outputs_trace anns s rs H E outs' s' rs' H' E'` by
    (irule current_outputs_trace_exists >> simp[]) >>
  simp[current_inst_trace_def] >> metis_tac[]
QED

Theorem current_inst_trace_operands:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  inst'.inst_operands = if inst.inst_opcode = PHI then inst.inst_operands
    else rename_current_operands rs inst.inst_operands
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem current_inst_trace_outputs:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns ==>
  LIST_REL (\(t,v) n. current_token_name H' t = SOME n) anns inst'.inst_outputs
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  metis_tac[current_outputs_trace_names]
QED

Theorem current_inst_trace_preserves:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V ==>
  current_allocation_consistent V H' s' rs' /\ current_env_realizes H' E' rs' V
Proof
  simp[current_inst_trace_def] >> metis_tac[current_outputs_trace_preserves]
QED

Definition current_local_trace_def:
  (current_local_trace [] insts s rs H E insts' s' rs' H' E' <=>
    insts = [] /\ insts' = [] /\ s' = s /\ rs' = rs /\ H' = H /\ E' = E) /\
  (current_local_trace (anns::annss) insts s rs H E insts' s' rs' H' E' <=>
    ?inst rest inst1 rest1 s1 rs1 H1 E1.
      insts = inst::rest /\ insts' = inst1::rest1 /\
      current_inst_trace anns inst s rs H E inst1 s1 rs1 H1 E1 /\
      current_local_trace annss rest s1 rs1 H1 E1 rest1 s' rs' H' E')
End

Theorem current_local_trace_projection:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  rename_current_block_insts s rs insts = (rs',s',insts')
Proof
  Induct >> simp[current_local_trace_def, rename_current_block_insts_def] >>
  rpt strip_tac >> gvs[rename_current_block_insts_def] >>
  drule current_inst_trace_projection >> strip_tac >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_local_trace_exists:
  !annss insts s rs H E rs' s' insts'.
  LIST_REL (\anns inst. MAP SND anns = inst.inst_outputs) annss insts /\
  rename_current_block_insts s rs insts = (rs',s',insts') ==>
  ?H' E'. current_local_trace annss insts s rs H E insts' s' rs' H' E'
Proof
  Induct >> Cases_on `insts` >>
  simp[rename_current_block_insts_def, current_local_trace_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (rs',s',insts')` mp_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `?H1 E1. current_inst_trace h' h s rs H E inst' s'' rs'' H1 E1` by
    (irule current_inst_trace_exists >> simp[]) >>
  first_x_assum drule_all >>
  disch_then (qspecl_then [`H1`, `E1`] strip_assume_tac) >>
  qexistsl_tac [`H'`, `E'`] >> metis_tac[]
QED

Theorem current_outputs_trace_keys:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  MAP FST H' = MAP FST H ++ MAP FST anns
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem current_annotations_split:
  current_annotations_ok V H (anns ++ rest) ==>
  current_annotations_ok V H anns /\
  current_annotations_ok V (H ++ MAP (\(t,v). (t,v,f t)) anns) rest
Proof
  simp[current_annotations_ok_def, ALL_DISTINCT_APPEND, MAP_APPEND,
       MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD,
       EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem current_outputs_trace_remaining:
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_annotations_ok V H (anns ++ rest) ==>
  current_annotations_ok V H' rest
Proof
  rpt strip_tac >> drule current_outputs_trace_keys >> strip_tac >>
  drule current_annotations_split >> strip_tac >>
  fs[current_annotations_ok_def, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF,
     pairTheory.UNCURRY, ETA_AX]
QED

Theorem current_local_trace_preserves:
  !annss insts s rs H E insts' s' rs' H' E' V.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V ==>
  current_allocation_consistent V H' s' rs' /\ current_env_realizes H' E' rs' V
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  `current_allocation_consistent V H1 s1 rs1 /\ current_env_realizes H1 E1 rs1 V` by
    (irule current_inst_trace_preserves >> metis_tac[]) >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_inst_trace_exit_env:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  E' = FOLDL (\env (t,v). (v =+ t) env) E anns
Proof
  simp[current_inst_trace_def] >> metis_tac[current_outputs_trace_exit_env]
QED

Theorem current_local_trace_exit_env:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  E' = FOLDL (\env (t,v). (v =+ t) env) E (FLAT annss)
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  drule current_inst_trace_exit_env >> strip_tac >>
  first_x_assum drule >> simp[rich_listTheory.FOLDL_APPEND]
QED

Theorem current_local_trace_history:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  ?tail. H' = H ++ tail
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  fs[current_inst_trace_def] >>
  drule current_outputs_trace_history >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  qexists_tac `tail ++ tail'` >> simp[APPEND_ASSOC]
QED

Theorem current_local_trace_keys:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  MAP FST H' = MAP FST H ++ MAP FST (FLAT annss)
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  fs[current_inst_trace_def] >>
  drule current_outputs_trace_keys >> strip_tac >>
  first_x_assum drule >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem current_local_trace_latest:
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  MEM v V ==>
  current_token_name H'
    (FOLDL (\env (t,v). (v =+ t) env) E (FLAT annss) v) =
      SOME (latest_current_name rs' v)
Proof
  rpt strip_tac >> drule_all current_local_trace_preserves >> strip_tac >>
  drule current_local_trace_exit_env >> strip_tac >>
  fs[current_env_realizes_def]
QED

Theorem current_local_trace_head:
  current_local_trace (anns::annss) (inst::rest) s rs H E
    insts' s' rs' H' E' ==>
  ?inst1 rest1 s1 rs1 H1 E1.
    insts' = inst1::rest1 /\
    current_inst_trace anns inst s rs H E inst1 s1 rs1 H1 E1 /\
    current_local_trace annss rest s1 rs1 H1 E1 rest1 s' rs' H' E'
Proof
  simp[current_local_trace_def]
QED

Theorem current_inst_trace_entry_name:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_env_realizes H E rs V /\ MEM v V ==>
  current_token_name H (E v) = SOME (latest_current_name rs v)
Proof
  simp[current_env_realizes_def]
QED

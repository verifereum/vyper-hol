(* Memory-write commutation, coalescing and replay facts. *)
Theory venomWriteReplayProps
Ancestors
  mmCopyEquiv memoryReadRel frameViewMemory dftCommutation
  regularCallEmitSim venomMemProps venomExecSemantics venomState
  rich_list list
Libs
  wordsLib finite_mapLib stepInstBaseLib

Theorem zero_merge_bound:
  d1 <= d2 /\ d1 + n1 <= eom /\ d2 + n2 <= eom ==>
  d1 + (MAX (d1+n1) (d2+n2) - d1) <= eom
Proof
  simp[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem zero_replace_merge:
  d1 <= d2 /\ d2 <= d1+n1 /\
  MAX (d1+n1) (d2+n2) <= LENGTH mem ==>
  replace_bytes d2 (REPLICATE n2 0w)
    (replace_bytes d1 (REPLICATE n1 0w) mem) =
  replace_bytes d1 (REPLICATE (MAX (d1+n1) (d2+n2)-d1) 0w) mem
Proof
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE,
    LENGTH_DROP, LENGTH_REPLICATE] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE,
    LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP, LENGTH_REPLICATE, arithmeticTheory.MAX_DEF] >>
  gvs[]
QED

Theorem expand_mem_max:
  expand_mem (expand_mem mem n) m = expand_mem mem (MAX n m)
Proof
  Cases_on `n <= m`
  >- (`MAX n m = m` by (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
      simp[expand_mem_monotone]) >>
  `MAX n m = n` by simp[arithmeticTheory.MAX_DEF] >>
  `~(m > LENGTH (expand_mem mem n))` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  simp[Once expand_mem_def]
QED

Theorem zero_write_merge:
  d1 <= d2 /\ d2 <= d1+n1 ==>
  write_memory_with_expansion d2 (REPLICATE n2 0w)
    (write_memory_with_expansion d1 (REPLICATE n1 0w) s) =
  write_memory_with_expansion d1
    (REPLICATE (MAX (d1+n1) (d2+n2)-d1) 0w) s
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1+n1 <= LENGTH (expand_mem s.vs_memory (d1+n1))` by simp[expand_mem_ge] >>
  simp[expand_replace] >>
  `d1 + (MAX (d1+n1) (d2+n2) - d1) = MAX (d1+n1) (d2+n2)` by
    (simp[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  simp[venomStateTheory.venom_state_component_equality] >>
  simp[expand_mem_max] >>
  irule zero_replace_merge >> simp[]
QED

Theorem zero_write_empty:
  write_memory_with_expansion dst [] s =
    s with vs_memory := expand_mem s.vs_memory dst
Proof
  simp[write_as_replace, replace_bytes_def, TAKE_DROP]
QED

Theorem replace_disjoint_commute:
  (d1 + LENGTH bs1 <= d2 \/ d2 + LENGTH bs2 <= d1) /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) <= LENGTH mem ==>
  replace_bytes d2 bs2 (replace_bytes d1 bs1 mem) =
  replace_bytes d1 bs1 (replace_bytes d2 bs2 mem)
Proof
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE,
    LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND,
    LENGTH_TAKE, LENGTH_DROP, arithmeticTheory.MAX_DEF] >> gvs[]
QED

Theorem write_disjoint_commute:
  (d1 + LENGTH bs1 <= d2 \/ d2 + LENGTH bs2 <= d1) ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion d1 bs1 (write_memory_with_expansion d2 bs2 s)
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1 + LENGTH bs1 <= LENGTH (expand_mem s.vs_memory (d1 + LENGTH bs1))` by
    simp[expand_mem_ge] >>
  `d2 + LENGTH bs2 <= LENGTH (expand_mem s.vs_memory (d2 + LENGTH bs2))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, expand_mem_max,
       venomStateTheory.venom_state_component_equality] >>
  simp[arithmeticTheory.MAX_COMM] >>
  irule replace_disjoint_commute >> simp[] >>
  simp[arithmeticTheory.MAX_DEF]
QED

Theorem write_log_commute:
  !ws s. EVERY (\(d,bs). d + LENGTH bs <= a \/ a + LENGTH bytes <= d) ws ==>
  write_memory_with_expansion a bytes
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion a bytes s) ws
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  simp[write_disjoint_commute]
QED

Theorem zero_log_merge:
  d1 <= d2 /\ d2 <= d1+n1 /\
  EVERY (\(d,bs). d + LENGTH bs <= d2 \/ d2+n2 <= d) ws ==>
  write_memory_with_expansion d2 (REPLICATE n2 0w)
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 (REPLICATE n1 0w) s) ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion d1
      (REPLICATE (MAX (d1+n1) (d2+n2)-d1) 0w) s) ws
Proof
  strip_tac >> simp[write_log_commute, zero_write_merge]
QED

Theorem write_pair_length:
  LENGTH (write_memory_with_expansion d2 bs2
    (write_memory_with_expansion d1 bs1 s)).vs_memory =
  MAX (LENGTH s.vs_memory) (MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2))
Proof
  simp[write_as_replace, replace_bytes_len, expand_mem_ge] >>
  simp[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem capture_store:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [Lit dst; Var v] /\
  lookup_var v s = SOME (mload src s) /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_memory =
    (write_memory_with_expansion (w2n dst) (read_memory src 32 s) s).vs_memory
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_write2_def,
      venomStateTheory.eval_operand_def] >>
  simp[mload_mstore_eq_mcopy_state, venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.read_memory_def]
QED

Theorem capture_copy:
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [Lit dst; Lit src; Lit len] /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_memory =
    (write_memory_with_expansion (w2n dst)
      (read_memory (w2n src) (w2n len) s) s).vs_memory
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK t` mp_tac >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[venomExecSemanticsTheory.step_inst_base_def,
      venomStateTheory.eval_operand_def] >>
  simp[venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Theorem known_value_frame:
  lookup_var x s = SOME value /\ step_inst_base inst s = OK t /\
  ~MEM (Var x) inst.inst_operands /\ ~MEM x inst.inst_outputs ==>
  lookup_var x t = SOME value
Proof
  strip_tac >>
  `update_var x value s = s` by
    (simp[venomStateTheory.update_var_def] >>
     `s.vs_vars |+ (x,value) = s.vs_vars` by
       (irule finite_mapTheory.FUPDATE_ELIM >>
        gvs[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
     simp[]) >>
  `step_inst_base inst (update_var x value s) =
   map_result_state (update_var x value) (step_inst_base inst s)` by
    (irule step_inst_base_frame >> metis_tac[]) >>
  gvs[map_result_state_def] >>
  qpat_x_assum `t = update_var x value t` (fn th => once_rewrite_tac[th]) >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem read_write_disjoint:
  n = 0 \/ bs = [] \/ a+n <= d \/ d+LENGTH bs <= a ==>
  read_memory a n (write_memory_with_expansion d bs s) = read_memory a n s
Proof
  Cases_on `n = 0` >- simp[venomStateTheory.read_memory_def] >>
  Cases_on `bs = []`
  >- (gvs[venomStateTheory.read_memory_def, write_as_replace,
          replace_bytes_def, expand_mem_def] >>
      rw[LIST_EQ_REWRITE, EL_APPEND_EQN, EL_TAKE, EL_DROP, EL_REPLICATE] >>
      rw[] >> gvs[]) >>
  strip_tac >>
  simp[venomStateTheory.read_memory_def, write_as_replace] >>
  irule read_nonoverlap_expand >> simp[]
QED

Theorem read_same_write:
  read_memory a n s = read_memory a n t ==>
  read_memory a n (write_memory_with_expansion d bs s) =
  read_memory a n (write_memory_with_expansion d bs t)
Proof
  simp[venomStateTheory.read_memory_def,
       memoryReadRelTheory.venom_returndata_read_byte, GENLIST_FUN_EQ] >>
  strip_tac >> rpt strip_tac >>
  irule frameViewMemoryTheory.write_memory_byte_agreement >>
  first_x_assum irule >> simp[]
QED

Theorem selective_replay:
  j <= r /\
  (!q. q < r ==> (H (SUC q)).vs_memory =
    (case cap q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  t0.vs_memory = (H 0).vs_memory /\
  (!q d bs. q < j /\ P q /\ cap q = SOME (d,bs) ==>
    a+n <= d \/ d+LENGTH bs <= a \/ n = 0 \/ bs = []) /\
  (!q d bs. j <= q /\ q < r /\ ~P q /\ cap q = SOME (d,bs) ==>
    a+n <= d \/ d+LENGTH bs <= a \/ n = 0 \/ bs = []) /\
  t = FOLDL (\st q. if P q then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    t0 (COUNT_LIST r) ==>
  read_memory a n t = read_memory a n (H j)
Proof
  strip_tac >>
  qabbrev_tac `R = \q. FOLDL (\st q. if P q then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    t0 (COUNT_LIST q)` >>
  `R 0 = t0 /\ (!q. R (SUC q) = if P q then R q else
     case cap q of NONE => R q | SOME (d,bs) => write_memory_with_expansion d bs (R q))` by
    simp[Abbr `R`, COUNT_LIST_SNOC, FOLDL_SNOC] >>
  `!q. q <= r ==> read_memory a n (R q) = read_memory a n (H (MIN q j))` by
    (Induct >- simp[venomStateTheory.read_memory_def] >>
     strip_tac >> `q <= r /\ q < r` by decide_tac >>
     first_x_assum (drule_then assume_tac) >>
     Cases_on `q < j`
     >- (`MIN q j = q /\ MIN (SUC q) j = SUC q` by
           (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
         gvs[] >>
         qpat_x_assum `!q. q < r ==> _` (qspec_then `q` mp_tac) >> simp[] >>
         Cases_on `cap q` >- gvs[venomStateTheory.read_memory_def] >>
         PairCases_on `x` >> simp[] >> strip_tac >>
         Cases_on `P q`
         >- (gvs[] >>
             `read_memory a n (write_memory_with_expansion x0 x1 (H q)) =
              read_memory a n (H q)` by
               (irule read_write_disjoint >> metis_tac[]) >>
             gvs[venomStateTheory.read_memory_def]) >>
         gvs[] >>
         `read_memory a n (write_memory_with_expansion x0 x1 (R q)) =
          read_memory a n (write_memory_with_expansion x0 x1 (H q))` by
           (irule read_same_write >> simp[]) >>
         gvs[venomStateTheory.read_memory_def]) >>
     `MIN q j = j /\ MIN (SUC q) j = j` by
       (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
     gvs[] >> Cases_on `P q` >- simp[] >>
     Cases_on `cap q` >- simp[] >>
     PairCases_on `x` >> simp[] >>
     `read_memory a n (write_memory_with_expansion x0 x1 (R q)) =
      read_memory a n (R q)` by
       (irule read_write_disjoint >> metis_tac[arithmeticTheory.NOT_LESS]) >>
     simp[]) >>
  first_x_assum (qspec_then `r` mp_tac) >>
  simp[arithmeticTheory.MIN_DEF, Abbr `R`] >> metis_tac[]
QED

Theorem read_write_log:
  !ws s. EVERY (\(d,bs). n = 0 \/ bs = [] \/ a+n <= d \/ d+LENGTH bs <= a) ws ==>
  read_memory a n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  read_memory a n s
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then (fn th => rewrite_tac[th])) >>
  simp[read_write_disjoint]
QED

Theorem read_write_log_memory:
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory /\
  EVERY (\(d,bs). n = 0 \/ bs = [] \/ a+n <= d \/ d+LENGTH bs <= a) ws ==>
  read_memory a n u = read_memory a n v
Proof
  strip_tac >>
  `read_memory a n u = read_memory a n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws)` by
    simp[venomStateTheory.read_memory_def] >>
  metis_tac[read_write_log]
QED

Theorem mload_write_log_memory:
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory /\
  EVERY (\(d,bs). a+32 <= d \/ d+LENGTH bs <= a) ws ==>
  mload a u = mload a v
Proof
  strip_tac >>
  `read_memory a 32 u = read_memory a 32 v` by
    (irule read_write_log_memory >> qexists_tac `ws` >>
     simp[] >> gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  gvs[venomStateTheory.read_memory_def, venomStateTheory.mload_def]
QED

Theorem mcopy_write_log:
  EVERY (\(d,bs). (src+n <= d \/ d+LENGTH bs <= src) /\
                     (dst+n <= d \/ d+LENGTH bs <= dst)) ws ==>
  mcopy dst src n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (mcopy dst src n s) ws
Proof
  strip_tac >>
  `EVERY (\(d,bs). n = 0 \/ bs = [] \/ src+n <= d \/ d+LENGTH bs <= src) ws` by
    (gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `read_memory src n
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws) =
    read_memory src n s` by simp[read_write_log] >>
  simp[venomExecSemanticsTheory.mcopy_def,
       GSYM venomStateTheory.read_memory_def] >>
  irule write_log_commute >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD, venomStateTheory.read_memory_def,
      LENGTH_TAKE, LENGTH_DROP] >> metis_tac[]
QED

Theorem mcopy_write_log_memory:
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws).vs_memory /\
  EVERY (\(d,bs). (src+n <= d \/ d+LENGTH bs <= src) /\
                     (dst+n <= d \/ d+LENGTH bs <= dst)) ws ==>
  (mcopy dst src n u).vs_memory =
  (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (mcopy dst src n v) ws).vs_memory
Proof
  strip_tac >>
  drule mcopy_write_log >>
  disch_then (qspec_then `v` (fn th => once_rewrite_tac[GSYM th])) >>
  simp[venomExecSemanticsTheory.mcopy_def, write_as_replace]
QED

Theorem payload_replace_merge:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  d1 + LENGTH merged <= LENGTH mem ==>
  replace_bytes d2 bs2 (replace_bytes d1 bs1 mem) =
  replace_bytes d1 merged mem
Proof
  strip_tac >>
  `LENGTH bs1 <= LENGTH merged /\ d2-d1 + LENGTH bs2 <= LENGTH merged` by
    (gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!i. i < LENGTH bs1 ==> EL i bs1 = EL i merged` by
    metis_tac[EL_TAKE] >>
  `!i. i < LENGTH bs2 ==> EL i bs2 = EL (i + (d2-d1)) merged` by
    (rpt strip_tac >> qpat_x_assum `bs2 = _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_TAKE, EL_DROP]) >>
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  gvs[EL_DROP, arithmeticTheory.MAX_DEF]
QED

Theorem payload_write_merge:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion d1 merged s
Proof
  strip_tac >> simp[write_as_replace] >>
  `d1 + LENGTH bs1 <= LENGTH (expand_mem s.vs_memory (d1 + LENGTH bs1))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, venomStateTheory.venom_state_component_equality,
       expand_mem_max] >>
  irule payload_replace_merge >> simp[expand_mem_ge]
QED

Theorem payload_log_merge:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  EVERY (\(d,bs). d + LENGTH bs <= d2 \/ d2 + LENGTH bs2 <= d) ws ==>
  write_memory_with_expansion d2 bs2
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 bs1 s) ws) =
  FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
    (write_memory_with_expansion d1 merged s) ws
Proof
  strip_tac >>
  drule_all payload_write_merge >>
  disch_then (qspec_then `s` assume_tac) >>
  simp[write_log_commute]
QED

Theorem payload_late_discharge:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  EVERY (\(d,bs). d + LENGTH bs <= d1 \/ d1 + LENGTH bs1 <= d) ws ==>
  write_memory_with_expansion d2 bs2
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 bs1 s) ws) =
  write_memory_with_expansion d1 merged
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws)
Proof
  strip_tac >>
  drule_all payload_write_merge >> strip_tac >>
  drule write_log_commute >>
  disch_then (qspec_then `s` (fn th => once_rewrite_tac[GSYM th])) >>
  simp[]
QED

Theorem payload_replace_merge_reverse:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) /\
  d1 + LENGTH merged <= LENGTH mem ==>
  replace_bytes d1 bs1 (replace_bytes d2 bs2 mem) =
  replace_bytes d1 merged mem
Proof
  strip_tac >>
  `LENGTH bs1 <= LENGTH merged /\ d2-d1 + LENGTH bs2 <= LENGTH merged` by
    (gvs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `!i. i < LENGTH bs1 ==> EL i bs1 = EL i merged` by
    metis_tac[EL_TAKE] >>
  `!i. i < LENGTH bs2 ==> EL i bs2 = EL (i + (d2-d1)) merged` by
    (rpt strip_tac >> qpat_x_assum `bs2 = _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_TAKE, EL_DROP]) >>
  rw[LIST_EQ_REWRITE, replace_bytes_def, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  rw[EL_APPEND_EQN, EL_TAKE, EL_DROP, LENGTH_APPEND, LENGTH_TAKE, LENGTH_DROP] >>
  gvs[EL_DROP, arithmeticTheory.MAX_DEF]
QED

Theorem payload_write_merge_reverse:
  d1 <= d2 /\ d2 <= d1 + LENGTH bs1 /\
  d1 + LENGTH merged = MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) merged /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-d1) merged) ==>
  write_memory_with_expansion d1 bs1 (write_memory_with_expansion d2 bs2 s) =
  write_memory_with_expansion d1 merged s
Proof
  strip_tac >> simp[write_as_replace] >>
  `d2 + LENGTH bs2 <= LENGTH (expand_mem s.vs_memory (d2 + LENGTH bs2))` by
    simp[expand_mem_ge] >>
  simp[expand_replace, venomStateTheory.venom_state_component_equality,
       expand_mem_max, arithmeticTheory.MAX_COMM] >>
  irule payload_replace_merge_reverse >> simp[expand_mem_ge]
QED

Theorem payload_write_merge_unordered:
  dst = MIN d1 d2 /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) = dst + LENGTH merged /\
  (d1 <= d2 /\ d2 <= d1 + LENGTH bs1 \/
   d2 <= d1 /\ d1 <= d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) (DROP (d1-dst) merged) /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-dst) merged) ==>
  write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 s) =
  write_memory_with_expansion dst merged s
Proof
  strip_tac >> Cases_on `d1 <= d2`
  >- (`dst = d1` by simp[arithmeticTheory.MIN_DEF] >> gvs[] >>
      irule payload_write_merge >>
      simp[] >> gvs[arithmeticTheory.MAX_DEF]) >>
  `dst = d2` by simp[arithmeticTheory.MIN_DEF] >> gvs[] >>
  irule payload_write_merge_reverse >>
  simp[arithmeticTheory.MAX_COMM]
QED

Theorem payload_late_discharge_unordered:
  dst = MIN d1 d2 /\
  MAX (d1 + LENGTH bs1) (d2 + LENGTH bs2) = dst + LENGTH merged /\
  (d1 <= d2 /\ d2 <= d1 + LENGTH bs1 \/
   d2 <= d1 /\ d1 <= d2 + LENGTH bs2) /\
  bs1 = TAKE (LENGTH bs1) (DROP (d1-dst) merged) /\
  bs2 = TAKE (LENGTH bs2) (DROP (d2-dst) merged) /\
  EVERY (\(d,bs). d + LENGTH bs <= d1 \/ d1 + LENGTH bs1 <= d) ws ==>
  write_memory_with_expansion d2 bs2
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (write_memory_with_expansion d1 bs1 s) ws) =
  write_memory_with_expansion dst merged
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws)
Proof
  strip_tac >>
  `!v. write_memory_with_expansion d2 bs2 (write_memory_with_expansion d1 bs1 v) =
       write_memory_with_expansion dst merged v` by
    (gen_tac >> irule payload_write_merge_unordered >> simp[]) >>
  drule write_log_commute >>
  disch_then (qspec_then `s` (fn th => once_rewrite_tac[GSYM th])) >>
  simp[]
QED

Theorem write_log_memory_cong:
  !ws s t. s.vs_memory = t.vs_memory ==>
  (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws).vs_memory =
  (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) t ws).vs_memory
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[write_as_replace]
QED

Theorem capture_create:
  EVERY (\j. ?d bs. cap j = SOME (d,bs) /\ C (EL j is) (H j) d bs) js /\
  cap n = SOME (d,bs) /\ C (EL n is) (H n) d bs ==>
  EVERY (\j. ?d bs. cap j = SOME (d,bs) /\ C (EL j is) (H j) d bs) (js ++ [n])
Proof
  simp[] >> metis_tac[]
QED

Theorem write_log_partition:
  !js s.
  (!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k ==>
    FST (wr j) + LENGTH (SND (wr j)) <= FST (wr k) \/
    FST (wr k) + LENGTH (SND (wr k)) <= FST (wr j)) ==>
  FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st) s js =
  FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
    (FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
      s (FILTER P js)) (FILTER (\j. ~P j) js)
Proof
  Induct_on `js` >- simp[] >> rpt gen_tac >> strip_tac >>
  `!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k ==>
    FST (wr j) + LENGTH (SND (wr j)) <= FST (wr k) \/
    FST (wr k) + LENGTH (SND (wr k)) <= FST (wr j)` by
      (rpt strip_tac >>
       first_x_assum (qspecl_then [`h::pre`, `j`, `mid`, `k`, `post`] mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `write_memory_with_expansion (FST (wr h)) (SND (wr h)) s` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> Cases_on `P h`
  >- simp[] >>
  `EVERY (\(d,bs). d + LENGTH bs <= FST (wr h) \/
    FST (wr h) + LENGTH (SND (wr h)) <= d) (MAP wr (FILTER P js))` by
    (simp[EVERY_MEM, MEM_MAP, MEM_FILTER, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> gvs[] >>
     rename1 `MEM k js` >>
     qpat_x_assum `MEM k js`
       (qx_choose_then `pre` (qx_choose_then `post` assume_tac) o REWRITE_RULE [MEM_SPLIT]) >>
     qpat_x_assum `!pre j mid k post. h::js = _ /\ _ ==> _`
       (qspecl_then [`[]`, `h`, `pre`, `k`, `post`] mp_tac) >>
     gvs[quantHeuristicsTheory.PAIR_EQ_EXPAND]) >>
  drule write_log_commute >> disch_then (qspec_then `s` mp_tac) >>
  simp[FOLDL_MAP, pairTheory.UNCURRY, combinTheory.o_DEF] >>
  strip_tac >> simp[]
QED

Theorem capture_log_canonical:
  !js ws. LIST_REL (\j w. cap j = SOME w) js ws ==>
    ws = MAP (THE o cap) js /\ EVERY (\j. IS_SOME (cap j)) js
Proof
  Induct_on `js` >> Cases_on `ws` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem mload_bytes:
  word_to_bytes (mload src s) T = read_memory src 32 s
Proof
  simp[venomStateTheory.mload_def, venomStateTheory.read_memory_def] >>
  irule venomMemPropsTheory.word_bytes_roundtrip_256 >> simp[LENGTH_TAKE_EQ]
QED

Theorem write_log_length:
  !ws s. LENGTH (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws).vs_memory =
    MAX (LENGTH s.vs_memory) (MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws))
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion,
    arithmeticTheory.MAX_ASSOC]
QED

Theorem write_log_byte:
  !ws s. (!d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs ==>
      EL (a-d) bs = b) ==>
    read_byte a (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws).vs_memory =
      if (?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs)
      then b else read_byte a s.vs_memory
Proof
  Induct_on `ws` >- simp[] >>
  Cases_on `h` >> simp[] >> rpt strip_tac >>
  simp[regularCallEmitSimTheory.read_byte_write_memory_with_expansion] >>
  Cases_on `?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs`
  >- (simp[] >> metis_tac[]) >>
  Cases_on `q <= a /\ a < q + LENGTH r` >> simp[] >> metis_tac[]
QED

Theorem write_log_frame:
  !ws s. ?m. FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s ws =
    s with vs_memory := m
Proof
  Induct_on `ws` >- simp[venomStateTheory.venom_state_component_equality] >>
  Cases_on `h` >> simp[] >> gen_tac >>
  first_x_assum (qspec_then `write_memory_with_expansion q r s` strip_assume_tac) >>
  qexists `m` >> simp[write_as_replace]
QED

Theorem write_log_endpoint:
  (!d bs. MEM (d,bs) ws ==> d + LENGTH bs <= e) /\
  (?d bs. MEM (d,bs) ws /\ d + LENGTH bs = e) ==>
  MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = e
Proof
  rpt strip_tac >> sym_tac >> irule MAX_LIST_TEST >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  metis_tac[MEM]
QED

Theorem selective_segment_replay:
  b <= j /\ j <= r /\
  (!q. b <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case cap q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  (!q d bs. b <= q /\ q < j /\ P q /\ cap q = SOME (d,bs) ==>
    a+n <= d \/ d+LENGTH bs <= a \/ n = 0 \/ bs = []) /\
  (!q d bs. j <= q /\ q < r /\ ~P q /\ cap q = SOME (d,bs) ==>
    a+n <= d \/ d+LENGTH bs <= a \/ n = 0 \/ bs = []) /\
  t = FOLDL (\st q. if P q then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H b) (MAP (\q. b+q) (COUNT_LIST (r-b))) ==>
  read_memory a n t = read_memory a n (H j)
Proof
  strip_tac >>
  mp_tac (Q.INST [`H` |-> `\q. H (b+q)`, `cap` |-> `\q. cap (b+q)`,
    `P` |-> `\q. P (b+q)`, `j` |-> `j-b`, `r` |-> `r-b`, `t0` |-> `H b`]
    (SPEC_ALL selective_replay)) >>
  simp[GSYM rich_listTheory.FOLDL_MAP] >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> simp[arithmeticTheory.ADD_CLAUSES] >>
          first_x_assum irule >> decide_tac) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!q d bs. b <= q /\ _ ==> _` (qspec_then `b+q` mp_tac) >>
          `b+q < j` by decide_tac >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!q d bs. j <= q /\ _ ==> _` (qspec_then `b+q` mp_tac) >>
          `b+q < r` by decide_tac >> simp[]) >>
      simp[rich_listTheory.FOLDL_MAP]) >> simp[rich_listTheory.FOLDL_MAP]
QED

Theorem capture_fold:
  !xs s. FOLDL (\st j. case cap j of NONE => st
      | SOME (d,bs) => write_memory_with_expansion d bs st) s xs =
    FOLDL (\st (d,bs). write_memory_with_expansion d bs st) s
      (MAP (THE o cap) (FILTER (\j. IS_SOME (cap j)) xs))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `cap h` >> simp[] >> rename1 `cap h = SOME w` >>
  PairCases_on `w` >> simp[]
QED

Theorem interval_replay:
  !n a H cap. a <= n /\
  (!q. a <= q /\ q < n ==> (H (SUC q)).vs_memory =
    (case cap q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) ==>
  (H n).vs_memory = (FOLDL (\st q. case cap q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (n-a)))).vs_memory
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[rich_listTheory.COUNT_LIST_def]) >>
  rpt strip_tac >> Cases_on `a = SUC n`
  >- gvs[rich_listTheory.COUNT_LIST_def] >>
  `a <= n` by decide_tac >>
  ` (H n).vs_memory = (FOLDL (\st q. case cap q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (n-a)))).vs_memory` by
    (first_x_assum irule >> simp[]) >>
  pop_assum (mk_asm "replay") >>
  ` (H (SUC n)).vs_memory = (case cap n of NONE => H n
    | SOME (d,bs) => write_memory_with_expansion d bs (H n)).vs_memory` by
    (first_x_assum irule >> simp[]) >>
  `SUC n - a = SUC (n-a) /\ a+(n-a) = n` by decide_tac >>
  simp[rich_listTheory.COUNT_LIST_SNOC, MAP_SNOC,
    rich_listTheory.FOLDL_SNOC] >>
  Cases_on `cap n` >> gvs[] >> PairCases_on `x` >>
  gvs[write_as_replace] >> asm "replay" mp_tac >>
  pure_rewrite_tac[write_as_replace] >> disch_then (fn th => rewrite_tac[th])
QED



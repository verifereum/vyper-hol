(* TOP-LEVEL: the actual static-array iteration preserves its encoded prefix
   and copies the next element's bytes. Helpers expose natural child windows
   and frame the counter write; no second execution model is introduced. *)
Theory abiStaticLoopPayload
Ancestors
  abiStaticLoopMemory abiStaticLoopFrame abiStaticLoopRun abiStaticLoopBody
  memoryReadProps venomState venomExecSemantics words arithmetic list

Theorem abi_static_loop_payload_prefix_frame:
  !info elem_size dst_addr src_addr counter_addr labels i ss.
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = n2w i /\
    (elem_size = 0 \/ w2n dst_addr + 32 + i * elem_size < dimword(:256)) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + i * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n dst_addr + 32) ==>
    read_memory (w2n dst_addr + 32) (i * elem_size)
      (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels ss) =
      read_memory (w2n dst_addr + 32) (i * elem_size) ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `elem_size = 0`
  >- simp[read_memory_def] >>
  `w2n (dst_addr + 32w + n2w i * n2w elem_size) =
    w2n dst_addr + 32 + i * elem_size` by
    (irule abi_static_loop_child_address >> gvs[]) >>
  irule abi_static_loop_effect_read_frame >> conj_tac
  >- (gvs[] >> decide_tac) >>
  qexists_tac `elem_size` >> gvs[] >> decide_tac
QED

Theorem abi_static_loop_payload_element:
  !info elem_size dst_addr src_addr counter_addr labels i ss.
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = n2w i /\
    (elem_size = 0 \/ w2n dst_addr + 32 + i * elem_size < dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + i * elem_size < dimword(:256)) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + i * elem_size + elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n dst_addr + 32 + i * elem_size) ==>
    read_memory (w2n dst_addr + 32 + i * elem_size) elem_size
      (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels ss) =
      read_memory (w2n src_addr + 32 + i * elem_size) elem_size ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `elem_size = 0`
  >- simp[read_memory_def] >>
  `w2n (dst_addr + 32w + n2w i * n2w elem_size) =
    w2n dst_addr + 32 + i * elem_size` by
    (irule abi_static_loop_child_address >> gvs[]) >>
  `w2n (src_addr + 32w + n2w i * n2w elem_size) =
    w2n src_addr + 32 + i * elem_size` by
    (irule abi_static_loop_child_address >> gvs[]) >>
  mp_tac (Q.SPECL [`info`, `elem_size`, `dst_addr`, `src_addr`, `elem_size`,
    `elem_size`, `counter_addr`, `ss`] abi_static_loop_body_read_self) >>
  impl_tac >- (gvs[] >> decide_tac) >>
  simp[abi_static_loop_effect_def, memory_reads_jump_to] >> gvs[]
QED

Theorem abi_static_loop_payload_step:
  !info elem_size dst_addr src_addr counter_addr labels i ss initial.
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = n2w i /\
    (elem_size = 0 \/ w2n dst_addr + 32 + i * elem_size < dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + i * elem_size < dimword(:256)) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + i * elem_size + elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n dst_addr + 32) /\
    read_memory (w2n dst_addr + 32) (i * elem_size) ss =
      read_memory (w2n src_addr + 32) (i * elem_size) (initial:venom_state) /\
    read_memory (w2n src_addr + 32 + i * elem_size) elem_size ss =
      read_memory (w2n src_addr + 32 + i * elem_size) elem_size initial ==>
    read_memory (w2n dst_addr + 32) (SUC i * elem_size)
      (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels ss) =
      read_memory (w2n src_addr + 32) (SUC i * elem_size) initial
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`info`, `elem_size`, `dst_addr`, `src_addr`, `counter_addr`,
    `labels`, `i`, `ss`] abi_static_loop_payload_prefix_frame) >>
  impl_tac >- (gvs[] >> decide_tac) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`info`, `elem_size`, `dst_addr`, `src_addr`, `counter_addr`,
    `labels`, `i`, `ss`] abi_static_loop_payload_element) >>
  impl_tac >- (gvs[] >> decide_tac) >> DISCH_TAC >>
  `SUC i * elem_size = i * elem_size + elem_size` by simp[MULT_CLAUSES] >>
  pop_assum SUBST1_TAC >> simp_tac bool_ss [read_memory_split] >> gvs[]
QED

Theorem abi_static_loop_source_element:
  !src_addr elem_size i n ss initial.
    i < n /\
    read_memory (w2n (src_addr:bytes32) + 32) (n * elem_size) (ss:venom_state) =
      read_memory (w2n src_addr + 32) (n * elem_size) (initial:venom_state) ==>
    read_memory (w2n src_addr + 32 + i * elem_size) elem_size ss =
      read_memory (w2n src_addr + 32 + i * elem_size) elem_size initial
Proof
  rpt gen_tac >> DISCH_TAC >>
  `(i + 1) * elem_size <= n * elem_size` by fs[LE_MULT_RCANCEL] >>
  qpat_x_assum `(i + 1) * elem_size <= n * elem_size`
    (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`w2n (src_addr:bytes32) + 32`, `n * elem_size`,
    `i * elem_size`, `elem_size`, `ss`] read_memory_subwindow) >>
  impl_tac >- fs[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`w2n (src_addr:bytes32) + 32`, `n * elem_size`,
    `i * elem_size`, `elem_size`, `initial`] read_memory_subwindow) >>
  impl_tac >- fs[] >> fs[]
QED

Theorem abi_static_loop_prefix_windows:
  !k n elem_size src_start dst_start upper.
    (k:num) <= n /\ dst_start + n * elem_size <= upper /\
    (src_start + n * elem_size <= dst_start \/ dst_start + n * elem_size <= src_start) ==>
    dst_start + k * elem_size <= upper /\
    (src_start + n * elem_size <= dst_start \/ dst_start + k * elem_size <= src_start)
Proof
  rpt gen_tac >> strip_tac >>
  `k * elem_size <= n * elem_size` by simp[LE_MULT_RCANCEL] >> decide_tac
QED

Theorem abi_static_loop_source_frame:
  !k n info elem_size dst_addr src_addr counter_addr labels ss.
    k <= n /\
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = 0w /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * elem_size <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n src_addr + 32) ==>
    read_memory (w2n src_addr + 32) (n * elem_size)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) k ss) =
      read_memory (w2n src_addr + 32) (n * elem_size) ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `elem_size = 0`
  >- simp[read_memory_def] >>
  mp_tac (Q.SPECL [`k`, `n`, `elem_size`, `w2n (src_addr:bytes32) + 32`,
    `w2n (dst_addr:bytes32) + 32`, `dimword(:256)`] abi_static_loop_prefix_windows) >>
  impl_tac >- (gvs[] >> decide_tac) >> strip_tac >>
  mp_tac (Q.SPECL [`k`, `info`, `elem_size`, `dst_addr`, `src_addr`, `elem_size`,
    `counter_addr`, `labels`, `ss`, `w2n (src_addr:bytes32) + 32`, `n * elem_size`]
    abi_static_loop_effects_read_frame) >>
  impl_tac >- (gvs[] >> decide_tac) >> simp[]
QED

Theorem abi_static_loop_payload_advance:
  !k n info elem_size dst_addr src_addr counter_addr labels ss.
    k < n /\
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = 0w /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * elem_size <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n dst_addr + 32) /\
    read_memory (w2n dst_addr + 32) (k * elem_size)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) k ss) =
      read_memory (w2n src_addr + 32) (k * elem_size) ss ==>
    read_memory (w2n dst_addr + 32) (SUC k * elem_size)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) (SUC k) ss) =
      read_memory (w2n src_addr + 32) (SUC k * elem_size) ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `elem_size = 0`
  >- simp[read_memory_def] >>
  PURE_ONCE_REWRITE_TAC [FUNPOW_SUC] >>
  qabbrev_tac `current = FUNPOW
    (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) k ss` >>
  mp_tac (Q.SPECL [`w2n (dst_addr:bytes32)`, `k`, `n`, `elem_size`]
    abi_static_loop_child_window) >> impl_tac >- (gvs[] >> decide_tac) >> strip_tac >>
  mp_tac (Q.SPECL [`w2n (src_addr:bytes32)`, `k`, `n`, `elem_size`]
    abi_static_loop_child_window) >> impl_tac >- (gvs[] >> decide_tac) >> strip_tac >>
  `mload (w2n counter_addr) current = n2w k` by
    (simp[Abbr`current`, abi_static_loop_effects_counter] >> fs[WORD_ADD_0]) >>
  `read_memory (w2n src_addr + 32) (n * elem_size) current =
    read_memory (w2n src_addr + 32) (n * elem_size) ss` by
    (simp_tac bool_ss [Abbr`current`] >> irule abi_static_loop_source_frame >>
     gvs[] >> decide_tac) >>
  `read_memory (w2n src_addr + 32 + k * elem_size) elem_size current =
    read_memory (w2n src_addr + 32 + k * elem_size) elem_size ss` by
    (mp_tac (Q.SPECL [`src_addr`, `elem_size`, `k`, `n`, `current`, `ss`]
       abi_static_loop_source_element) >> impl_tac >- (gvs[] >> decide_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`info`, `elem_size`, `dst_addr`, `src_addr`, `counter_addr`,
    `labels`, `k`, `current`, `ss`] abi_static_loop_payload_step) >>
  impl_tac >- (gvs[Abbr`current`] >> decide_tac) >> simp[]
QED

Theorem abi_static_loop_effects_payload_prefix:
  !k n info elem_size dst_addr src_addr counter_addr labels ss.
    k <= n /\
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = 0w /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * elem_size <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n dst_addr + 32) ==>
    read_memory (w2n dst_addr + 32) (k * elem_size)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) k ss) =
      read_memory (w2n src_addr + 32) (k * elem_size) ss
Proof
  Induct_on `k` >- simp[read_memory_def] >> rpt gen_tac >> DISCH_TAC >>
  `read_memory (w2n dst_addr + 32) (k * elem_size)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) k ss) =
    read_memory (w2n src_addr + 32) (k * elem_size) ss` by
    (first_x_assum (qspecl_then [`n`, `info`, `elem_size`, `dst_addr`, `src_addr`,
       `counter_addr`, `labels`, `ss`] mp_tac) >>
     impl_tac >- (gvs[] >> decide_tac) >> simp[]) >>
  qpat_x_assum `!n info elem_size dst_addr src_addr counter_addr labels ss. _` kall_tac >>
  mp_tac (Q.SPECL [`k`, `n`, `info`, `elem_size`, `dst_addr`, `src_addr`,
    `counter_addr`, `labels`, `ss`] abi_static_loop_payload_advance) >>
  impl_tac >- (gvs[] >> decide_tac) >> simp[]
QED

Theorem abi_static_loop_effects_payload:
  !n info elem_size dst_addr src_addr counter_addr labels ss.
    ((info = AbiPrimWord /\ elem_size = 32) \/ info = AbiCopy elem_size) /\
    elem_size < dimword(:256) /\ mload (w2n counter_addr) ss = 0w /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= dimword(:256)) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * elem_size <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n src_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n src_addr + 32) /\
    (elem_size = 0 \/ w2n dst_addr + 32 + n * elem_size <= w2n counter_addr \/
      w2n counter_addr + 32 <= w2n dst_addr + 32) ==>
    read_memory (w2n dst_addr + 32) (n * elem_size)
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr elem_size elem_size counter_addr labels) n ss) =
      read_memory (w2n src_addr + 32) (n * elem_size) ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`n`, `n`, `info`, `elem_size`, `dst_addr`, `src_addr`,
    `counter_addr`, `labels`, `ss`] abi_static_loop_effects_payload_prefix) >>
  impl_tac >- (gvs[] >> decide_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop payload theorem: " ^ name)
  end) (DB.thms "abiStaticLoopPayload")

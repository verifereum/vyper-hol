(* TOP-LEVEL: every generated static-array iteration preserves a disjoint
   source window. Natural bounds justify the actual 256-bit child address;
   zero-size elements require no address nonwrapping premise. *)
Theory abiStaticLoopFrame
Ancestors
  abiStaticLoopMemory abiStaticLoopRun abiStaticLoopBody memoryReadProps
  venomState venomExecSemantics words arithmetic

Theorem abi_static_loop_iteration_read_frame:
  !info copied_count dst_addr src_addr mem_sz counter_addr labels ss i n offset read_len.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\ i < n /\
    mload (w2n counter_addr) ss = n2w i /\
    (copied_count = 0 \/ w2n dst_addr + 32 + n * copied_count <= dimword(:256)) /\
    (copied_count = 0 \/ offset + read_len <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * copied_count <= offset) /\
    (offset + read_len <= w2n counter_addr \/ w2n counter_addr + 32 <= offset) ==>
    read_memory offset read_len
      (abi_static_loop_effect info dst_addr src_addr copied_count mem_sz counter_addr labels ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `copied_count = 0`
  >- (irule abi_static_loop_effect_read_frame >> conj_tac >- fs[] >>
      qexists_tac `0` >> fs[]) >>
  mp_tac (Q.SPECL [`w2n (dst_addr:bytes32)`, `i`, `n`, `copied_count`]
    abi_static_loop_child_window) >> impl_tac >- (gvs[] >> decide_tac) >> strip_tac >>
  `w2n (dst_addr + 32w + n2w i * n2w copied_count) =
    w2n dst_addr + 32 + i * copied_count` by
    (irule abi_static_loop_child_address >> gvs[] >> decide_tac) >>
  irule abi_static_loop_effect_read_frame >> conj_tac >- fs[] >>
  qexists_tac `copied_count` >> gvs[] >> decide_tac
QED

Theorem abi_static_loop_effects_read_frame:
  !n info copied_count dst_addr src_addr mem_sz counter_addr labels ss offset read_len.
    ((info = AbiPrimWord /\ copied_count = 32) \/ info = AbiCopy copied_count) /\
    copied_count < dimword(:256) /\ mload (w2n counter_addr) ss = 0w /\
    (copied_count = 0 \/ w2n dst_addr + 32 + n * copied_count <= dimword(:256)) /\
    (copied_count = 0 \/ offset + read_len <= w2n dst_addr + 32 \/
      w2n dst_addr + 32 + n * copied_count <= offset) /\
    (offset + read_len <= w2n counter_addr \/ w2n counter_addr + 32 <= offset) ==>
    read_memory offset read_len
      (FUNPOW (abi_static_loop_effect info dst_addr src_addr copied_count mem_sz counter_addr labels) n ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (FUNPOW_invariant_index |> INST_TYPE [alpha |-> ``:venom_state``] |>
    Q.INST [`P` |-> `\current. read_memory offset read_len current = read_memory offset read_len ss`,
      `R` |-> `\current. ?i. i < n /\ mload (w2n (counter_addr:bytes32)) current = n2w i`,
      `f` |-> `abi_static_loop_effect info dst_addr src_addr copied_count mem_sz counter_addr labels`] |>
    Q.SPECL [`n`, `ss`] |> BETA_RULE) >> impl_tac
  >- (conj_tac >- simp[] >> conj_tac
      >- (qx_gen_tac `i` >> DISCH_TAC >> qexists_tac `i` >>
          fs[abi_static_loop_effects_counter, WORD_ADD_0]) >>
      qx_gen_tac `current` >> strip_tac >>
      rename1 `mload (w2n counter_addr) current = n2w i` >>
      mp_tac (Q.SPECL [`info`, `copied_count`, `dst_addr`, `src_addr`, `mem_sz`,
        `counter_addr`, `labels`, `current`, `i`, `n`, `offset`, `read_len`]
        abi_static_loop_iteration_read_frame) >>
      impl_tac >- (gvs[] >> decide_tac) >> fs[]) >>
  simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop frame theorem: " ^ name)
  end) (DB.thms "abiStaticLoopFrame")

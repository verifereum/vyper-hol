(* TOP-LEVEL: a static field starts immediately after the completed heads.
   Empty payloads impose no pointer-range condition and preserve all reads. *)
Theory abiStaticFieldMemory
Ancestors
  abiFieldBytesPath abiFieldLayoutDefs abiMemoryFrame memoryReadProps
  compileEnv venomState list words arithmetic

Theorem abi_static_field_head_separation:
  !(dst_addr:bytes32) fields byte_count.
    (byte_count = 0 \/ w2n dst_addr + abi_field_head_size fields < dimword(:256)) ==>
    abi_window_separated (w2n dst_addr) (abi_field_head_size fields)
      (w2n (dst_addr + n2w (abi_field_head_size fields))) byte_count
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `byte_count = 0`
  >- simp[abi_window_separated_def] >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> fs[]) >>
  simp[abi_window_separated_def, regions_disjoint_def]
QED

Theorem abi_static_field_read:
  !(dst_addr:bytes32) fields payload (ss:venom_state).
    (LENGTH payload = 0 \/ w2n dst_addr + abi_field_head_size fields < dimword(:256)) /\
    read_memory (w2n (dst_addr + n2w (abi_field_head_size fields))) (LENGTH payload) ss = payload ==>
    read_memory (w2n dst_addr + abi_field_head_size fields) (LENGTH payload) ss = payload
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `payload = []`
  >- simp[read_memory_def] >> fs[] >>
  `w2n (dst_addr + n2w (abi_field_head_size fields)) = w2n dst_addr + abi_field_head_size fields` by
    (irule abi_field_word_address >> decide_tac) >>
  fs[]
QED

(* TOP-LEVEL: every live static iteration writes only the root output and
   index counter. The same two-window frame composes over the runtime fold,
   retaining enough precision to protect the separate parent counter. *)
Theory abiNativeStaticArrayFrame
Ancestors
  abiNativeArrayFrames abiNativeStaticArrayEffects abiNativeStaticArrayBounds abiNativeStaticArrayRun
  abiNativeStaticArrayState abiNativeArrayResources abiNativeEncodingDefs abiMemoryEncoding abiFieldLayoutDefs
  abiMemoryFrameCover abiMemoryFrame abiStaticLoopRun compileEnv venomState list words arithmetic

Theorem abi_native_static_array_step_frame:
  !func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity dst_addr
      info stride fields initial ss index labels.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity index ss /\ index < LENGTH fields ==>
    abi_memory_frame [(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
      abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)] ss
      (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_static_array_data _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_static_array_data_def]) >>
  drule_all abi_native_static_array_element_bounds >> strip_tac >>
  qspecl_then [`info`, `dst_addr`, `root_addr`, `abi_static_encoder_size info`, `stride`, `counter_addr`, `labels`, `ss`]
    mp_tac abi_native_static_effect_frame >> impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`w2n dst_addr`, `LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
    abi_field_bytes (abi_field_head_size fields) fields)`,
    `w2n (dst_addr + 32w + n2w index * n2w (abi_static_encoder_size info))`, `abi_static_encoder_size info`,
    `w2n counter_addr`, `ss`,
    `abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss`]
    mp_tac abi_native_array_write_frame >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

Theorem abi_native_static_array_run_frame:
  !iterations func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity
      dst_addr info stride fields initial ss labels.
    iterations <= LENGTH fields /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity 0 ss ==>
    abi_memory_frame [(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
      abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)] ss
      (FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels)
        iterations ss)
Proof
  Induct_on `iterations` >- simp[] >> rpt gen_tac >> strip_tac >>
  `iterations <= LENGTH fields /\ iterations < LENGTH fields` by decide_tac >>
  first_x_assum drule_all >> disch_then (qspec_then `labels` ASSUME_TAC) >>
  qspecl_then [`iterations`, `func`, `root_cs`, `root_after`, `source_id`, `target_id`, `counter_inst`, `counter_addr`,
    `loop_cs`, `root_addr`, `source_capacity`, `dst_addr`, `info`, `stride`, `fields`, `initial`, `ss`, `labels`]
    mp_tac abi_native_static_array_memory_run >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_static_array_step_frame >> disch_then (qspec_then `labels` ASSUME_TAC) >>
  simp_tac bool_ss [FUNPOW_SUC] >> irule abi_memory_frame_trans_same >>
  qexists_tac `FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels)
    iterations ss` >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed cumulative actual static array write frame: " ^ name)
  end) (DB.thms "abiNativeStaticArrayFrame")

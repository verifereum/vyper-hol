(* TOP-LEVEL: the actual static-loop memory effect preserves raw array
   data and allocation resources for every live runtime iteration count.
   The source stride may differ from the packed encoded element width. *)
Theory abiNativeStaticArrayRun
Ancestors
  abiNativeStaticArrayStep abiNativeStaticArrayState abiNativeArrayResources abiNativeEncodingDefs
  abiMemoryEncoding abiFieldLayoutDefs abiStaticLoopRun compileEnv venomState list words arithmetic

Theorem abi_native_static_array_memory_run:
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
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity iterations
      (FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels)
        iterations ss) /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
      (FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels)
        iterations ss)
Proof
  Induct_on `iterations` >- simp[] >> rpt gen_tac >> strip_tac >>
  `iterations <= LENGTH fields` by decide_tac >>
  first_x_assum drule_all >> disch_then (qspec_then `labels` strip_assume_tac) >>
  `iterations < LENGTH fields` by decide_tac >>
  drule_all abi_native_static_array_step >> disch_then (qspec_then `labels` mp_tac) >>
  simp_tac bool_ss [FUNPOW_SUC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary runtime static array memory fold: " ^ name)
  end) (DB.thms "abiNativeStaticArrayRun")

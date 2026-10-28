(* TOP-LEVEL: append a completed child to an aggregate's existing heads and
   tails. The child's written-window frame preserves all earlier fields. *)
Theory abiFieldCompose
Ancestors
  abiFieldMemory abiFieldLayoutDefs abiMemoryFrame memoryReadProps
  compileEnv venomState list pair words arithmetic

Theorem abi_fields_layout_single:
  !is_dyn payload arena head_offset tail_offset ss.
    abi_fields_layout [(is_dyn,payload)] arena head_offset tail_offset ss <=>
    read_memory (arena + head_offset) (LENGTH (abi_field_head tail_offset is_dyn payload)) ss =
      abi_field_head tail_offset is_dyn payload /\
    read_memory (arena + tail_offset) (LENGTH (abi_field_tail is_dyn payload)) ss =
      abi_field_tail is_dyn payload
Proof
  simp[abi_fields_layout_cons]
QED

Theorem abi_fields_layout_extend:
  !fields is_dyn payload arena head_offset tail_offset writes before after.
    abi_fields_layout fields arena head_offset tail_offset before /\
    abi_memory_frame writes before after /\
    EVERY (\(offset,byte_count). abi_window_separated (arena + head_offset)
      (abi_field_head_size fields) offset byte_count) writes /\
    EVERY (\(offset,byte_count). abi_window_separated (arena + tail_offset)
      (abi_field_tail_size fields) offset byte_count) writes /\
    read_memory (arena + head_offset + abi_field_head_size fields)
      (LENGTH (abi_field_head (tail_offset + abi_field_tail_size fields) is_dyn payload)) after =
      abi_field_head (tail_offset + abi_field_tail_size fields) is_dyn payload /\
    read_memory (arena + tail_offset + abi_field_tail_size fields)
      (LENGTH (abi_field_tail is_dyn payload)) after = abi_field_tail is_dyn payload ==>
    abi_fields_layout (fields ++ [(is_dyn,payload)]) arena head_offset tail_offset after
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_fields_layout_frame >> DISCH_TAC >>
  asm_simp_tac bool_ss [abi_fields_layout_append, abi_fields_layout_single, ADD_ASSOC]
QED

Theorem abi_fields_layout_dynamic_extend:
  !fields payload arena head_offset tail_offset writes before after.
    abi_fields_layout fields arena head_offset tail_offset before /\
    abi_memory_frame writes before after /\
    EVERY (\(offset,byte_count). abi_window_separated (arena + head_offset)
      (abi_field_head_size fields) offset byte_count) writes /\
    EVERY (\(offset,byte_count). abi_window_separated (arena + tail_offset)
      (abi_field_tail_size fields) offset byte_count) writes /\
    mload (arena + head_offset + abi_field_head_size fields) after =
      n2w (tail_offset + abi_field_tail_size fields) /\
    read_memory (arena + tail_offset + abi_field_tail_size fields) (LENGTH payload) after = payload ==>
    abi_fields_layout (fields ++ [(T,payload)]) arena head_offset tail_offset after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fields`, `T`, `payload`, `arena`, `head_offset`, `tail_offset`,
    `writes`, `before`, `after`] abi_fields_layout_extend) >>
  asm_simp_tac (srw_ss()) [abi_field_head_def, abi_field_tail_def, read_memory_word]
QED

Theorem abi_fields_layout_static_extend:
  !fields payload arena head_offset tail_offset writes before after.
    abi_fields_layout fields arena head_offset tail_offset before /\
    abi_memory_frame writes before after /\
    EVERY (\(offset,byte_count). abi_window_separated (arena + head_offset)
      (abi_field_head_size fields) offset byte_count) writes /\
    EVERY (\(offset,byte_count). abi_window_separated (arena + tail_offset)
      (abi_field_tail_size fields) offset byte_count) writes /\
    read_memory (arena + head_offset + abi_field_head_size fields) (LENGTH payload) after = payload ==>
    abi_fields_layout (fields ++ [(F,payload)]) arena head_offset tail_offset after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fields`, `F`, `payload`, `arena`, `head_offset`, `tail_offset`,
    `writes`, `before`, `after`] abi_fields_layout_extend) >>
  fs[abi_field_head_def, abi_field_tail_def, read_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed incremental ABI field memory composition: " ^ name)
  end) (DB.thms "abiFieldCompose")

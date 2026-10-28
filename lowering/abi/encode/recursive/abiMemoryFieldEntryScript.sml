(* TOP-LEVEL: executing the actual field source ADD supplies the complete
   source-memory relation for an arbitrary nested child and remaining fields.
   Helper: an exact cons inversion without runtime or child-call assumptions. *)
Theory abiMemoryFieldEntry
Ancestors
  abiMemoryEncoding abiMemoryEncodingElements abiFieldAddress abiFieldBytesPath
  abiFieldOperands abiComplexCode abiMemoryLeafRun
  compileEnv fragBlockPath venomState list pair words arithmetic

Theorem abi_memory_fields_cons_cases:
  !info abi_sz mem_sz is_dyn rest src span mem payload fields.
    abi_memory_fields ((info,abi_sz,mem_sz,is_dyn)::rest) src span mem ((is_dyn,payload)::fields) <=>
    mem_sz <= span /\ abi_memory_encoding info src mem_sz mem payload /\
    abi_sz = (if is_dyn then 32 else LENGTH payload) /\
    abi_memory_fields rest (src + mem_sz) (span - mem_sz) mem fields
Proof
  simp[Once abi_memory_fields_cases] >> metis_tac[]
QED

Theorem abi_memory_field_entry:
  !ctx func src source_offset cs ss root_addr info abi_sz mem_sz is_dyn rest span payload fields.
    fn_has_code cs (abi_complex_field_cut src source_offset cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand src ss = SOME root_addr /\
    w2n root_addr + source_offset < dimword (:256) /\
    abi_memory_fields ((info,abi_sz,mem_sz,is_dyn)::rest) (w2n root_addr + source_offset)
      span ss.vs_memory ((is_dyn,payload)::fields) ==>
    fragment_path ctx func ss (abi_field_address_state cs source_offset root_addr ss) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0))
      (abi_field_address_state cs source_offset root_addr ss) = SOME (root_addr + n2w source_offset) /\
    abi_memory_encoding info (w2n (root_addr + n2w source_offset)) mem_sz
      (abi_field_address_state cs source_offset root_addr ss).vs_memory payload /\
    abi_memory_fields rest (w2n root_addr + source_offset + mem_sz) (span - mem_sz)
      (abi_field_address_state cs source_offset root_addr ss).vs_memory fields /\
    abi_sz = (if is_dyn then 32 else LENGTH payload) /\ mem_sz <= span
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (root_addr + n2w source_offset) = w2n root_addr + source_offset` by
    (irule abi_field_word_address >> simp[]) >>
  qspecl_then [`ctx`, `func`, `src`, `source_offset`, `cs`, `ss`, `root_addr`]
    mp_tac abi_field_address_path >> impl_tac >- simp[] >> DISCH_TAC >>
  fs[abi_memory_fields_cons_cases, abi_field_address_state_frame, abi_field_address_state_value]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive ABI field source entry: " ^ name)
  end) (DB.thms "abiMemoryFieldEntry")

(* Contained field capacity for actual memory projections. *)
Theory bodyFieldMemory
Ancestors
  exprSimAttributeFields bodyAllocMemory
  valueEncoding compileEnv venomState words list

Theorem body_field_region_frontier:
  fields_layout fields fs /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next ==>
  addr + struct_field_offset fields id + type_memory_size ftv <= s.vs_alloca_next
Proof
  strip_tac >> drule_all struct_field_offset_le >> decide_tac
QED

Theorem body_field_source_region:
  fields_layout fields fs /\ struct_has_type fs vals /\
  fields_in_memory vals fs addr s.vs_memory /\ fields_val_wf vals fs /\
  ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next ==>
  val_in_memory ftv fv (addr + struct_field_offset fields id) s.vs_memory /\
  val_wf ftv fv /\
  addr + struct_field_offset fields id + type_memory_size ftv <= s.vs_alloca_next
Proof
  strip_tac >>
  conj_tac >- (irule fields_in_memory_field >> metis_tac[]) >>
  conj_tac >- (irule fields_val_wf_field >> metis_tac[]) >>
  irule body_field_region_frontier >> metis_tac[]
QED

Theorem body_field_address_no_wrap:
  fields_layout fields fs /\ ALOOKUP fs id = SOME ftv /\
  (addr : num) + type_memory_size_fields fs <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  w2n ((n2w addr : bytes32) + n2w (struct_field_offset fields id)) =
    addr + struct_field_offset fields id
Proof
  strip_tac >> drule_all body_field_region_frontier >> strip_tac >>
  `addr + struct_field_offset fields id < dimword (:256)` by decide_tac >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_FIELD_REGION_MEMORY_AUDIT OK\n"
     else raise Fail "body field region inherited admission"
  end) [body_field_region_frontier, body_field_source_region, body_field_address_no_wrap];

(* Linked frame transport for the reached fixed-byte Keccak suffix. *)
Theory bodyKeccakFixedMods
Ancestors
  bodyFullHashKeccakFixed bodyMethodIdScratchFrameMods
  bodyForRangeScalarFrameMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyInvSplit exprLoweringProps loweringStateRelDefs ptrDiscipline
  compileEnv venomState venomInst bodyPtrDefs words finite_map list pred_set

(* The physical observations are deliberately explicit: they are supplied by
   the concrete three-instruction suffix, while this theorem performs only the
   linked ghost/immutable lift. *)
Theorem keccak_fixed_suffix_mods:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  immutable_frame_mods func ce cx es s /\
  ghost_inv_at D 0 d ce cx es G' tn' z /\
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
                           FLOOKUP G' x = FLOOKUP G x /\
                           FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
  tn'.t_mem SUBSET tn.t_mem /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n) /\ lo <= b /\
  (!a sz. a + sz <= b \/ b + n <= a ==>
      mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory) /\
  compile_keccak256_bytesm value (LENGTH bs) sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK z ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' z /\
  immutable_frame_mods func ce cx es z
Proof
  strip_tac >> drule_all method_id_scratch_frame_mods >> simp[]
QED

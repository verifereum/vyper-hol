(* Execute an ABI encoder using allocation-site ownership. No ghost execution
   of the encoder is asserted by this ordinary-execution boundary. *)
Theory externalReturnRegisteredRun
Ancestors externalReturnAllocPtr abiEncoderWindowRun allocaSiteResource

Theorem registered_window_geometry[local]:
  alloca_inv initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_size) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_cap <= source_size /\ output_cap <= output_size /\ source_id <> output_id ==>
  sb + source_cap <= initial.vs_alloca_next /\
  d + output_cap <= initial.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,source_cap) (d,output_cap)
Proof
  strip_tac >>
  `sb + source_size <= initial.vs_alloca_next` by
    (irule alloca_site_registered_below >> metis_tac[]) >>
  `d + output_size <= initial.vs_alloca_next` by
    (irule alloca_site_registered_below >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (sb,source_size) (d,output_size)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem compile_abi_encode_to_buf_registered_window_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_inv initial /\ alloca_room ctx func initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_size) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_cap <= source_size /\ LENGTH (enc at av) <= output_size /\
  source_id <> output_id /\ source_id NOTIN frag_ids st st' /\
  output_id NOTIN frag_ids st st' /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st st' /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (frag_ids st st')
      [(d,LENGTH (enc at av))] initial actual /\
    alloca_inv actual /\ alloca_room ctx func actual /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  drule_all registered_window_geometry >> strip_tac >>
  irule compile_abi_encode_to_buf_window_run >> asm_rewrite_tac[] >>
  qexistsl_tac [`dst`, `ei`, `sb`, `source_cap`, `src`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `source_id <> inst.inst_id /\ output_id <> inst.inst_id` by metis_tac[] >>
  `sz = 32` by metis_tac[] >> asm_rewrite_tac[] >>
  conj_tac >-
    (irule (cj 3 registered_window_geometry) >>
     qexistsl_tac [`initial`, `inst.inst_id`, `sz`, `source_id`, `source_size`] >> simp[]) >>
  irule (cj 3 registered_window_geometry) >>
  qexistsl_tac [`initial`, `inst.inst_id`, `sz`, `output_id`, `output_size`] >> simp[]
QED

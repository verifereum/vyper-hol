(* Source-free or bounded-source execution at the same framed endpoint. *)
Theory abiEncodeSourceFrontierMemory
Ancestors
  abiEncodeEmptySourceMemory abiEncoderWindowRunMem abiEncoderWindowContract
  abiEncoderWindowPhase abiEncoderWindowMemFrame
  venomState venomExecSemantics compileEnv fragExec words list

Theorem compile_abi_encode_to_buf_source_frontier_mem_frame:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  (cap=0 \/ sb+cap <= s.vs_alloca_next) /\
  d+LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_strong_result ctx func st en out at av d s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  rpt gen_tac >> disch_tac >> Cases_on `cap=0`
  >- (gvs[] >> drule_all compile_abi_encode_to_buf_empty_source_strong_mem_frame >>
      simp_tac bool_ss []) >>
  gvs[] >>
  `abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s` by
    (asm_rewrite_tac[abi_encoder_window_pre_def] >> decide_tac) >>
  drule_all compile_abi_encode_to_buf_window_strong_mem_frame >> simp_tac bool_ss []
QED

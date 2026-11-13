(* Task-owned bytes-copy boundary; explicit frame theorem follows here. *)
Theory externalReturnCopyBoundary
Ancestors
  valueCopy fragExec immutableMemoryFrame context exprLoweringProps
  emitHelperProps loweringPosts venomExecSemantics venomState venomInst
  words list arithmetic vfmConstants

Theorem return_bytestring_copy_extent_explicit:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  mem_word_at (w2n a) s0.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= D ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         (t with <|vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
                   vs_prev_bb := s0.vs_prev_bb;
                   vs_current_bb := s0.vs_current_bb;
                   vs_inst_idx := s0.vs_inst_idx|>) = s0 /\
         (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
         (!p n. p + n <= w2n d \/ w2n d + D <= p ==>
           mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
         LENGTH s0.vs_memory <= LENGTH t.vs_memory) (\r. F)
Proof
  strip_tac >> drule_all store_bytestring_run_exact >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[] >>
  conj_tac
  >- (irule mcopy_val_in_memory >> simp[]) >>
  conj_tac
  >- gvs[venom_state_component_equality] >>
  conj_tac >- gvs[lookup_var_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >>
      decide_tac) >>
  simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF]
QED

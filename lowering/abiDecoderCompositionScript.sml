(* Interface probes only: not a recursive decoder execution theorem. *)
Theory abiDecoderComposition
Ancestors
  abiDecoderContract fragExec abiTupleProps emitHelperProps valueEncodingProps
  venomExecSemantics venomExecProofs venomInst venomState compileEnv emitHelper
  exprLoweringProps words

Definition abi_decode_copy_opcode_def:
  abi_decode_copy_opcode opc =
    if opc = CALLDATALOAD then CALLDATACOPY
    else if opc = DLOAD then DLOADBYTES else MCOPY
End

Definition abi_decode_copy_bytes_def:
  abi_decode_copy_bytes opc p n s =
    TAKE n (DROP p (abi_decode_source opc s) ++ REPLICATE n 0w)
End

(* Snapshot copy: memory overlap is legal for this single operation. Future
   reads require a separate source-disjointness invariant. *)
Theorem abi_decode_copy_step:
  abi_decode_source_opcode opc /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  eval_operand sz_op s = SOME n ==>
  step_inst_base (mk_inst id (abi_decode_copy_opcode opc) [dst;src;sz_op] []) s =
    OK (write_memory_with_expansion (w2n d)
      (abi_decode_copy_bytes opc (w2n p) (w2n n) s) s)
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >>
  simp[abi_decode_copy_opcode_def, abi_decode_copy_bytes_def,
       abi_decode_source_def, Once step_inst_base_def, mk_inst_def, mcopy_def]
QED

Theorem abi_decode_copy_sequence:
  emit_void (abi_decode_copy_opcode opc) [dst;src;sz_op] st = ((),st') /\
  abi_decode_source_opcode opc /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
  eval_operand sz_op s = SOME n ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    mem_bytes_at (w2n d) (w2n n) s'.vs_memory =
      abi_decode_copy_bytes opc (w2n p) (w2n n) s /\
    abi_decode_frame (w2n d) (w2n n) s s' /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op s' = SOME w)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id (abi_decode_copy_opcode opc)
    [dst;src;sz_op] []) s = OK (write_memory_with_expansion (w2n d)
      (abi_decode_copy_bytes opc (w2n p) (w2n n) s) s)` by
    (irule abi_decode_copy_step >> simp[]) >>
  simp[run_inst_seq_def] >>
  `LENGTH (abi_decode_copy_bytes opc (w2n p) (w2n n) s) = w2n n` by
    simp[abi_decode_copy_bytes_def] >>
  conj_tac
  >- metis_tac[write_memory_mem_bytes_at_same] >>
  conj_tac
  >- (simp[abi_decode_frame_def] >> conj_tac
      >- (rpt strip_tac >> irule write_memory_mem_bytes_at_disjoint >>
          simp[] >> decide_tac) >>
      simp[write_memory_with_expansion_def]) >>
  Cases_on `op` >> simp[eval_operand_def, write_memory_with_expansion_def,
                            lookup_var_def]
QED

(* Straight-line prefix -> child -> continuation; the middle fragment may
   finish blocks. Code containment is provided by cs_extends, not guessed
   from freshness of SSA variables. *)
Theorem abi_decode_child_compose:
  frag_exec ctx st0 st1 P A (K F) /\
  frag_exec ctx st1 st2 B C (K F) /\
  frag_exec ctx st2 st3 D Q (K F) /\
  (!s. A s ==> B s) /\ (!s. C s ==> D s) /\
  cs_extends st0 st1 /\ cs_extends st1 st2 /\ cs_extends st2 st3 ==>
  frag_exec ctx st0 st3 P Q (K F)
Proof
  strip_tac >>
  `frag_exec ctx st1 st2 A D (K F)` by
    (irule frag_exec_conseq >> qexistsl_tac [`B`,`C`,`K F`] >> simp[]) >>
  `frag_exec ctx st0 st2 P D (K F)` by
    (irule frag_exec_seq >> qexistsl_tac [`A`,`st1`] >> simp[]) >>
  irule frag_exec_seq >> qexistsl_tac [`D`,`st2`] >> simp[] >>
  metis_tac[cs_extends_trans]
QED

(* A header has no PHIs; entering it selects exactly one successor. *)
Theorem abi_decode_header_step:
  eval_operand cond s = SOME w /\ ~s.vs_halted ==>
  run_block fuel ctx
    <|bb_label := hdr;
      bb_instructions := [mk_inst id JNZ [cond;Label body_lbl;Label done] []]|> s =
    OK (jump_to (if w = 0w then done else body_lbl) s)
Proof
  strip_tac >>
  `eval_operand cond (s with vs_inst_idx := 0) = SOME w` by
    (Cases_on `cond` >> gvs[eval_operand_def, lookup_var_def]) >>
  simp[run_block_def, eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_def,
       Once step_inst_base_def, is_terminator_def, jump_to_def] >>
  Cases_on `w = 0w` >> simp[]
QED

(* Zero iterations: the continuation is arbitrary and is NOT executed by
   this probe. Lookup equalities expose the precise label-containment premise. *)
Theorem abi_decode_zero_iteration:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr;
      bb_instructions := [mk_inst id JNZ [cond;Label body_lbl;Label done] []]|> /\
  hdr <> body_lbl /\ hdr <> done /\ body_lbl <> done /\
  s.vs_current_bb = hdr /\ eval_operand cond s = SOME 0w /\ ~s.vs_halted ==>
  run_blocks (SUC fuel) ctx fn s =
    run_blocks fuel ctx fn (jump_to done s)
Proof
  strip_tac >> drule_all abi_decode_header_step >> strip_tac >>
  simp[Once run_blocks_unfold, jump_to_def]
QED

(* One iteration: the child is proved separately for every fuel. It restores
   the header, clears the test at the bound, and preserves a frame F. This
   tests CFG composition only, not correctness of any particular child. *)
Theorem abi_decode_one_iteration:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr;
      bb_instructions := [mk_inst id JNZ [cond;Label body_lbl;Label done] []]|> /\
  lookup_block body_lbl fn.fn_blocks = SOME child /\
  hdr <> body_lbl /\ hdr <> done /\ body_lbl <> done /\
  s.vs_current_bb = hdr /\ eval_operand cond s = SOME w /\ w <> 0w /\
  ~s.vs_halted /\
  (!f. run_block f ctx child (jump_to body_lbl s) = OK t) /\
  t.vs_current_bb = hdr /\ eval_operand cond t = SOME 0w /\ ~t.vs_halted /\
  frame s t ==>
  run_blocks (SUC (SUC (SUC fuel))) ctx fn s =
    run_blocks fuel ctx fn (jump_to done t) /\
  frame s t
Proof
  strip_tac >> simp[] >>
  qpat_assum `eval_operand cond s = SOME w`
    (mp_then Any mp_tac abi_decode_header_step) >>
  simp[] >> strip_tac >>
  simp[Once run_blocks_unfold] >>
  `~(jump_to body_lbl s).vs_halted /\
   (jump_to body_lbl s).vs_current_bb = body_lbl` by simp[jump_to_def] >>
  simp[Once run_blocks_unfold] >>
  irule abi_decode_zero_iteration >> simp[] >> metis_tac[]
QED

Theorem abi_decode_jump_observations:
  eval_operand op (jump_to lbl t) = eval_operand op t /\
  abi_decode_load opc p (jump_to lbl t) = abi_decode_load opc p t /\
  (abi_decode_frame d n s (jump_to lbl t) <=> abi_decode_frame d n s t)
Proof
  Cases_on `op` >>
  simp[jump_to_def, eval_operand_def, lookup_var_def, abi_decode_load_def,
       abi_decode_source_def, mload_def, abi_decode_frame_def]
QED

(* Concrete next loop-rule obligation (NOT proved here):

   Let H be the header above and let J i s assert:
     i <= count /\ i < dimword(:256) /\ count < dimword(:256) /\
     mload index_slot s = n2w i /\
     mload source_count_slot s = n2w count /\
     initialized_typed_prefix i s /\ untouched_source_suffix i s /\
     protected_operands s /\ output_and_scratch_frame s0 s.

   Header code must first establish cond = bool_to_word (i < count)
   and preserve J. For every i < count and J i s, the child+increment+
   backedge must reach t with J (i+1) t, current_bb = hdr, index = 0,
   and a continuation simulation at any non-Error result (with sufficient
   fuel). Header/body/done lookup equalities, distinct labels, and absence
   of PHIs are explicit premises, as in the probes above.

   Required conclusion: for J 0 s, there exists t with J count t at the
   done block, and every non-Error run_from result at t lifts to a run_from
   result at s with some fuel. Exit predicate is K F.

   Induction measure: count-i; body decreases it because i<count and
   i'=i+1<=count. The memory index increment must additionally be connected
   to this natural increment using the stated nonwrap bound. Child frame
   must protect the count and index slots except for its specified index
   write, preserve all future memory-source bytes, and allow scratch writes.
   A recursive child may finish blocks: use frag_exec with cs_extends and
   continuation simulation, NOT an equality at the same fuel. Our finite
   probes assume fuel-independent run_block behavior only for the isolated
   body; they do not assert this for arbitrary recursive children. *)

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_COMPOSITION_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder composition probe not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderComposition");

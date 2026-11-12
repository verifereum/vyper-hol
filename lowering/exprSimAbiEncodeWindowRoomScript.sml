(* The window encoder runner with its allocation room taken over a
   different function table than the one it executes in.  When the
   function has no INVOKE, running it never consults ctx_functions. *)
Theory exprSimAbiEncodeWindowRoom
Ancestors
  abiEncoderWindowRun abiEncoderWindowContract abiEncoderRegisteredEffect
  abiDecoderLoop exprLoweringProps fragExec compileEnv
  venomState venomInst venomExecSemantics venomMemDefs venomWf
  venomExecProps venomInstProofs contractABI valueEncoding

Theorem exec_block_ctx_no_invoke:
  !fuel ctx ctx' bb s.
    (!i. MEM i bb.bb_instructions ==> i.inst_opcode <> INVOKE) ==>
    exec_block fuel ctx bb s = exec_block fuel ctx' bb s
Proof
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >> gvs[PULL_FORALL] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  gvs[get_instruction_def] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
    metis_tac[listTheory.MEM_EL] >>
  drule step_inst_ctx_irrel >>
  disch_then (qspecl_then [`fuel`, `ctx`, `ctx'`, `s`] SUBST1_TAC) >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem run_blocks_ctx_no_invoke:
  !fuel ctx ctx' fn s.
    (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> INVOKE) ==>
    run_blocks fuel ctx fn s = run_blocks fuel ctx' fn s
Proof
  Induct >> rpt strip_tac >> ONCE_REWRITE_TAC[run_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  `!i. MEM i x.bb_instructions ==> i.inst_opcode <> INVOKE` by
    metis_tac[lookup_block_fn_insts] >>
  `!s. exec_block fuel ctx x s = exec_block fuel ctx' x s` by
    metis_tac[exec_block_ctx_no_invoke] >>
  `!s. run_blocks fuel ctx fn s = run_blocks fuel ctx' fn s` by metis_tac[] >>
  asm_rewrite_tac[]
QED

Theorem run_from_ctx_no_invoke:
  !fuel ctx ctx' fn s.
    (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> INVOKE) ==>
    run_from fuel ctx fn s = run_from fuel ctx' fn s
Proof
  rw[run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  `!i. MEM i x.bb_instructions ==> i.inst_opcode <> INVOKE` by
    metis_tac[lookup_block_fn_insts] >>
  `!s. exec_block fuel ctx x s = exec_block fuel ctx' x s` by
    metis_tac[exec_block_ctx_no_invoke] >>
  `!s. run_blocks fuel ctx fn s = run_blocks fuel ctx' fn s` by
    metis_tac[run_blocks_ctx_no_invoke] >>
  asm_rewrite_tac[]
QED

Theorem abi_decode_sim_ctx_no_invoke:
  !ctx ctx' fn s t.
    (!i. MEM i (fn_insts fn) ==> i.inst_opcode <> INVOKE) /\
    abi_decode_sim ctx fn s t ==> abi_decode_sim ctx' fn s t
Proof
  rw[abi_decode_sim_def] >> metis_tac[run_from_ctx_no_invoke]
QED

Theorem compile_abi_encode_to_buf_window_run_room:
  !dst src ei st out st' ctx fs func initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    (!i. MEM i (fn_insts func) ==> i.inst_opcode <> INVOKE) /\
    alloca_inv initial /\
    alloca_room (ctx with ctx_functions := fs) func initial /\
    sb + source_cap <= initial.vs_alloca_next /\
    d + LENGTH (enc at av) <= initial.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (sb,source_cap) (d,LENGTH (enc at av)) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (sb,source_cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,LENGTH (enc at av))] initial actual /\
      alloca_inv actual /\
      alloca_room (ctx with ctx_functions := fs) func actual /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
             lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\
      actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  rpt strip_tac >>
  drule compile_abi_encode_to_buf_window_run >>
  rpt (disch_then drule) >>
  strip_tac >> qexists_tac `actual` >> asm_rewrite_tac[] >>
  metis_tac[abi_decode_sim_ctx_no_invoke]
QED

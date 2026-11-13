(* Compiler slices for the dynamic memory-to-storage traversal. *)
Theory placeStorageLayoutCounted
Ancestors
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  typedArrayControlCounted bodyMemAssignTopCopyPaths fragExecMem fragGasPathMem
  bodyLiteralBufferMemory
  instMemFrontier venomExecSemantics venomExecProofs venomInst venomState
  fragGasMode valueEncodingProps fragExec words arithmetic list rich_list

Theorem dyn_storage_word_layout:
  compile_dynarray_to_storage src dst 1 em tr sa = ((),sb) ==>
  sb.cs_next_var = sa.cs_next_var + 11 /\
  sb.cs_next_id = sa.cs_next_id + 17 /\
  sb.cs_next_label = sa.cs_next_label + 3 /\
  LENGTH sb.cs_blocks = LENGTH sa.cs_blocks + 3 /\
  sb.cs_current_bb = fresh_label_output "dyn_exit" (sa.cs_next_label + 2) /\
  sb.cs_current_insts =
    [mk_inst (sa.cs_next_id + 16) (if tr then TSTORE else SSTORE)
      [dst; Var ("%" ++ toString sa.cs_next_var)] []]
Proof
  Cases_on `tr` >> simp[compile_dynarray_to_storage_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_label_def, fresh_var_def, fresh_id_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def] >>
  strip_tac >> gvs[]
QED

Theorem dyn_storage_word_blocks:
  compile_dynarray_to_storage src dst 1 em tr sa = ((),sb) ==>
  sb.cs_blocks =
    <| bb_label := fresh_label_output "dyn_body" (sa.cs_next_label + 1);
       bb_instructions :=
       [mk_inst (sa.cs_next_id + 6) MUL
          [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit 32w]
          ["%" ++ toString (sa.cs_next_var + 4)];
        mk_inst (sa.cs_next_id + 7) ADD
          [Lit 32w; Var ("%" ++ toString (sa.cs_next_var + 4))]
          ["%" ++ toString (sa.cs_next_var + 5)];
        mk_inst (sa.cs_next_id + 8) ADD
          [src; Var ("%" ++ toString (sa.cs_next_var + 5))]
          ["%" ++ toString (sa.cs_next_var + 6)];
        mk_inst (sa.cs_next_id + 9) MLOAD
          [Var ("%" ++ toString (sa.cs_next_var + 6))]
          ["%" ++ toString (sa.cs_next_var + 7)];
        mk_inst (sa.cs_next_id + 10) ADD
          [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit 1w]
          ["%" ++ toString (sa.cs_next_var + 8)];
        mk_inst (sa.cs_next_id + 11) ADD
          [dst; Var ("%" ++ toString (sa.cs_next_var + 8))]
          ["%" ++ toString (sa.cs_next_var + 9)];
        mk_inst (sa.cs_next_id + 12) (if tr then TSTORE else SSTORE)
          [Var ("%" ++ toString (sa.cs_next_var + 9));
           Var ("%" ++ toString (sa.cs_next_var + 7))] [];
        mk_inst (sa.cs_next_id + 13) ADD
          [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit 1w]
          ["%" ++ toString (sa.cs_next_var + 10)];
        mk_inst (sa.cs_next_id + 14) ASSIGN
          [Var ("%" ++ toString (sa.cs_next_var + 10))]
          ["%" ++ toString (sa.cs_next_var + 1)];
        mk_inst (sa.cs_next_id + 15) JMP
          [Label (fresh_label_output "dyn_cond" sa.cs_next_label)] []] |> ::
    <| bb_label := fresh_label_output "dyn_cond" sa.cs_next_label;
       bb_instructions :=
       [mk_inst (sa.cs_next_id + 3) LT
          [Var ("%" ++ toString (sa.cs_next_var + 1));
           Var ("%" ++ toString sa.cs_next_var)]
          ["%" ++ toString (sa.cs_next_var + 2)];
        mk_inst (sa.cs_next_id + 4) ISZERO
          [Var ("%" ++ toString (sa.cs_next_var + 2))]
          ["%" ++ toString (sa.cs_next_var + 3)];
        mk_inst (sa.cs_next_id + 5) JNZ
          [Var ("%" ++ toString (sa.cs_next_var + 3));
           Label (fresh_label_output "dyn_exit" (sa.cs_next_label + 2));
           Label (fresh_label_output "dyn_body" (sa.cs_next_label + 1))] []] |> ::
    <| bb_label := sa.cs_current_bb;
       bb_instructions := sa.cs_current_insts ++
       [mk_inst sa.cs_next_id MLOAD [src] ["%" ++ toString sa.cs_next_var];
        mk_inst (sa.cs_next_id + 1) ASSIGN [Lit 0w]
          ["%" ++ toString (sa.cs_next_var + 1)];
        mk_inst (sa.cs_next_id + 2) JMP
          [Label (fresh_label_output "dyn_cond" sa.cs_next_label)] []] |> ::
    sa.cs_blocks
Proof
  Cases_on `tr` >> simp[compile_dynarray_to_storage_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_label_def, fresh_var_def,
    fresh_id_def, emit_op_def, emit_void_def, emit_inst_def, emit_def,
    new_block_def] >> strip_tac >> gvs[]
QED

Theorem dyn_storage_multi_split:
  ew <> 1 /\
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) ==>
  ?sc sd lbl.
    sc.cs_next_var = sa.cs_next_var + 10 /\
    sc.cs_next_id = sa.cs_next_id + 12 /\
    sc.cs_next_label = sa.cs_next_label + 3 /\
    sc.cs_current_bb = fresh_label_output "dyn_body" (sa.cs_next_label + 1) /\
    sc.cs_current_insts =
      [mk_inst (sa.cs_next_id + 6) MUL
         [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit (n2w em)]
         ["%" ++ toString (sa.cs_next_var + 4)];
       mk_inst (sa.cs_next_id + 7) ADD
         [Lit 32w; Var ("%" ++ toString (sa.cs_next_var + 4))]
         ["%" ++ toString (sa.cs_next_var + 5)];
       mk_inst (sa.cs_next_id + 8) ADD
         [src; Var ("%" ++ toString (sa.cs_next_var + 5))]
         ["%" ++ toString (sa.cs_next_var + 6)];
       mk_inst (sa.cs_next_id + 9) MUL
         [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit (n2w ew)]
         ["%" ++ toString (sa.cs_next_var + 7)];
       mk_inst (sa.cs_next_id + 10) ADD
         [Lit 1w; Var ("%" ++ toString (sa.cs_next_var + 7))]
         ["%" ++ toString (sa.cs_next_var + 8)];
       mk_inst (sa.cs_next_id + 11) ADD
         [dst; Var ("%" ++ toString (sa.cs_next_var + 8))]
         ["%" ++ toString (sa.cs_next_var + 9)]] /\
    sc.cs_blocks =
      <| bb_label := fresh_label_output "dyn_cond" sa.cs_next_label;
         bb_instructions :=
         [mk_inst (sa.cs_next_id + 3) LT
            [Var ("%" ++ toString (sa.cs_next_var + 1));
             Var ("%" ++ toString sa.cs_next_var)]
            ["%" ++ toString (sa.cs_next_var + 2)];
          mk_inst (sa.cs_next_id + 4) ISZERO
            [Var ("%" ++ toString (sa.cs_next_var + 2))]
            ["%" ++ toString (sa.cs_next_var + 3)];
          mk_inst (sa.cs_next_id + 5) JNZ
            [Var ("%" ++ toString (sa.cs_next_var + 3));
             Label (fresh_label_output "dyn_exit" (sa.cs_next_label + 2));
             Label (fresh_label_output "dyn_body" (sa.cs_next_label + 1))] []] |> ::
      <| bb_label := sa.cs_current_bb;
         bb_instructions := sa.cs_current_insts ++
         [mk_inst sa.cs_next_id MLOAD [src] ["%" ++ toString sa.cs_next_var];
          mk_inst (sa.cs_next_id + 1) ASSIGN [Lit 0w]
            ["%" ++ toString (sa.cs_next_var + 1)];
          mk_inst (sa.cs_next_id + 2) JMP
            [Label (fresh_label_output "dyn_cond" sa.cs_next_label)] []] |> ::
      sa.cs_blocks /\
    compile_word_copy_loop
      (Var ("%" ++ toString (sa.cs_next_var + 6)))
      (Var ("%" ++ toString (sa.cs_next_var + 9))) ew LocMemory
      (if tr then LocTransient else LocStorage) F sc = (lbl,sd) /\
    (do nc <- emit_op ADD
          [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit 1w];
        emit_inst ASSIGN [nc] ["%" ++ toString (sa.cs_next_var + 1)];
        emit_inst JMP [Label (fresh_label_output "dyn_cond" sa.cs_next_label)] [];
        new_block (fresh_label_output "dyn_exit" (sa.cs_next_label + 2));
        emit_void (if tr then TSTORE else SSTORE)
          [dst; Var ("%" ++ toString sa.cs_next_var)]
     od) sd = ((),sb)
Proof
  Cases_on `tr` >> strip_tac >>
  gvs[compile_dynarray_to_storage_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_label_def, fresh_var_def,
    fresh_id_def, emit_op_def, emit_void_def, emit_inst_def, emit_def,
    new_block_def] >>
  qmatch_asmsub_abbrev_tac `compile_word_copy_loop _ _ _ _ _ _ sc` >>
  pairarg_tac >> gvs[] >> qexists_tac `sc` >>
  simp[Abbr `sc`]
QED

Theorem dyn_storage_entry_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++
    [mk_inst id MLOAD [src] [len];
     mk_inst (id+1) ASSIGN [Lit 0w] [ctr];
     mk_inst (id+2) JMP [Label hdr] []] /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to hdr ((update_var ctr 0w
      (update_var len (mload (w2n p) s) s))
        with vs_inst_idx := LENGTH prefix + 2)))
Proof
  strip_tac >>
  qabbrev_tac `q = update_var ctr 0w (update_var len (mload (w2n p) s) s)` >>
  `~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `q`, update_var_def] >>
  `gas_marked_path T ctx fn s 0
    (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH
      [mk_inst id MLOAD [src] [len];
       mk_inst (id+1) ASSIGN [Lit 0w] [ctr]]))` by
    (irule topcopy_seq_path >> simp[] >>
     simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, mk_inst_def,
       is_terminator_def, run_inst_seq_mem_ok_def, below_frontier_MLOAD,
       below_frontier_no_ranges, run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_read1_def, exec_pure1_def, eval_operands_def, eval_operand_def,
       Abbr `q`, update_var_def]) >>
  `gas_marked_path T ctx fn (q with vs_inst_idx := LENGTH prefix + 2) 0
    (OK (jump_to hdr (q with vs_inst_idx := LENGTH prefix + 2)))` by
    (irule topcopy_jump_path >> simp[] >>
     qexists_tac `mk_inst (id+2) JMP [Label hdr] []` >>
     simp[get_instruction_def, EL_APPEND2, mk_inst_def,
       step_inst_base_opcode_eqs]) >>
  gvs[gas_marked_path_def] >> drule_all gas_path_mem_then >> simp[Abbr `q`]
QED

Theorem dyn_storage_length_store_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if tr then TSTORE else SSTORE) [dst; len] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  eval_operand dst s = SOME d /\ eval_operand len s = SOME n ==>
  gas_path_mem ctx fn s 0
    (OK ((if tr then tstore d n s else sstore d n s)
      with vs_inst_idx := s.vs_inst_idx + 1))
Proof
  strip_tac >>
  `gas_marked_path T ctx fn s 0
    (OK ((if tr then tstore d n s else sstore d n s)
      with vs_inst_idx := s.vs_inst_idx + LENGTH
        [mk_inst id (if tr then TSTORE else SSTORE) [dst; len] []]))` by
    (irule topcopy_seq_path >> Cases_on `tr` >>
     gvs[mk_inst_def, is_terminator_def, run_inst_seq_mem_ok_def,
       below_frontier_no_ranges, run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_write2_def, eval_operands_def, eval_operand_def]) >>
  gvs[gas_marked_path_def]
QED

Theorem dyn_storage_multi_addresses_path:
  code =
    [mk_inst id MUL [Var ctr; Lit (n2w em)] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MUL [Var ctr; Lit (n2w ew)] [dm];
     mk_inst (id+4) ADD [Lit 1w; Var dm] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp]] /\
  ALL_DISTINCT [ctr; mv; so; sp; dm; off; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [mv; so; sp; dm; off; dp]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var ctr s = SOME i /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
    lookup_var sp q = SOME (p + (32w + i * n2w em)) /\
    lookup_var dp q = SOME (d + (1w + i * n2w ew)) /\
    (q with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. ~MEM x [mv; so; sp; dm; off; dp] ==>
       lookup_var x q = lookup_var x s) /\
    q.vs_inst_idx = s.vs_inst_idx + 6
Proof
  strip_tac >>
  qabbrev_tac `u = update_var dp (d + (1w + i * n2w ew))
    (update_var off (1w + i * n2w ew) (update_var dm (i * n2w ew)
      (update_var sp (p + (32w + i * n2w em))
        (update_var so (32w + i * n2w em) (update_var mv (i * n2w em) s)))))` >>
  `run_inst_seq code s = OK u` by
    (Cases_on `src` >> Cases_on `dst` >> gvs[ALL_DISTINCT, MEM, eval_operand_def] >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operands_def, eval_operand_update_var_mstore,
       eval_operand_def, lookup_var_update_var, Abbr `u`]) >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[mk_inst_def, below_frontier_no_ranges]) >>
  `gas_marked_path T ctx fn s 0
    (OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule topcopy_seq_path >> gvs[mk_inst_def, is_terminator_def]) >>
  qexists_tac `u with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  gvs[gas_marked_path_def, Abbr `u`, ALL_DISTINCT, MEM,
    lookup_var_update_var, update_var_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED


Theorem dyn_storage_source_stage[local]:
  ALL_DISTINCT [ctr; mv; so; sp] /\
  (!x. src = Var x ==> ~MEM x [mv; so; sp]) /\
  eval_operand src s = SOME p /\ lookup_var ctr s = SOME i ==>
  ?q. run_inst_seq
      [mk_inst id MUL [Var ctr; Lit 32w] [mv];
       mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
       mk_inst (id+2) ADD [src; Var so] [sp]] s = OK q /\
    run_inst_seq_mem_ok
      [mk_inst id MUL [Var ctr; Lit 32w] [mv];
       mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
       mk_inst (id+2) ADD [src; Var so] [sp]] s /\
    lookup_var sp q = SOME (p + (32w + i * 32w)) /\
    (q with vs_vars := s.vs_vars) = s /\
    (!op. (!x. op = Var x ==> ~MEM x [mv; so; sp]) ==>
       eval_operand op q = eval_operand op s)
Proof
  strip_tac >>
  qexists_tac `update_var sp (p + (32w + i * 32w))
    (update_var so (32w + i * 32w) (update_var mv (i * 32w) s))` >>
  conj_tac
  >- (Cases_on `src` >> gvs[ALL_DISTINCT, MEM, eval_operand_def] >>
      simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
        exec_pure2_def, eval_operands_def, eval_operand_def, lookup_var_update_var]) >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      simp[mk_inst_def, below_frontier_no_ranges]) >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases >> simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem dyn_storage_destination_stage[local]:
  ALL_DISTINCT [ctr; off; dp] /\
  (!x. dst = Var x ==> ~MEM x [off; dp]) /\
  eval_operand dst s = SOME d /\ lookup_var ctr s = SOME i ==>
  ?q. run_inst_seq
      [mk_inst id ADD [Var ctr; Lit 1w] [off];
       mk_inst (id+1) ADD [dst; Var off] [dp]] s = OK q /\
    run_inst_seq_mem_ok
      [mk_inst id ADD [Var ctr; Lit 1w] [off];
       mk_inst (id+1) ADD [dst; Var off] [dp]] s /\
    lookup_var dp q = SOME (d + (i + 1w)) /\
    (q with vs_vars := s.vs_vars) = s /\
    (!op. (!x. op = Var x ==> ~MEM x [off; dp]) ==>
       eval_operand op q = eval_operand op s)
Proof
  strip_tac >>
  qexists_tac `update_var dp (d + (i + 1w)) (update_var off (i + 1w) s)` >>
  conj_tac
  >- (Cases_on `dst` >> gvs[ALL_DISTINCT, MEM, eval_operand_def] >>
      simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
        exec_pure2_def, eval_operands_def, eval_operand_def, lookup_var_update_var]) >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      simp[mk_inst_def, below_frontier_no_ranges]) >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases >> simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem dyn_storage_load_stage[local]:
  eval_operand op s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq [mk_inst id MLOAD [op] [v]] s =
    OK (update_var v (mload (w2n p) s) s) /\
  run_inst_seq_mem_ok [mk_inst id MLOAD [op] [v]] s
Proof
  strip_tac >> conj_tac
  >- (`step_inst_base (mk_inst id MLOAD [op] [v]) s =
         OK (update_var v (mload (w2n p) s) s)` by
        (irule step_MLOAD >> simp[]) >> simp[run_inst_seq_def]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]
QED

Theorem dyn_storage_store_stage[local]:
  eval_operand dst s = SOME d /\ lookup_var ctr s = SOME i /\
  lookup_var v s = SOME w /\ ~s.vs_call_ctx.cc_static /\
  ALL_DISTINCT [ctr; v; off; dp] /\
  (!x. dst = Var x ==> ~MEM x [off; dp]) ==>
  ?q. run_inst_seq
      ([mk_inst id ADD [Var ctr; Lit 1w] [off];
        mk_inst (id+1) ADD [dst; Var off] [dp]] ++
       [mk_inst (id+2) (if tr then TSTORE else SSTORE) [Var dp; Var v] []]) s = OK q /\
    run_inst_seq_mem_ok
      ([mk_inst id ADD [Var ctr; Lit 1w] [off];
        mk_inst (id+1) ADD [dst; Var off] [dp]] ++
       [mk_inst (id+2) (if tr then TSTORE else SSTORE) [Var dp; Var v] []]) s /\
    (q with vs_vars := s.vs_vars) =
      (if tr then tstore (d + (i + 1w)) w s else sstore (d + (i + 1w)) w s) /\
    (!op. (!x. op = Var x ==> ~MEM x [off; dp]) ==>
       eval_operand op q = eval_operand op s)
Proof
  strip_tac >>
  `ALL_DISTINCT [ctr; off; dp]` by fs[ALL_DISTINCT, MEM] >>
  drule_all dyn_storage_destination_stage >>
  disch_then (qspec_then `id` (qx_choose_then `a` strip_assume_tac)) >>
  `lookup_var v a = SOME w` by
    (first_x_assum (qspec_then `Var v` mp_tac) >>
     simp[eval_operand_def] >> fs[ALL_DISTINCT, MEM]) >>
  `~a.vs_call_ctx.cc_static` by fs[venom_state_component_equality] >>
  `run_inst_seq [mk_inst (id+2) (if tr then TSTORE else SSTORE)
      [Var dp; Var v] []] a =
    OK (if tr then tstore (d + (i + 1w)) w a else sstore (d + (i + 1w)) w a)` by
    (Cases_on `tr` >> simp[run_inst_seq_def, step_inst_base_opcode_eqs,
       mk_inst_def, exec_write2_def, eval_operands_def, eval_operand_def]) >>
  `run_inst_seq_mem_ok [mk_inst (id+2) (if tr then TSTORE else SSTORE)
      [Var dp; Var v] []] a` by
    (irule run_inst_seq_mem_ok_every >> Cases_on `tr` >>
     simp[mk_inst_def, below_frontier_no_ranges]) >>
  drule_all run_inst_seq_mem_ok_append_run >> disch_tac >>
  qpat_assum `run_inst_seq [_; _] s = OK a`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst (id+2) (if tr then TSTORE else SSTORE)
    [Var dp; Var v] []]` assume_tac) >>
  qexists_tac `if tr then tstore (d + (i + 1w)) w a else sstore (d + (i + 1w)) w a` >>
  simp[] >> conj_tac
  >- (Cases_on `tr` >> fs[venom_state_component_equality, tstore_def, sstore_def]) >>
  gen_tac >> strip_tac >>
  `eval_operand op a = eval_operand op s` by
    (first_x_assum irule >> fs[MEM]) >>
  Cases_on `tr` >> Cases_on `op` >>
  gvs[eval_operand_def, tstore_def, sstore_def, lookup_var_def]
QED

Theorem dyn_storage_read_stage[local]:
  ALL_DISTINCT [ctr; mv; so; sp; v] /\
  (!x. src = Var x ==> ~MEM x [mv; so; sp]) /\
  eval_operand src s = SOME p /\ lookup_var ctr s = SOME i /\
  w2n (p + (32w + i * 32w)) + 32 <= s.vs_alloca_next ==>
  ?q. run_inst_seq
      ([mk_inst id MUL [Var ctr; Lit 32w] [mv];
        mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
        mk_inst (id+2) ADD [src; Var so] [sp]] ++
       [mk_inst (id+3) MLOAD [Var sp] [v]]) s = OK q /\
    run_inst_seq_mem_ok
      ([mk_inst id MUL [Var ctr; Lit 32w] [mv];
        mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
        mk_inst (id+2) ADD [src; Var so] [sp]] ++
       [mk_inst (id+3) MLOAD [Var sp] [v]]) s /\
    lookup_var v q = SOME (mload (w2n (p + (32w + i * 32w))) s) /\
    (q with vs_vars := s.vs_vars) = s /\
    (!op. (!x. op = Var x ==> ~MEM x [mv; so; sp; v]) ==>
       eval_operand op q = eval_operand op s)
Proof
  strip_tac >>
  `ALL_DISTINCT [ctr; mv; so; sp]` by fs[ALL_DISTINCT, MEM] >>
  drule_all dyn_storage_source_stage >>
  disch_then (qspec_then `id` (qx_choose_then `a` strip_assume_tac)) >>
  `eval_operand (Var sp) a = SOME (p + (32w + i * 32w))` by
    simp[eval_operand_def] >>
  `w2n (p + (32w + i * 32w)) + 32 <= a.vs_alloca_next` by
    fs[venom_state_component_equality] >>
  drule_all dyn_storage_load_stage >>
  disch_then (qspecl_then [`v`, `id+3`] strip_assume_tac) >>
  drule_all run_inst_seq_mem_ok_append_run >> disch_tac >>
  qpat_assum `run_inst_seq [_; _; _] s = OK a`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[mk_inst (id+3) MLOAD [Var sp] [v]]` assume_tac) >>
  qexists_tac `update_var v (mload (w2n (p + (32w + i * 32w))) a) a` >>
  simp[] >> conj_tac
  >- fs[mload_def, update_var_def, lookup_var_update_var,
        venom_state_component_equality] >>
  conj_tac
  >- fs[update_var_def, venom_state_component_equality] >>
  gen_tac >> strip_tac >>
  `eval_operand op a = eval_operand op s` by
    (first_x_assum irule >> fs[MEM]) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_update_var, MEM]
QED

Theorem dyn_storage_word_body_run[local]:
  code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MLOAD [Var sp] [v];
     mk_inst (id+4) ADD [Var ctr; Lit 1w] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp];
     mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dp; Var v] []] /\
  ALL_DISTINCT [ctr; mv; so; sp; v; off; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [mv; so; sp; v; off; dp]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var ctr s = SOME i /\ ~s.vs_call_ctx.cc_static /\
  w2n (p + (32w + i * 32w)) + 32 <= s.vs_alloca_next ==>
  ?q. run_inst_seq code s = OK q /\ run_inst_seq_mem_ok code s /\
    (q with vs_vars := s.vs_vars) =
      (if tr then tstore (d + (i + 1w))
         (mload (w2n (p + (32w + i * 32w))) s) s
       else sstore (d + (i + 1w))
         (mload (w2n (p + (32w + i * 32w))) s) s) /\
    (!op. (!x. op = Var x ==> ~MEM x [mv; so; sp; v; off; dp]) ==>
       eval_operand op q = eval_operand op s)
Proof
  strip_tac >>
  `ALL_DISTINCT [ctr; mv; so; sp; v]` by fs[ALL_DISTINCT, MEM] >>
  `!x. src = Var x ==> ~MEM x [mv; so; sp]` by fs[MEM] >>
  drule_all dyn_storage_read_stage >>
  disch_then (qspec_then `id` (qx_choose_then `a` strip_assume_tac)) >>
  `eval_operand dst a = SOME d` by
    (first_x_assum (qspec_then `dst` mp_tac) >> simp[] >> fs[MEM]) >>
  `lookup_var ctr a = SOME i` by
    (first_x_assum (qspec_then `Var ctr` mp_tac) >>
     simp[eval_operand_def] >> fs[ALL_DISTINCT, MEM]) >>
  `~a.vs_call_ctx.cc_static` by fs[venom_state_component_equality] >>
  `ALL_DISTINCT [ctr; v; off; dp]` by fs[ALL_DISTINCT, MEM] >>
  `!x. dst = Var x ==> ~MEM x [off; dp]` by fs[MEM] >>
  drule_all dyn_storage_store_stage >>
  disch_then (qspecl_then [`tr`, `id+4`] (qx_choose_then `q` strip_assume_tac)) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq tail a = OK q` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq front s = OK a` >>
  drule_all run_inst_seq_mem_ok_append_run >> disch_tac >>
  qpat_assum `run_inst_seq front s = OK a`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `tail` assume_tac) >>
  `code = front ++ tail` by simp[Abbr `front`, Abbr `tail`] >>
  qexists_tac `q` >> simp[] >> Cases_on `tr` >>
  fs[venom_state_component_equality, tstore_def, sstore_def]
QED

Theorem dyn_storage_word_body_path:
  code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w; Var mv] [so];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) MLOAD [Var sp] [v];
     mk_inst (id+4) ADD [Var ctr; Lit 1w] [off];
     mk_inst (id+5) ADD [dst; Var off] [dp];
     mk_inst (id+6) (if tr then TSTORE else SSTORE) [Var dp; Var v] []] /\
  ALL_DISTINCT [ctr; mv; so; sp; v; off; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [mv; so; sp; v; off; dp]) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var ctr s = SOME i /\ ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  w2n (p + (32w + i * 32w)) + 32 <= s.vs_alloca_next /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?q. gas_path_mem ctx fn s 0 (OK q) /\
    (q with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
      (if tr then tstore (d + (i + 1w))
         (mload (w2n (p + (32w + i * 32w))) s) s
       else sstore (d + (i + 1w))
         (mload (w2n (p + (32w + i * 32w))) s) s) /\
    (!x. ~MEM x [mv; so; sp; v; off; dp] ==>
       lookup_var x q = lookup_var x s) /\
    q.vs_memory = s.vs_memory /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_inst_idx = s.vs_inst_idx + 7
Proof
  strip_tac >> drule_all dyn_storage_word_body_run >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `LENGTH code = 7` by simp[] >>
  `gas_marked_path T ctx fn s 0
    (OK (q with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule topcopy_seq_path >> Cases_on `tr` >>
     gvs[mk_inst_def, is_terminator_def]) >>
  qexists_tac `q with vs_inst_idx := s.vs_inst_idx + LENGTH code` >>
  gvs[gas_marked_path_def] >>
  conj_tac
  >- (Cases_on `tr` >>
      fs[venom_state_component_equality, tstore_def, sstore_def]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      first_x_assum (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def, lookup_var_def]) >>
  Cases_on `tr` >>
  fs[venom_state_component_equality, tstore_def, sstore_def]
QED

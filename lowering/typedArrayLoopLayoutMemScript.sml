(* Layout of the concrete fixed-array widening loop. *)
Theory typedArrayLoopLayoutMem
Ancestors
  typedArrayLoopControlMem typedBytesArrayMem context compileEnv loweringStateRelDefs emitHelper
  exprLoweringProps emitHelperProps fragExec words arithmetic list rich_list vfmConstants
  venomExecSemantics venomExecProofs venomInst venomState fragExecMem instMemFrontier

Theorem typed_bytes_array_loop_counters:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) ==>
  sb.cs_next_var = sa.cs_next_var + 13 /\
  sb.cs_next_id = sa.cs_next_id + 18 /\
  sb.cs_next_label = sa.cs_next_label + 3 /\
  LENGTH sb.cs_blocks = LENGTH sa.cs_blocks + 3 /\
  sb.cs_current_bb = fresh_label_output "typed_sa_exit" (sa.cs_next_label + 2) /\
  sb.cs_current_insts = []
Proof
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_abi_dynamic_def, word_size_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def,
       compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def] >>
  strip_tac >> gvs[]
QED

Theorem typed_bytes_array_loop_blocks:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) ==>
  let hdr = fresh_label_output "typed_sa_cond" sa.cs_next_label;
      body_lbl = fresh_label_output "typed_sa_body" (sa.cs_next_label + 1);
      exit_lbl = fresh_label_output "typed_sa_exit" (sa.cs_next_label + 2);
      ctr = "%" ++ toString sa.cs_next_var;
      cmp = "%" ++ toString (sa.cs_next_var + 1);
      done = "%" ++ toString (sa.cs_next_var + 2);
      so = "%" ++ toString (sa.cs_next_var + 3);
      dso = "%" ++ toString (sa.cs_next_var + 4);
      sp = "%" ++ toString (sa.cs_next_var + 5);
      dp = "%" ++ toString (sa.cs_next_var + 6);
      nv = "%" ++ toString (sa.cs_next_var + 12)
  in ?body_code.
    sb.cs_blocks =
      <|bb_label := body_lbl; bb_instructions := body_code|> ::
      <|bb_label := hdr; bb_instructions :=
        typed_sa_header_insts (sa.cs_next_id + 2) ctr cmp done ncount body_lbl exit_lbl|> ::
      <|bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
        [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
         mk_inst (sa.cs_next_id + 1) JMP [Label hdr] []]|> :: sa.cs_blocks /\
    isPREFIX
      [mk_inst (sa.cs_next_id + 5) MUL [Var ctr; Lit 64w] [so];
       mk_inst (sa.cs_next_id + 6) MUL [Var ctr; Lit 96w] [dso];
       mk_inst (sa.cs_next_id + 7) ADD [src; Var so] [sp];
       mk_inst (sa.cs_next_id + 8) ADD [dst; Var dso] [dp]] body_code /\
    DROP 10 body_code = typed_sa_backedge_insts (sa.cs_next_id + 15) ctr nv hdr /\
    LENGTH body_code = 13
Proof
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_abi_dynamic_def, word_size_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def,
       compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def] >>
  strip_tac >> gvs[typed_sa_header_insts_def, typed_sa_backedge_insts_def]
QED

Theorem typed_bytes_array_loop_code:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  let hdr = fresh_label_output "typed_sa_cond" sa.cs_next_label;
      body_lbl = fresh_label_output "typed_sa_body" (sa.cs_next_label + 1);
      exit_lbl = fresh_label_output "typed_sa_exit" (sa.cs_next_label + 2);
      ctr = "%" ++ toString sa.cs_next_var;
      cmp = "%" ++ toString (sa.cs_next_var + 1);
      done = "%" ++ toString (sa.cs_next_var + 2)
  in lookup_block hdr fn.fn_blocks = SOME
       <|bb_label := hdr; bb_instructions :=
         typed_sa_header_insts (sa.cs_next_id + 2) ctr cmp done ncount body_lbl exit_lbl|> /\
     lookup_block sa.cs_current_bb fn.fn_blocks = SOME
       <|bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
         [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
          mk_inst (sa.cs_next_id + 1) JMP [Label hdr] []]|> /\
     ?body_bb. lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
       phi_prefix_length body_bb.bb_instructions = 0 /\
       DROP 10 body_bb.bb_instructions =
         typed_sa_backedge_insts (sa.cs_next_id + 15) ctr
           ("%" ++ toString (sa.cs_next_var + 12)) hdr /\
       LENGTH body_bb.bb_instructions = 13
Proof
  strip_tac >> drule typed_bytes_array_loop_blocks >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `isPREFIX _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [IS_PREFIX_APPEND]) >>
  drule typed_bytes_array_loop_counters >> strip_tac >>
  fs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem typed_sa_pointer_run:
  ALL_DISTINCT [so; dso; sp; dp] /\ ~MEM ctr [so; dso; sp; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so; dso; sp; dp]) /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w dest_base) /\
  eval_operand (Var ctr) s = SOME (n2w i) ==>
  let code =
    [mk_inst id MUL [Var ctr; Lit (n2w src_stride)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w dst_stride)] [dso];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var dso] [dp]]
  in run_inst_seq_mem_ok code s /\
     ?q. run_inst_seq code s = OK q /\
       eval_operand (Var sp) q = SOME (n2w (source_base + src_stride*i)) /\
       eval_operand (Var dp) q = SOME (n2w (dest_base + dst_stride*i)) /\
       (q with vs_vars := s.vs_vars) = s /\
       (!x. ~MEM x [so; dso; sp; dp] ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      simp[mk_inst_def, below_frontier_no_ranges]) >>
  qexists_tac `update_var dp (n2w (dest_base + dst_stride*i))
    (update_var sp (n2w (source_base + src_stride*i))
      (update_var dso (n2w (dst_stride*i))
        (update_var so (n2w (src_stride*i)) s)))` >>
  Cases_on `src` >> Cases_on `dst` >>
  gvs[ALL_DISTINCT, eval_operand_def] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, lookup_var_update_var,
       word_add_n2w, word_mul_n2w] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem typed_bytes_array_initial_cont:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_cont_sim ctx fn s
    (jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
Proof
  strip_tac >> drule_all typed_bytes_array_loop_code >> simp[] >> strip_tac >>
  irule typed_sa_initial_sim >>
  simp[typed_sa_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
  qexists_tac `sa.cs_next_id` >> simp[]
QED

Theorem typed_bytes_array_child_states:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) ==>
  ?sc ec.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+6))) (BaseT (BytesT (Dynamic 33)))
      (Var ("%" ++ toString (sa.cs_next_var+5))) (BaseT (BytesT (Dynamic 1)))
      sc = ((),ec) /\
    sc.cs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
    ec.cs_current_bb = sc.cs_current_bb /\
    sc.cs_current_insts = TAKE 4 (HD sb.cs_blocks).bb_instructions /\
    ec.cs_current_insts = TAKE 10 (HD sb.cs_blocks).bb_instructions /\
    LENGTH sc.cs_current_insts = 4 /\ LENGTH ec.cs_current_insts = 10 /\
    sc.cs_next_var = sa.cs_next_var+7 /\ ec.cs_next_var = sa.cs_next_var+12 /\
    sc.cs_blocks = ec.cs_blocks /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6))
Proof
  strip_tac >>
  qexists_tac `sa with <|
    cs_next_var := sa.cs_next_var+7; cs_next_id := sa.cs_next_id+9;
    cs_next_label := sa.cs_next_label+3;
    cs_current_bb := fresh_label_output "typed_sa_body" (sa.cs_next_label+1);
    cs_blocks := TL sb.cs_blocks;
    cs_current_insts := TAKE 4 (HD sb.cs_blocks).bb_instructions |>` >>
  qexists_tac `SND (compile_store_memory_typed ce
    (Var ("%" ++ toString (sa.cs_next_var+6))) (BaseT (BytesT (Dynamic 33)))
    (Var ("%" ++ toString (sa.cs_next_var+5))) (BaseT (BytesT (Dynamic 1)))
    (sa with <|
      cs_next_var := sa.cs_next_var+7; cs_next_id := sa.cs_next_id+9;
      cs_next_label := sa.cs_next_label+3;
      cs_current_bb := fresh_label_output "typed_sa_body" (sa.cs_next_label+1);
      cs_blocks := TL sb.cs_blocks;
      cs_current_insts := TAKE 4 (HD sb.cs_blocks).bb_instructions |>))` >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_abi_dynamic_def, word_size_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def,
       compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_op_def, emit_void_def, emit_inst_def, emit_def, new_block_def] >>
  strip_tac >> gvs[] >>
  simp[compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def,
       compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_op_def, emit_void_def,
       emit_inst_def, emit_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem typed_bytes_array_body_lookup[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  lookup_block (fresh_label_output "typed_sa_body" (sa.cs_next_label+1))
    fn.fn_blocks = SOME (HD sb.cs_blocks)
Proof
  strip_tac >> drule typed_bytes_array_loop_blocks >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule typed_bytes_array_loop_counters >> strip_tac >>
  fs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem typed_bytes_array_child_code:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?sc ec body_bb.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+6))) (BaseT (BytesT (Dynamic 33)))
      (Var ("%" ++ toString (sa.cs_next_var+5))) (BaseT (BytesT (Dynamic 1)))
      sc = ((),ec) /\ fn_has_code sc ec fn /\
    lookup_block sc.cs_current_bb fn.fn_blocks = SOME body_bb /\
    sc.cs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
    ec.cs_current_bb = sc.cs_current_bb /\
    sc.cs_current_insts = TAKE 4 body_bb.bb_instructions /\
    ec.cs_current_insts = TAKE 10 body_bb.bb_instructions /\
    LENGTH sc.cs_current_insts = 4 /\ LENGTH ec.cs_current_insts = 10 /\
    sc.cs_next_var = sa.cs_next_var+7 /\ ec.cs_next_var = sa.cs_next_var+12 /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+5)) /\
    not_fresh_at sc ("%" ++ toString (sa.cs_next_var+6))
Proof
  strip_tac >> drule_all typed_bytes_array_body_lookup >> strip_tac >>
  drule typed_bytes_array_child_states >> strip_tac >>
  qexistsl_tac [`sc`, `ec`, `HD sb.cs_blocks`] >> simp[] >>
  simp[fn_has_code_def, emitted_blocks_def] >>
  simp[IS_PREFIX_APPEND] >>
  qexists_tac `DROP 10 (HD sb.cs_blocks).bb_instructions` >>
  simp[TAKE_DROP]
QED

(* Straight-line prefixes shared by concrete and child-parametric loops. *)
Theorem typed_array_prefix_cont:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX code bb.bb_instructions /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK q /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 ==>
  mem_cont_sim ctx fn s (q with vs_inst_idx := LENGTH code)
Proof
  strip_tac >>
  irule (SRULE [emitted_insts_def, fn_has_code_def, emitted_blocks_def]
    (Q.INST [`sa` |-> `ARB with <|cs_blocks := []; cs_current_bb := s.vs_current_bb;
        cs_current_insts := []|>`,
      `sb` |-> `ARB with <|cs_blocks := []; cs_current_bb := s.vs_current_bb;
        cs_current_insts := code|>`] (SPEC_ALL typed_bytes_child_seq_cont))) >>
  simp[] >> metis_tac[]
QED

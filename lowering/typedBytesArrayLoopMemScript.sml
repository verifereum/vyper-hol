(* Prefix invariant for the actual Bytes1-to-Bytes33 array loop. *)
Theory typedBytesArrayLoopMem
Ancestors
  typedArrayLoopLayoutMem typedBytesArrayMem typedArrayLoopControlMem
  memContinuation fragExec fragExecMem exprSimAggregateEncoding valueEncoding valueEncodingProps
  venomState venomInst venomExecSemantics compileEnv exprLoweringProps emitHelperProps
  vyperValue vyperTyping words arithmetic list rich_list vfmConstants

Definition typed_bytes_array_prefix_def:
  typed_bytes_array_prefix bss addr stride cap i mem <=>
    !j. j < i ==>
      val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV (EL j bss))
        (addr + stride*j) mem
End

Theorem typed_bytes_array_prefix_zero[local]:
  typed_bytes_array_prefix bss addr stride cap 0 mem
Proof
  simp[typed_bytes_array_prefix_def]
QED

Theorem typed_bytes_array_prefix_suc[local]:
  typed_bytes_array_prefix bss addr stride cap i mem /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV (EL i bss))
    (addr + stride*i) mem ==>
  typed_bytes_array_prefix bss addr stride cap (SUC i) mem
Proof
  simp[typed_bytes_array_prefix_def, prim_recTheory.LESS_THM] >> metis_tac[]
QED

Theorem typed_bytes_array_prefix_preserved[local]:
  typed_bytes_array_prefix bss addr 96 33 i mem /\
  i <= LENGTH bss /\ EVERY (\bs. LENGTH bs <= 1) bss /\
  mem_bytes_at addr (96*i) mem = mem_bytes_at addr (96*i) mem' ==>
  typed_bytes_array_prefix bss addr 96 33 i mem'
Proof
  rw[typed_bytes_array_prefix_def] >>
  `j < LENGTH bss` by decide_tac >>
  `LENGTH (EL j bss) <= 1` by
    (fs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  irule val_in_memory_relocate >>
  conj_tac >- simp[val_wf_def, type_memory_size_def, word_size_def] >>
  qexistsl_tac [`mem`, `96`, `addr + 96*j`] >>
  simp[type_memory_size_def, word_size_def] >>
  irule mem_bytes_at_translated_window >>
  qexists_tac `96*i` >> simp[]
QED

Theorem typed_bytes_array_prefix_array:
  typed_bytes_array_prefix bss addr 96 33 (LENGTH bss) mem ==>
  val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 33))) (Fixed (LENGTH bss)))
    (ArrayV (make_array_value (BaseTV (BytesT (Dynamic 33)))
      (Fixed (LENGTH bss)) (MAP BytesV bss))) addr mem
Proof
  strip_tac >> irule fixed_array_from_dense >> simp[] >>
  irule elems_in_memory_intro >>
  fs[typed_bytes_array_prefix_def, EL_MAP, type_memory_size_def,
     word_size_def]
QED

Theorem typed_bytes_array_source_element[local]:
  typed_bytes_array_prefix bss addr 64 1 (LENGTH bss) mem /\
  EVERY (\bs. LENGTH bs <= 1) bss /\ j < LENGTH bss /\
  mem_bytes_at addr (64 * LENGTH bss) mem =
    mem_bytes_at addr (64 * LENGTH bss) mem' ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV (EL j bss))
    (addr + 64*j) mem'
Proof
  strip_tac >>
  `LENGTH (EL j bss) <= 1` by
    (fs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  irule val_in_memory_relocate >>
  conj_tac >- simp[val_wf_def, type_memory_size_def, word_size_def] >>
  qexistsl_tac [`mem`, `64`, `addr + 64*j`] >>
  fs[typed_bytes_array_prefix_def, type_memory_size_def, word_size_def] >>
  irule mem_bytes_at_translated_window >>
  qexists_tac `64 * LENGTH bss` >> simp[]
QED

Definition typed_bytes_array_loop_inv_def:
  typed_bytes_array_loop_inv sa bss source_addr dest_addr initial i s <=>
    i <= LENGTH bss /\ ~s.vs_halted /\
    s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    s.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
    mem_bytes_at source_addr (64 * LENGTH bss) s.vs_memory =
      mem_bytes_at source_addr (64 * LENGTH bss) initial.vs_memory /\
    typed_bytes_array_prefix bss dest_addr 96 33 i s.vs_memory /\
    (s with <|vs_vars := initial.vs_vars; vs_memory := initial.vs_memory;
      vs_current_bb := initial.vs_current_bb; vs_inst_idx := initial.vs_inst_idx;
      vs_prev_bb := initial.vs_prev_bb|>) = initial /\
    (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x initial)
End

Theorem typed_bytes_array_loop_init[local]:
  ~s.vs_halted ==>
  typed_bytes_array_loop_inv sa bss source_addr dest_addr s 0
    (jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
Proof
  strip_tac >>
  simp[typed_bytes_array_loop_inv_def, typed_bytes_array_prefix_zero,
       jump_to_def, update_var_def, lookup_var_def, eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> "%" ++ toString sa.cs_next_var` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >> gvs[]
QED

Theorem typed_bytes_array_loop_start[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. typed_bytes_array_loop_inv sa bss source_addr dest_addr s 0 u /\
      mem_cont_sim ctx fn s u
Proof
  strip_tac >> drule_all typed_bytes_array_initial_cont >> strip_tac >>
  qexists_tac `jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
    (update_var ("%" ++ toString sa.cs_next_var) 0w s)` >>
  simp[typed_bytes_array_loop_init]
QED

Theorem typed_bytes_array_loop_exit_cont[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  typed_bytes_array_loop_inv sa bss source_addr dest_addr initial (LENGTH bss) u /\
  LENGTH bss < dimword(:256) /\
  lookup_block (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
    fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  mem_cont_sim ctx fn u
    (jump_to (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) (LENGTH bss) (LENGTH bss) u))
Proof
  strip_tac >> drule_all typed_bytes_array_loop_code >> simp[] >> strip_tac >>
  fs[typed_bytes_array_loop_inv_def] >>
  irule (SRULE [] (Q.INST [`i` |-> `LENGTH bss`, `ncount` |-> `LENGTH bss`]
    (SPEC_ALL typed_sa_header_sim))) >> simp[] >>
  qexistsl_tac [`fresh_label_output "typed_sa_body" (sa.cs_next_label+1)`,
    `"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >> simp[]
QED

Theorem typed_bytes_array_prefix_cont[local]:
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


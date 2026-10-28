(* TOP-LEVEL: aggregate argument snapshots execute the actual emitted
   allocation and copy. Zero-size aggregates emit only the allocation. *)
Theory memoryValueSnapshot
Ancestors
  memoryValueRelocation memoryValueDefs valueEncoding
  stmtLowering exprLowering context compileEnv exprLoweringProps emitHelper emitHelperProps
  ssaOperandFrame fragBlockPath fragExec instIdxIndep memoryReadProps
  venomExecSemantics venomState venomInst
  finite_map list rich_list words arithmetic
Libs wordsLib

Definition memory_snapshot_addr_def:
  memory_snapshot_addr id ss : bytes32 =
    n2w (case FLOOKUP ss.vs_allocas id of
           NONE => ss.vs_alloca_next | SOME (offset,sz) => offset)
End

Definition memory_snapshot_alloc_frame_def:
  memory_snapshot_alloc_frame id byte_count ss =
    if FLOOKUP ss.vs_allocas id = NONE then
      ss with <| vs_allocas := ss.vs_allocas |+ (id,(ss.vs_alloca_next,byte_count));
                 vs_alloca_next := ss.vs_alloca_next + byte_count |>
    else ss
End

Definition memory_snapshot_allocated_def:
  memory_snapshot_allocated id (var_base:num) byte_count ss =
    update_var (STRING #"%" (toString var_base)) (memory_snapshot_addr id ss)
      (memory_snapshot_alloc_frame id byte_count ss)
End

Definition memory_snapshot_result_def:
  memory_snapshot_result id var_base byte_count (src_addr:bytes32) ss =
    if byte_count = 0 then memory_snapshot_allocated id var_base byte_count ss
    else mcopy (w2n (memory_snapshot_addr id ss)) (w2n src_addr) byte_count
      (memory_snapshot_allocated id var_base byte_count ss)
End

Theorem compile_materialize_aggregate_code:
  !cenv ty src cs op cs'.
    ~is_word_type ty /\ ~is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') ==>
    op = Var (STRING #"%" (toString cs.cs_next_var)) /\
    emitted_insts cs cs' =
      [mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
        [STRING #"%" (toString cs.cs_next_var)]] ++
      (if type_memory_bytes cenv ty = 0 then [] else
        [mk_inst (cs.cs_next_id + 1) MCOPY
          [Var (STRING #"%" (toString cs.cs_next_var)); src;
           Lit (n2w (type_memory_bytes cenv ty))] []]) /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 1
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `type_memory_bytes cenv ty` >>
  gvs[compile_materialize_vv_def, unwrap_value_def, compile_alloc_buffer_def,
    compile_store_memory_def, compile_copy_memory_def, emit_op_def, emit_void_def,
    fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emitted_insts_def,
    same_blocks_def, DROP_APPEND1, DROP_LENGTH_NIL]
QED

Theorem memory_snapshot_allocated_memory[simp]:
  !id var_base byte_count ss.
    (memory_snapshot_allocated id var_base byte_count ss).vs_memory = ss.vs_memory
Proof
  simp[memory_snapshot_allocated_def, update_var_def, memory_snapshot_alloc_frame_def] >>
  rw[]
QED

Theorem memory_snapshot_alloc_frame_operand:
  !arg_op id byte_count ss.
    eval_operand arg_op (memory_snapshot_alloc_frame id byte_count ss) = eval_operand arg_op ss
Proof
  Cases_on `arg_op` >>
  simp[memory_snapshot_alloc_frame_def, eval_operand_def, lookup_var_def] >> rw[]
QED

Theorem memory_snapshot_allocated_operand:
  !arg_op id var_base byte_count ss.
    arg_op <> Var (STRING #"%" (toString var_base)) ==>
    eval_operand arg_op (memory_snapshot_allocated id var_base byte_count ss) =
      eval_operand arg_op ss
Proof
  simp[memory_snapshot_allocated_def, eval_operand_update_var_avoids,
    memory_snapshot_alloc_frame_operand]
QED

Theorem memory_snapshot_allocated_result[simp]:
  !id var_base byte_count ss.
    eval_operand (Var (STRING #"%" (toString var_base)))
      (memory_snapshot_allocated id var_base byte_count ss) = SOME (memory_snapshot_addr id ss)
Proof
  simp[memory_snapshot_allocated_def, eval_operand_update_var]
QED

val snapshot_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``ALLOCA``, ``MCOPY``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem memory_snapshot_allocation_step:
  !id var_base byte_count ss.
    byte_count < dimword(:256) ==>
    step_inst_base (mk_inst id ALLOCA [Lit (n2w byte_count)]
      [STRING #"%" (toString var_base)]) ss =
      OK (memory_snapshot_allocated id var_base byte_count ss)
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `FLOOKUP ss.vs_allocas id`
  >- asm_simp_tac (srw_ss()) (snapshot_steps @
       [memory_snapshot_allocated_def, memory_snapshot_addr_def,
        memory_snapshot_alloc_frame_def, exec_alloca_def, mk_inst_def,
        eval_operand_lit, LET_THM]) >>
  rename1 `FLOOKUP _ _ = SOME recorded_region` >> PairCases_on `recorded_region` >>
  asm_simp_tac (srw_ss()) (snapshot_steps @
    [memory_snapshot_allocated_def, memory_snapshot_addr_def,
     memory_snapshot_alloc_frame_def, exec_alloca_def, mk_inst_def,
     eval_operand_lit, LET_THM])
QED

Theorem memory_snapshot_copy_step:
  !id var_base byte_count src ss src_addr.
    byte_count < dimword(:256) /\ eval_operand src ss = SOME src_addr /\
    src <> Var (STRING #"%" (toString var_base)) ==>
    step_inst_base (mk_inst (id + 1) MCOPY
      [Var (STRING #"%" (toString var_base)); src; Lit (n2w byte_count)] [])
      (memory_snapshot_allocated id var_base byte_count ss) =
      OK (mcopy (w2n (memory_snapshot_addr id ss)) (w2n src_addr) byte_count
        (memory_snapshot_allocated id var_base byte_count ss))
Proof
  rpt gen_tac >> DISCH_TAC >>
  asm_simp_tac (srw_ss()) (snapshot_steps @
    [mk_inst_def, memory_snapshot_allocated_operand, eval_operand_lit])
QED

Theorem compile_materialize_aggregate_execution:
  !cenv ty src cs op cs' ss src_addr.
    ~is_word_type ty /\ ~is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_bytes cenv ty < dimword(:256) /\
    eval_operand src ss = SOME src_addr /\
    src <> Var (STRING #"%" (toString cs.cs_next_var)) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (memory_snapshot_result cs.cs_next_id cs.cs_next_var
        (type_memory_bytes cenv ty) src_addr ss)
Proof
  rpt strip_tac >> drule_all compile_materialize_aggregate_code >>
  strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `type_memory_bytes cenv ty`,
    `src`, `ss`, `src_addr`] memory_snapshot_copy_step) >>
  impl_tac >- simp[] >> DISCH_TAC >> Cases_on `type_memory_bytes cenv ty = 0` >>
  simp[run_inst_seq_def, memory_snapshot_result_def,
    memory_snapshot_allocation_step, memory_snapshot_copy_step]
QED

Theorem memory_snapshot_result_reads:
  !id var_base byte_count src_addr ss read_len.
    read_len <= byte_count ==>
    read_memory (w2n (memory_snapshot_addr id ss)) read_len
      (memory_snapshot_result id var_base byte_count src_addr ss) =
      read_memory (w2n src_addr) read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `byte_count = 0`
  >- (gvs[] >> simp[memory_snapshot_result_def,
        read_memory_eq_mem_bytes_at, mem_bytes_at_def]) >>
  mp_tac (Q.SPECL [`w2n (memory_snapshot_addr id ss)`, `w2n (src_addr:bytes32)`,
    `byte_count`, `read_len`, `memory_snapshot_allocated id var_base byte_count ss`]
    read_memory_mcopy_prefix) >> impl_tac >- fs[] >>
  simp[memory_snapshot_result_def, read_memory_eq_mem_bytes_at]
QED

Theorem memory_snapshot_result_layout:
  !tv v id var_base byte_count src_addr ss.
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= byte_count ==>
    memory_value_rel tv v (w2n (memory_snapshot_addr id ss))
      (memory_snapshot_result id var_base byte_count src_addr ss).vs_memory
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory (w2n (memory_snapshot_addr id ss)) (type_memory_size tv)
    (memory_snapshot_result id var_base byte_count src_addr ss) =
    read_memory (w2n src_addr) (type_memory_size tv) ss` by
    (irule memory_snapshot_result_reads >> fs[]) >>
  mp_tac (Q.SPECL [`tv`, `v`, `w2n (src_addr:bytes32)`, `ss.vs_memory`,
    `w2n (memory_snapshot_addr id ss)`,
    `(memory_snapshot_result id var_base byte_count src_addr ss).vs_memory`]
    memory_value_rel_relocate) >>
  impl_tac >- fs[read_memory_eq_mem_bytes_at] >> simp[]
QED

Theorem memory_snapshot_result_operand[simp]:
  !id var_base byte_count src_addr ss.
    eval_operand (Var (STRING #"%" (toString var_base)))
      (memory_snapshot_result id var_base byte_count src_addr ss) =
      SOME (memory_snapshot_addr id ss)
Proof
  rpt gen_tac >> Cases_on `byte_count = 0` >>
  simp[memory_snapshot_result_def, eval_operand_mcopy_eq]
QED

Theorem memory_snapshot_result_operand_frame:
  !arg_op id var_base byte_count src_addr ss.
    arg_op <> Var (STRING #"%" (toString var_base)) ==>
    eval_operand arg_op (memory_snapshot_result id var_base byte_count src_addr ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> Cases_on `byte_count = 0` >>
  simp[memory_snapshot_result_def, eval_operand_mcopy_eq, memory_snapshot_allocated_operand]
QED

Theorem memory_snapshot_result_control[simp]:
  !id var_base byte_count src_addr ss.
    (memory_snapshot_result id var_base byte_count src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (memory_snapshot_result id var_base byte_count src_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (memory_snapshot_result id var_base byte_count src_addr ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `byte_count = 0` >> Cases_on `FLOOKUP ss.vs_allocas id` >>
  simp[memory_snapshot_result_def, memory_snapshot_allocated_def,
    memory_snapshot_alloc_frame_def, update_var_def, mcopy_def,
    write_memory_with_expansion_def]
QED

Theorem compile_materialize_aggregate_straight:
  !cenv ty src cs op cs'.
    ~is_word_type ty /\ ~is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs')
Proof
  rpt strip_tac >> drule_all compile_materialize_aggregate_code >> strip_tac >>
  Cases_on `type_memory_bytes cenv ty = 0` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem compile_materialize_aggregate_path:
  !ctx func cenv ty tv v src cs op cs' ss src_addr.
    ~is_word_type ty /\ ~is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_bytes cenv ty < dimword(:256) /\
    eval_operand src ss = SOME src_addr /\
    src <> Var (STRING #"%" (toString cs.cs_next_var)) /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ val_wf tv v /\
    type_memory_size tv <= type_memory_bytes cenv ty /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. out = (memory_snapshot_result cs.cs_next_id cs.cs_next_var
        (type_memory_bytes cenv ty) src_addr ss with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\
      eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      memory_value_rel tv v (w2n (memory_snapshot_addr cs.cs_next_id ss)) out.vs_memory /\
      (!arg_op. arg_op <> op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule_all compile_materialize_aggregate_execution >> strip_tac >>
  drule_all compile_materialize_aggregate_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts cs cs')` by
    (drule_all compile_materialize_aggregate_straight >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `memory_snapshot_result cs.cs_next_id cs.cs_next_var
      (type_memory_bytes cenv ty) src_addr ss`] fragment_path_emitted) >>
  impl_tac >- simp[] >> strip_tac >>
  `memory_value_rel tv v (w2n (memory_snapshot_addr cs.cs_next_id ss))
    (memory_snapshot_result cs.cs_next_id cs.cs_next_var
      (type_memory_bytes cenv ty) src_addr ss).vs_memory` by
    (irule memory_snapshot_result_layout >> simp[]) >>
  qexists_tac `(memory_snapshot_result cs.cs_next_id cs.cs_next_var
    (type_memory_bytes cenv ty) src_addr ss) with
      vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx, memory_snapshot_result_operand_frame]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete memory snapshot theorem: " ^ name)
  end) (DB.thms "memoryValueSnapshot")

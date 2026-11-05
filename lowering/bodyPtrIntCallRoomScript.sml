Theory bodyPtrIntCallRoom
Ancestors
  intCallCallee exprLoweringProps fragExec venomState venomInst
  venomExecSemantics words finite_map arithmetic pred_set list
  loweringHalt emitHelper compileEnv allocLimits exprSimHyps exprSimHypsDefs vyperAST

(* Static charge is nonincreasing along the concrete raw sequence. *)
Theorem intcall_run_inst_seq_alloca_room:
  !is func s t ctx.
    run_inst_seq is s = OK t /\
    EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE) is /\
    alloca_room ctx func s ==>
    alloca_room ctx func t
Proof
  rpt strip_tac >> drule_all run_inst_seq_static_charge >>
  fs[alloca_room_def] >> decide_tac
QED

Theorem intcall_scratch_room:
  alloca_room ctx func s /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
  inst.inst_id NOTIN FDOM s.vs_allocas /\ n < dimword (:256) ==>
  s.vs_alloca_next + n < dimword (:256)
Proof
  strip_tac >> drule_all alloca_room_fresh >> simp[w2n_n2w]
QED

Theorem intcall_compile_scratch_room:
  compile_alloc_buffer n st = (buf,st') /\ fn_has_code st st' func /\
  alloca_room ctx func s /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  n < dimword (:256) ==>
  s.vs_alloca_next + n < dimword (:256)
Proof
  strip_tac >> drule compile_alloc_buffer_emission >> strip_tac >>
  `fn_has_code sx st' func` by metis_tac[fn_has_code_split] >>
  drule_all emit_inst_fn_member >> strip_tac >>
  irule intcall_scratch_room >> conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`ctx`,`func`,`mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [p]`] >>
  gvs[mk_inst_def] >> strip_tac >> res_tac >> decide_tac
QED

(* Allocation limits bound aggregates; every word-shaped type occupies 32 bytes. *)
Theorem intcall_type_alloc_room:
  type_alloc_ok ce ty ==> type_memory_bytes ce ty < dimword (:256)
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (Cases_on `ty` >> gvs[is_word_type_def, type_memory_bytes_def, dimword_def] >>
      rename1 `is_word_type (BaseT b)` >> Cases_on `b` >>
      gvs[is_word_type_def, type_memory_bytes_def, dimword_def] >>
      rename1 `is_word_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
      gvs[is_word_type_def, type_memory_bytes_def, dimword_def]) >>
  fs[type_alloc_ok_def, dimword_def] >> decide_tac
QED

Theorem intcall_expr_body_scratch_size:
  expr_body_pre ce cx env e es /\ ty = expr_type e /\
  ce'.ce_struct_fields = ce.ce_struct_fields ==>
  type_memory_bytes ce' ty < dimword (:256)
Proof
  strip_tac >>
  `type_alloc_ok ce (expr_type e)` by
    (irule alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_def]) >>
  drule intcall_type_alloc_room >>
  drule type_memory_bytes_struct_fields >> simp[]
QED

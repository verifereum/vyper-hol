(* Compiler-facing clean variable-size RETURN boundary. *)
Theory extRetAbiReturnConsumerPtr
Ancestors
  extRetCountedPtr fragExec fragGasPathPtr fragGasSeqPtr
  emitHelper compileEnv bodyPtrDefs ptrDiscipline venomState venomInst
  words list arithmetic

Theorem emit_return_clean_gas_path_ptr:
  emit_inst RETURN [Var dst; Var len] [] sa = (u,sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dst s = SOME (n2w b) /\ lookup_var len s = SOME (n2w n) /\
  n < dimword(:256) /\ b < dimword(:256) /\ ptr_covers G tn dst s n /\
  op_taint tn (Var len) = {} /\ stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!i. b <= i /\ i < b+n ==> i NOTIN tn.t_mem) ==>
  ?t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tn (Halt t)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id RETURN [Var dst; Var len] []]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id RETURN [Var dst; Var len] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_covers G tn dst s (w2n (n2w n : 256 word))` by simp[] >>
  `!i. w2n (n2w b : 256 word) <= i /\
       i < w2n (n2w b : 256 word)+w2n (n2w n : 256 word) ==> i NOTIN tn.t_mem` by
    simp[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all return_var_size_gas_path_ptr >> metis_tac[]
QED

Theorem gas_path_ptr_then_emit_return_clean:
  gas_path_ptr (cx_dead cx) 0 ctx fn PG G0 tn0 s0 k G tn (OK s) /\
  emit_inst RETURN [Var dst; Var len] [] sa = (u,sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var dst s = SOME (n2w b) /\ lookup_var len s = SOME (n2w n) /\
  n < dimword(:256) /\ b < dimword(:256) /\ ptr_covers G tn dst s n /\
  op_taint tn (Var len) = {} /\ stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
  (!i. b <= i /\ i < b+n ==> i NOTIN tn.t_mem) ==>
  ?t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G0 tn0 s0 k G tn (Halt t)
Proof
  strip_tac >> drule_all emit_return_clean_gas_path_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexists_tac `t` >>
  irule (gas_path_ptr_then |> Q.INST [`m` |-> `0`] |> SRULE []) >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[]
QED

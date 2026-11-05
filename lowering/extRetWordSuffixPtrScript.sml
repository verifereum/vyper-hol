Theory extRetWordSuffixPtr
Ancestors
  extRetCountedPtr loweringHalt contextCodegenRelProps fragExec
  stmtLowering compileEnv venomState venomInst fragGasPathPtr
  abiBuiltinAllocation bodyPtrDefs finite_map

(* The suffix starts at an indexed boundary, even when the prefix's last
   instruction is a terminator. No intermediate openness is needed. *)
Theorem compile_external_return_word_suffix_gas_path_ptr:
  !cx ctx fn PG G tn s op ei msz nkey ut iv st x st' w base.
    compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    fn_has_code st st' fn /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
      st.cs_next_id = SOME (base,32) /\ base < dimword (:256) ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_word_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) /\
   get_instruction bb (s.vs_inst_idx + 1) =
     SOME (mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] []) /\
   get_instruction bb (s.vs_inst_idx + 2) =
     SOME (mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn n => mp_tac (Q.SPEC n th)) [`0`, `1`, `2`]) >> simp[]) >>
  irule alloca_return_word_gas_path_ptr >> simp[] >> metis_tac[]
QED

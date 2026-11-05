Theory extRetCopySuffixPtr
Ancestors
  extRetCountedPtr loweringHalt contextCodegenRelProps fragExec
  stmtLowering compileEnv venomState venomInst fragGasPathPtr
  abiBuiltinAllocation bodyPtrDefs finite_map words list

Theorem compile_external_return_copy_suffix_gas_path_ptr:
  !cx ctx fn PG G tn s src m n nkey ut iv st x st' cenv es ty sa sb v tv w.
    compile_external_return (SOME (Var src)) F F (AbiCopy m) n F nkey ut iv st =
      (x,st') /\ not_fresh_at st src /\
    fn_has_code st st' fn /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v (Var src) s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand (Var src) s = SOME w /\
    n < dimword (:256) /\ m <= n /\ m <= val_footprint tv v /\
    ptr_covers G tn src s m /\
    (!j. w2n w <= j /\ j < w2n w + m ==> j NOTIN tn.t_mem) /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `src <> buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (st.cs_next_id+1) MCOPY [Var buf; Var src; Lit (n2w m)] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (st.cs_next_id+2) RETURN [Var buf; Lit (n2w m)] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  qspecl_then [`st.cs_next_id`, `n2w n`, `buf`, `s`]
    strip_assume_tac step_alloca_frame >>
  qpat_x_assum `!i. i < _ ==> _` kall_tac >>
  gvs[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) alloca_copy_return_gas_path_ptr >>
  simp[] >> disch_then drule_all >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem compile_external_return_copy_zero_suffix_gas_path_ptr:
  !cx ctx fn PG G tn s op n nkey ut iv st x st' cenv es w.
    compile_external_return (SOME op) F F (AbiCopy 0) n F nkey ut iv st = (x,st') /\
    (!y. op = Var y ==> not_fresh_at st y) /\
    fn_has_code st st' fn /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es s /\ n < dimword (:256) /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `op <> Var buf` by metis_tac[] >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) /\
   get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (st.cs_next_id+1) MCOPY [Var buf; op; Lit 0w] []) /\
   get_instruction bb (s.vs_inst_idx+2) =
     SOME (mk_inst (st.cs_next_id+2) RETURN [Var buf; Lit 0w] [])` by
    (qpat_x_assum `!i. _` (fn th =>
       map_every (fn j => mp_tac (Q.SPEC j th)) [`0`, `1`, `2`]) >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [buf]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >>
     qexistsl_tac [`bb`, `s.vs_current_bb`] >> simp[] >>
     gvs[get_instruction_def] >>
     `LENGTH st.cs_current_insts < LENGTH bb.bb_instructions` by decide_tac >>
     metis_tac[listTheory.EL_MEM]) >>
  qpat_x_assum `!i. i < _ ==> _` kall_tac >>
  gvs[] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) alloca_copy_zero_gas_path_ptr >>
  simp[] >> metis_tac[]
QED

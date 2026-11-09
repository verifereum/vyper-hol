(* Empty fixed-array copies execute no memory accesses, even on the slow path. *)
Theory typedCopyEmptyMemory
Ancestors
  typedCopyIndexMemory typedCopyControlMemory typedMemoryCopy fragExecMem fragLoopMemory fragExec
  context contextProps compileEnv emitHelper exprLoweringProps
  venomExecSemantics venomState valueEncoding words list arithmetic

Theorem typed_copy_sarray_zero_slow_frag_mem[local]:
  compile_copy_sarray_typed cenv dst dty src sty 0 sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `fresh_label "typed_sa_cond" sa = (hdr,l1)` >>
  rename1 `fresh_label "typed_sa_body" l1 = (blabel,l2)` >>
  rename1 `fresh_label "typed_sa_exit" l2 = (exit,l3)` >>
  rename1 `fresh_var l3 = (counter,init)` >>
  rename1 `emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0)` >>
  rename1 `emit_inst JMP [Label hdr] [] st0 = ((),st1)` >>
  rename1 `new_block hdr st1 = (u1,sth)` >>
  rename1 `emit_op LT [Var counter; Lit 0w] sth = (lt,h1)` >>
  rename1 `emit_op ISZERO [lt] h1 = (done,stj)` >>
  rename1 `emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2)` >>
  rename1 `new_block blabel st2 = (u2,stb)` >>
  rename1 `emit_inst ASSIGN [_] [counter] _ = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all typed_copy_sarray_slow_layout >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qmatch_goalsub_abbrev_tac `frag_exec_mem ctx sa stx P Q R` >>
  qabbrev_tac `Inv = \k t. k = 0 /\ lookup_var counter t = SOME 0w /\
    t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t` >>
  qabbrev_tac `J = \k t. Inv k t /\ eval_operand done t = SOME 1w` >>
  suspend "compose"
QED

Resume typed_copy_sarray_zero_slow_frag_mem[compose]:
  `frag_exec_mem ctx init st0 P (Inv 0) R` by
    (simp[Abbr `P`, Abbr `Inv`, Abbr `R`] >>
     `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
     drule_all typed_copy_assign_frag_mem >> disch_then (qspec_then `ctx` mp_tac) >>
     disch_then (mp_then Any irule frag_exec_mem_conseq) >>
     simp[Abbr `Q`, typed_copy_state_frame_def] >> metis_tac[]) >>
  `frag_exec_mem ctx sa st0 P (Inv 0) R` by
    (qpat_x_assum `frag_exec_mem _ init _ _ _ _` mp_tac >>
     simp[frag_exec_mem_def, fragExecTheory.fn_has_code_def,
          fragExecTheory.emitted_blocks_def]) >>
  `frag_exec_mem ctx st0 stx (Inv 0) (J 0) R` by suspend "loop" >>
  `cs_extends sa st0 /\ cs_extends st0 stx` by metis_tac[ci_mono_def] >>
  drule_all frag_exec_mem_seq >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_index_inv_def]
QED

Resume typed_copy_sarray_zero_slow_frag_mem[loop]:
  irule frag_exec_loop_mem >> conj_tac
  >- (simp[Abbr `Inv`, Abbr `Q`, typed_copy_state_frame_jump,
           typed_copy_lookup_var_jump] >> simp[jump_to_def]) >>
  conj_tac
  >- (simp[Abbr `J`, Abbr `Inv`, Abbr `Q`, typed_copy_state_frame_jump,
           typed_copy_lookup_var_jump, typed_copy_eval_operand_jump] >>
      simp[jump_to_def]) >>
  qexistsl_tac [`blabel`, `done`, `exit`, `hdr`] >>
  goal_assum (drule_at (Pat `new_block exit _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ ste = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ st0 = _`)) >>
  goal_assum (drule_at (Pat `new_block hdr _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block blabel _ = _`)) >> simp[] >>
  rpt (qpat_x_assum `fresh_label _ _ = _` kall_tac) >>
  qpat_x_assum `fresh_var _ = _` kall_tac >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac) >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  conj_tac
  >- simp[Abbr `J`] >>
  rpt strip_tac >> simp[Abbr `J`, Abbr `R`] >>
  irule frag_exec_mem_pointwise >> qx_gen_tac `t` >> strip_tac >>
  `lookup_var counter t = SOME (n2w 0)` by gvs[Abbr `Inv`] >>
  drule_all (SRULE [] (Q.INST [`N` |-> `0`, `k` |-> `0`]
    (SPEC_ALL typed_copy_header_frag_mem))) >>
  disch_then (qspecl_then [`w2n dw`, `0`, `ctx`] mp_tac) >> simp[] >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  rpt strip_tac >> simp[Abbr `Inv`] >> conj_tac
  >- metis_tac[typed_copy_state_frame_counter] >>
  simp[Abbr `Q`] >> conj_tac >- gvs[] >>
  irule typed_copy_state_frame_trans >> qexists_tac `t` >>
  simp[] >> conj_tac >- gvs[] >>
  irule typed_copy_state_frame_mono >> goal_assum (drule_at Any) >> simp[]
QED

Finalise typed_copy_sarray_zero_slow_frag_mem

Theorem typed_copy_sarray_zero_frag_mem:
  compile_copy_sarray_typed cenv dst dty src sty 0 sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  frag_exec_mem ctx sa sb (\u. u = s)
    (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  rpt strip_tac >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\
              ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def, compile_copy_memory_zero] >>
      strip_tac >> gvs[] >> irule frag_exec_mem_refl >> simp[]) >>
  irule typed_copy_sarray_zero_slow_frag_mem >> metis_tac[]
QED

(* No-access composition for heterogeneous fields with empty layouts. *)
Theory typedCopyEmptyFieldsMemory
Ancestors
  typedCopyEmptyMemory typedMemoryCopy fragExecMem context contextProps
  compileEnv emitHelper exprLoweringProps venomExecSemantics venomState
  valueEncoding words list arithmetic

Theorem typed_copy_fields_empty_frag_mem:
  !dtys stys dst src sa sb s dw sw.
    LENGTH stys = LENGTH dtys /\
    (!i. i < LENGTH dtys ==>
      type_memory_bytes cenv (EL i dtys) = 0 /\
      type_memory_bytes cenv (EL i stys) = 0 /\
      (!dst src sa sb s dw sw.
        compile_store_memory_typed cenv dst (EL i dtys) src (EL i stys) sa = ((),sb) /\
        (!x. dst = Var x ==> not_fresh_at sa x) /\
        (!x. src = Var x ==> not_fresh_at sa x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
        frag_exec_mem ctx sa sb (\u. u = s)
          (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F))) /\
    compile_typed_copy_fields cenv dst src dtys stys 0 0 sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
    frag_exec_mem ctx sa sb (\u. u = s)
      (\t. t.vs_memory = s.vs_memory /\ typed_copy_state_frame sa (w2n dw) 0 s t) (\r. F)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_store_memory_typed_def, comp_return_def] >>
      irule frag_exec_mem_refl >> simp[]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> gnvs[] >>
  rename1 `compile_typed_copy_fields cenv dst src (dty::dtys) (sty::stys) 0 0 sa = ((),sb)` >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, compile_with_byte_offset_clauses,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory_typed cenv dst dty src sty sa = (u,sc)` >>
  Cases_on `u` >> gvs[] >>
  suspend "compose"
QED

Resume typed_copy_fields_empty_frag_mem[compose]:
  `ci_mono sa sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends sa sc /\ cs_extends sc sb` by metis_tac[ci_mono_def] >>
  qpat_x_assum `!dst src sa sb s dw sw. _` drule_all >>
  disch_then (mp_then Any irule frag_exec_mem_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typed_copy_operand_fresh_mono] >>
  qpat_x_assum `!stys dst src sa sb s dw sw. _`
    (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >>
  impl_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[] >> metis_tac[]) >>
  disch_then (mp_then Any irule frag_exec_mem_conseq) >> simp[] >>
  metis_tac[typed_copy_state_frame_mono, typed_copy_state_frame_trans]
QED

Finalise typed_copy_fields_empty_frag_mem

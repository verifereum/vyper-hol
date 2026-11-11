(* Counted RET at the very endpoint of a protected typed copy. *)
Theory bodyIntCallSharpReturn
Ancestors
  bodyIntCallCopySharpRank bodyIntCallReachableReturn
  bodyIntCallCopySharpDynamic placeMemoryCopyEffect emitHelperProps
  emitHelper compileEnv fragExec fragGasPath fragGasMode gasCount
  venomExecSemantics venomInst venomState

Theorem emitted_memory_ret_path:
  emit_inst RET [rpc] [] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (?pc. eval_operand rpc s = SOME pc) ==>
  gas_path ctx func s 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id RET [rpc] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH _ ==> _`
    (qspec_then `0` assume_tac) >>
  irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  simp[gas_path_edge_def] >>
  qexistsl_tac [`0`, `mk_inst sa.cs_next_id RET [rpc] []`] >>
  simp[gas_count_step_def] >>
  conj_tac >- gvs[] >> disj2_tac >>
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def,
       eval_operands_def, exit_result_def]
QED

Theorem typed_copy_effect_ret_path:
  typed_copy_effect ctx func sa sm s t d n /\
  emit_inst RET [rpc] [] sm = ((),sb) /\ fn_has_code sm sb func /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (?pc. eval_operand rpc s = SOME pc) /\
  (!b sz. P b sz ==> regions_disjoint b sz d n) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  gas_path ctx func s 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
  (!b sz. P b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!op. reserved op ==> eval_operand op t = eval_operand op s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand rpc t = eval_operand rpc s` by
    (irule typed_copy_effect_operand_preserved >> metis_tac[]) >>
  `gas_path ctx func t 0
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)` by
    (irule emitted_memory_ret_path >>
     drule typed_copy_effect_endpoint >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (drule typed_copy_effect_path >>
      simp[gas_marked_path_def] >> strip_tac >>
      drule_all gas_path_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
      gvs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule typed_copy_effect_operand_preserved >> metis_tac[]) >>
  gvs[typed_copy_effect_def, venom_state_component_equality]
QED

Theorem protected_sharp_store_ret_path:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  fn_inst_ids_distinct func /\ type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  regions_disjoint (w2n sw) (type_memory_size stv)
                   (w2n dw) (type_memory_size dtv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  compile_store_memory_typed cenv dp dt sp st sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\
  (!x. dp = Var x ==> not_fresh_at sa x) /\
  (!x. sp = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand dp s = SOME dw /\ eval_operand sp s = SOME sw /\
  (?pc. eval_operand rpc s = SOME pc) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!b sz. P b sz ==>
     regions_disjoint b sz (w2n dw) (type_memory_size dtv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
    gas_path ctx func s 0
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
    (!b sz. P b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!op. reserved op ==> eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sa sm s t (w2n dw) (type_memory_size dtv)` by
    (irule compile_store_memory_typed_forward_sharp >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`stv`, `sw`, `tenv`] >>
     gvs[compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  irule typed_copy_effect_ret_path >>
  goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`rpc`, `sb`] >> simp[]
QED

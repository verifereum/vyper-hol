(* Synchronized actual compiler boundary and counted entry resources. *)
Theory bodyIntCallPackageRun
Ancestors
  bodyIntCallPackageBoundary bodyIntCallInvokedCode bodyIntCallPackageInputs
  bodyIntCallInvokeEntry bodyIntCallPackageControl allocaFrontierBound compileVyper
  venomExecProps venomWf list

Theorem invoked_internal_body_run:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  cenv.ce_func_info (nsid_to_string (NONE,name)) = (nret,rbs,pvs) /\
  set_internal_package_target cenv.ce_target
    (package_internal_fn tops F (assign_nkeys tops 0) cenv.ce_is_ctor
      (if cx.in_deploy then
         compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
       else 0)
      (mut,F,rr,name,args,([] : expr list),ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor,ilen,ss',rt) ==>
  label = lbl /\ is_nr = F /\ ss' = ss /\
  ?entry final ce2 pc imm body_start body_env body_end u mr.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,pc,imm),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case rt of NONE => emit_inst RET [pc] [] body_end
                   | SOME ty => emit_inst INVALID [] [] body_end) = ((),final) /\
    fn_has_code entry body_start callee /\
    fn_has_code body_start body_end callee /\ fn_has_code body_end final callee /\
    entry.cs_current_insts = [] /\
    entry.cs_current_bb = (HD callee.fn_blocks).bb_label /\
    setup_callee callee argv t = SOME entered /\
    run_inst_seq (emitted_insts entry body_start) entered = OK u /\
    gas_path ctx callee entered
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts entry body_start)))
      (OK (u with vs_inst_idx := LENGTH body_start.cs_current_insts)) /\
    ~u.vs_halted /\ u.vs_current_bb = body_start.cs_current_bb /\
    mat_inv callee ce2 penv body_start u t.vs_alloca_next mr /\
    mat_frame entry entered u /\
    (!n b sz. mr n = SOME (b,sz) <=>
      ?i off. i < LENGTH params /\ ~SND (EL i params) /\
        FST (EL i params) = n /\ FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) /\
        b = w2n (EL ((if has_rb then 1 else 0) + i) argv))
Proof
  strip_tac >>
  `is_nr = F /\ ss' = ss` by
    fs[package_internal_fn_def, set_internal_package_target_def] >>
  gvs[] >> drule_all gas_invoke_entry_decode >> strip_tac >>
  drule_all body_inv_invoked_internal_code >> strip_tac >>
  qpat_x_assum `label = lbl` SUBST_ALL_TAC >>
  drule_all selected_internal_body_boundary >> strip_tac >> gvs[] >>
  drule_all intcall_entry_package_inputs >> strip_tac >>
  `fn_inst_ids_distinct callee` by
    (drule lookup_function_MEM >> simp[MEM_SPLIT] >> strip_tac >>
     gvs[ctx_inst_ids_distinct_def, fn_inst_ids_distinct_def,
         MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  drule_all internal_entry_counted_resources >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  qexistsl_tac [`after`, `mr`] >> simp[arithmeticTheory.ADD_COMM]
QED

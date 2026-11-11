(* Selected code interval for the function actually entered by INVOKE. *)
Theory bodyIntCallInvokedCode
Ancestors
  bodyIntCallPackageInputs bodyIntCallSelectedCode bodyIntCallInvokeEntry bodySim

Theorem body_inv_invoked_internal_code:
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
  label = lbl /\
  ?before old st0 after setup first phi_state.
    new_block label before = (old,st0) /\
    compile_internal_function ce params has_rb is_nr key trans view ctor ilen
      ss' rt st0 = ((),after) /\
    fn_has_code st0 after callee /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
    ctx_inst_ids_distinct ctx /\
    setup_callee callee argv t = SOME setup /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    eval_phis setup first.bb_instructions = OK phi_state /\
    ~phi_state.vs_halted /\
    entered = phi_state with vs_inst_idx :=
      phi_prefix_length first.bb_instructions
Proof
  strip_tac >>
  drule_all gas_invoke_entry_decode >> strip_tac >>
  drule_all (cj 1 intcall_entry_package_inputs) >> strip_tac >>
  `cenv.ce_is_ctor = cx.in_deploy` by gvs[body_inv_def] >>
  gvs[] >> drule_all body_inv_selected_internal_code >> strip_tac >>
  gvs[] >> metis_tac[]
QED

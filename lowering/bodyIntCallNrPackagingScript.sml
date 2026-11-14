(* Guarded internal callee packaging over the joint statement producer. *)
Theory bodyIntCallNrPackaging
Ancestors
  bodyIntCallNrBodyCode bodyIntCallNrInvokedCode bodyIntCallNrNormalLanding
  bodyIntCallNrEntryReady bodyIntCallNrBodyOutcome bodyIntCallEntryPhi
  bodyIntCallPackageControl bodyIntCallPackageExitFields
  bodyIntCallPackageBodyControl bodyIntCallJointPackage
  compileVyper compileEnv venomExecProps venomWf list vyperInterpreter
Libs
  monadsyntax

Theorem selected_internal_guarded_boundary:
  body_inv tops ctx caller_ce cx /\
  lookup_function label ctx.ctx_functions = SOME callee /\
  new_block label before = (old,entry) /\
  compile_internal_function ce params has_rb nr key trans view ctor ilen
    ss rt entry = ((),final) /\ fn_has_code entry final callee /\
  setup_callee callee argv caller = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions ==>
  ?ce2 rpc imm prelock body_start body_env body_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,rpc,imm),prelock) /\
    (if nr then compile_nonreentrant_lock key trans view prelock
     else ((),prelock)) = ((),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    fn_has_code entry prelock callee /\ fn_has_code prelock body_start callee /\
    fn_has_code body_start body_end callee /\ fn_has_code body_end final callee /\
    entry.cs_current_insts = [] /\
    entry.cs_current_bb = (HD callee.fn_blocks).bb_label /\ entered = setup /\
    (~block_is_terminated body_end ==>
      ?su. (if nr then compile_nonreentrant_unlock key trans view body_end
            else ((),body_end)) = ((),su) /\
        (case rt of NONE => emit_inst RET [rpc] [] su
                  | SOME ty => emit_inst INVALID [] [] su) = ((),final))
Proof
  strip_tac >> drule_all internal_function_guarded_body_code >> strip_tac >>
  drule_all body_inv_function_entry_label >> strip_tac >>
  `entry.cs_current_insts = [] /\
   entry.cs_current_bb = (HD callee.fn_blocks).bb_label` by gvs[new_block_def] >>
  `entered = setup` by (irule internal_entry_phi_landing >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >> simp[]
QED

Theorem internal_package_guard_metadata:
  set_internal_package_target target
    (package_internal_fn tops T (K global_nonreentrant_slot) ctor ilen
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (label,ce,params,has_rb,is_nr,key,trans,view,ctor',ilen',ss',rt) ==>
  is_nr = nr /\ key = global_nonreentrant_slot /\ trans = T /\
  view = (mut = View) /\ ss' = ss /\
  ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View)
Proof
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, is_view_mut_def] >> strip_tac >> gvs[]
QED

(* Diagnostic: the supported-header whitelist does not supply the source
   typing header condition needed to equate the two guard view flags. *)
Theorem supported_guard_header_gap:
  supported_declaration_header tops
    (FunctionDecl Internal Pure T F name [] [] NoneT []) /\
  ~function_header_ok Internal Pure T F name [] [] NoneT
Proof
  simp[supportedDeclsTheory.supported_function_header_contract,
       supportedDeclsTheory.supported_function_return_def,
       supportedTypesTheory.supported_return_type_def,
       vyperTypeContractTheory.function_header_ok_def]
QED

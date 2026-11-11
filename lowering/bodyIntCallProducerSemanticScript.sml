(* Actual-entry semantic bridges for the joint statement producer. *)
Theory bodyIntCallProducerSemantic
Ancestors
  bodyIntCallActualEntrySemantic bodyIntCallResourceEntry bodySimEntry
  bodyIntCallJointContract bodyIntCallEntryInputs bodyIntCallBodyTyping
  bodyIntCallSource bodySim compileVyper moduleLowering intCallCallee
  bodyIntCallActualEntryFields compileEnv

Theorem body_inv_packaged_actual_entry:
  body_inv tops ctx caller cx /\
  set_internal_package_target caller.ce_target
    (package_internal_fn tops use_trans nkeys caller.ce_is_ctor imm_size
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,pc,imm),st1) ==>
  body_inv tops ctx (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    (cx with stk updated_by CONS owner)
Proof
  strip_tac >> drule compile_internal_entry_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  `body_inv tops ctx
     (build_compile_env tops Internal mut name args ret ss use_trans
       with <|ce_target := caller.ce_target; ce_is_ctor := caller.ce_is_ctor|>)
     (cx with stk updated_by CONS owner)` by
    (irule body_inv_build_internal_env >> irule body_inv_push_stack >> simp[]) >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def, body_inv_def] >> metis_tac[]
QED

(* Presence alone suffices for this nonfailure fact; no namespace uniqueness
   is needed, even when an earlier declaration shadows the given body. *)
Theorem internal_decl_lookup_not_none:
  !tops src name fm nr raw args dflts ret ss.
    MEM (FunctionDecl Internal fm nr raw name args dflts ret ss) tops ==>
    vyperInterpreter$lookup_function src name Internal tops <> NONE
Proof
  Induct_on `tops` >- simp[] >>
  gen_tac >> gen_tac >> Cases_on `h` >>
  simp[vyperInterpreterTheory.lookup_function_def] >>
  rpt strip_tac >> gvs[]
  >~ [`vyperInterpreter$lookup_function _ _ Internal (VariableDecl vis _ _ _ _ :: _)`] >-
    (Cases_on `vis` >> gvs[vyperInterpreterTheory.lookup_function_def] >>
     metis_tac[])
  >~ [`vyperInterpreter$lookup_function _ _ Internal (HashMapDecl vis _ _ _ _ _ :: _)`] >-
    (Cases_on `vis` >> gvs[vyperInterpreterTheory.lookup_function_def] >>
     metis_tac[]) >>
  metis_tac[]
QED

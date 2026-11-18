Theory bodyFullShadowBodyInv
Ancestors
  gasShadowUnit gasShadowState gasShadow compileVyper vyperCompiler compileEnv
  moduleLowering fragExec venomInst venomWf vyperAST bodySim list

(* Each selected internal function has paired code from its real and shadow
   compiler runs. The two contexts stay fixed through the body induction. *)
Definition shadow_body_inv_def:
  shadow_body_inv tops ctx shadow_ctx <=>
    gas_shadow_context ctx shadow_ctx /\
    !is_ctor mut nr rr name args dflts ret ss callee.
      MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
      lookup_function
        (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
           is_ctor)
        ctx.ctx_functions = SOME callee ==>
      ?rpolicy unit label ce params has_rb nr' key trans view ctor ilen
       compiled_ss rt before old entry final sf beforeS oldS entryS finalS.
        (if is_ctor then
           ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
         else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
        ctx = unit.cu_context /\
        set_internal_package_target rpolicy.rpol_target
          (package_internal_fn tops T (K global_nonreentrant_slot) is_ctor
            (if is_ctor then
               compute_immutables_len
                 (get_struct_fields (make_struct_fields_map tops)) tops
             else 0)
            (mut,nr,rr,name,args,dflts,ret,ss)) =
          (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
           compiled_ss,rt) /\
        compiled_ss = ss /\
        new_block label before = (old,entry) /\
        compile_internal_function ce params has_rb nr' key trans view ctor ilen
          compiled_ss rt entry = ((),final) /\
        fn_has_code entry final callee /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
        ctx_inst_ids_distinct ctx /\
        MEM sf shadow_ctx.ctx_functions /\
        gas_shadow_function callee sf /\
        new_block label beforeS = (oldS,entryS) /\
        compile_internal_function ce params has_rb nr' key trans view ctor ilen
          (MAP gas_shadow_stmt compiled_ss) rt entryS = ((),finalS) /\
        gas_shadow_state entry entryS /\
        gas_shadow_state final finalS /\
        fn_has_code entryS finalS sf
End

Theorem shadow_body_inv_callee_code:
  !tops ctx shadow_ctx cenv cx mut nr rr name args dflts ret ss callee.
    shadow_body_inv tops ctx shadow_ctx /\
    body_inv tops ctx cenv cx /\ gas_shadow_context ctx shadow_ctx /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
    lookup_function
      (internal_fn_label (build_func_ids 0 tops name) name (MAP SND args)
         cx.in_deploy)
      ctx.ctx_functions = SOME callee ==>
    ?rpolicy unit label ce params has_rb nr' key trans view ctor ilen
     compiled_ss rt before old entry final sf beforeS oldS entryS finalS.
      (if cx.in_deploy then
         ?rbc. lower_vyper_deploy_unit tops rpolicy rbc = SOME unit
       else lower_vyper_runtime_unit tops rpolicy = SOME unit) /\
      ctx = unit.cu_context /\
      set_internal_package_target rpolicy.rpol_target
        (package_internal_fn tops T (K global_nonreentrant_slot) cx.in_deploy
          (if cx.in_deploy then
             compute_immutables_len
               (get_struct_fields (make_struct_fields_map tops)) tops
           else 0)
          (mut,nr,rr,name,args,dflts,ret,ss)) =
        (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) /\
      compiled_ss = ss /\
      new_block label before = (old,entry) /\
      compile_internal_function ce params has_rb nr' key trans view ctor ilen
        compiled_ss rt entry = ((),final) /\
      fn_has_code entry final callee /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
      ctx_inst_ids_distinct ctx /\
      MEM sf shadow_ctx.ctx_functions /\
      gas_shadow_function callee sf /\
      new_block label beforeS = (oldS,entryS) /\
      compile_internal_function ce params has_rb nr' key trans view ctor ilen
        (MAP gas_shadow_stmt compiled_ss) rt entryS = ((),finalS) /\
      gas_shadow_state entry entryS /\
      gas_shadow_state final finalS /\
      fn_has_code entryS finalS sf
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `shadow_body_inv _ _ _`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [shadow_body_inv_def]) >>
  disch_then (qspecl_then
    [`cx.in_deploy`, `mut`, `nr`, `rr`, `name`, `args`, `dflts`, `ret`, `ss`,
     `callee`] mp_tac) >>
  simp[]
QED

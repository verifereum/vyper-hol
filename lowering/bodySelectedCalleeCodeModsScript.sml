Theory bodySelectedCalleeCodeMods
Ancestors
  bodyFullShadowBodyInv

(* Select the two compilation runs for the function already found by lookup. *)
Theorem selected_callee_paired_code_mods:
  !mods exps cx ctx shadow_ctx src tops vis mut nr rr name args dflts ret ss callee.
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    ALOOKUP mods src = SOME tops /\
    (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
    lookup_function
      (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,name)))
         (nsid_to_string (src,name)) (MAP SND args) cx.in_deploy)
      ctx.ctx_functions = SOME callee ==>
    ?rpolicy unit label ce params has_rb nr' key trans view ctor ilen
     compiled_ss rt before old entry final sf beforeS oldS entryS finalS.
      (if cx.in_deploy then
         ?rbc. lower_vyper_deploy_unit_mods mods exps rpolicy rbc = SOME unit
       else lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit) /\
      ctx = unit.cu_context /\
      set_internal_package_target rpolicy.rpol_target
        (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy
          (if cx.in_deploy then imm_len_mods mods else 0)
          (src,subst_consts_fn_mods (consts_env_mods mods)
            (mut,nr,rr,name,args,dflts,ret,ss))) =
        (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
         compiled_ss,rt) /\
      compiled_ss = subst_consts_stmts_mods (consts_env_mods mods) ss /\
      new_block label before = (old,entry) /\
      compile_internal_function ce params has_rb nr' key trans view ctor ilen
        compiled_ss rt entry = ((),final) /\
      fn_has_code entry final callee /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
      ctx_inst_ids_distinct ctx /\
      MEM sf shadow_ctx.ctx_functions /\
      gas_shadow_function callee sf /\
      new_block label beforeS = (oldS,entryS) /\
      compile_internal_function (gas_shadow_env T ce) params has_rb nr' key
        trans view ctor ilen (MAP gas_shadow_stmt compiled_ss) rt entryS =
        ((),finalS) /\
      gas_shadow_state entry entryS /\
      gas_shadow_state final finalS /\
      fn_has_code entryS finalS sf
Proof
  rpt gen_tac >> simp[shadow_body_inv_mods_def] >> strip_tac >>
  first_x_assum irule >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`tops`, `vis`] >> simp[]
QED

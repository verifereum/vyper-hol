Theory bodyFullShadowBodyInv
Ancestors
  gasShadowUnit gasShadowState gasShadow gasShadowCompileBase compileVyper vyperCompiler compileEnv
  moduleLowering fragExec venomInst venomWf vyperAST bodySim list
  bodyInvSplit compileUnit constSubst constSubstMods bodyPtrDefs gasContext ptrDiscipline ptrSafeRun
  loweringStateRelDefs venomState vyperState vyperContext
  alist finite_map pred_set words combin

(* Each selected internal function has paired code from its real and shadow
   compiler runs. The two contexts stay fixed through the body induction. *)
Definition shadow_body_inv_mods_def[nocompute]:
  shadow_body_inv_mods mods exps ctx shadow_ctx <=>
    gas_shadow_context ctx shadow_ctx /\
    !src tops is_ctor vis mut nr rr name args dflts ret ss callee.
      ALOOKUP mods src = SOME tops /\
      (vis = Internal \/ (is_ctor /\ src <> NONE /\ vis = Deploy)) /\
      MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
      lookup_function
        (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,name)))
           (nsid_to_string (src,name)) (MAP SND args) is_ctor)
        ctx.ctx_functions = SOME callee ==>
      ?rpolicy unit label ce params has_rb nr' key trans view ctor ilen
       compiled_ss rt before old entry final sf beforeS oldS entryS finalS.
        (if is_ctor then
           ?rbc. lower_vyper_deploy_unit_mods mods exps rpolicy rbc = SOME unit
         else lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit) /\
        ctx = unit.cu_context /\
        set_internal_package_target rpolicy.rpol_target
          (package_internal_fn_unit mods T (K global_nonreentrant_slot) is_ctor
            (if is_ctor then imm_len_mods mods else 0)
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
End

Definition shadow_body_inv_split_def[nocompute]:
  shadow_body_inv tops ctx shadow_ctx <=>
    shadow_body_inv_mods [(NONE,tops)] [] ctx shadow_ctx
End

Theorem shadow_body_inv_def:
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
            (subst_consts_fn (module_consts_env tops [])
              (mut,nr,rr,name,args,dflts,ret,ss))) =
          (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
           compiled_ss,rt) /\
        compiled_ss = subst_consts_stmts (module_consts_env tops []) ss /\
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
  simp[shadow_body_inv_split_def, shadow_body_inv_mods_def,
       ALOOKUP_def, optionTheory.FORALL_OPTION, nsid_to_string_def,
       build_func_ids_mods_singleton, lower_vyper_runtime_unit_mods_singleton,
       lower_vyper_deploy_unit_mods_singleton, package_internal_fn_unit_singleton,
       imm_len_mods_singleton, immSectionDeadTheory.imm_len_def,
       consts_env_mods_singleton, subst_consts_fn_mods_singleton,
       subst_consts_mods_singleton]
QED

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
          (subst_consts_fn (module_consts_env tops [])
            (mut,nr,rr,name,args,dflts,ret,ss))) =
        (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) /\
      compiled_ss = subst_consts_stmts (module_consts_env tops []) ss /\
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `shadow_body_inv _ _ _`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [shadow_body_inv_def]) >>
  disch_then (qspecl_then
    [`cx.in_deploy`, `mut`, `nr`, `rr`, `name`, `args`, `dflts`, `ret`, `ss`,
     `callee`] mp_tac) >>
  simp[]
QED

Definition dead_lo_ok_mods_def[nocompute]:
  dead_lo_ok_mods H D lo cenv cx <=>
    dead_sub (cx_dead H cx) D /\
    D.d_stor = (cx_dead H cx).d_stor /\ D.d_trans = (cx_dead H cx).d_trans /\
    (cenv.ce_is_ctor ==> !im. D.d_imm im = UNIV) /\
    lo = (if cenv.ce_is_ctor then imm_len_mods cenv.ce_modules else 0)
End

Theorem dead_lo_ok_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] ==>
  (dead_lo_ok_mods H D lo cenv cx <=> dead_lo_ok H D lo cenv cx)
Proof
  simp[dead_lo_ok_mods_def, dead_lo_ok_def, imm_len_mods_singleton]
QED

Definition ghost_inv_at_mods_def[nocompute]:
  ghost_inv_at_mods D lo d cenv (cx : evaluation_context) (es : evaluation_state) G tn
    (s : venom_state) <=>
    (!name entry p sz.
       lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
               mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory entry.type entry.value (w2n w) mem) /\
    return_buf_ptr d cenv G tn s /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            op_taint tn (Var x) = {}) /\
    stor_taint_ok_at D tn s /\
    (!i. i < lo /\ i IN tn.t_mem ==>
         imm_section_dead_mods cenv (mem_bytes_at 0 lo s.vs_memory) i) /\
    (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
         FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next
End

Theorem ghost_inv_at_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] ==>
  (ghost_inv_at_mods D lo d cenv cx es G tn s <=> ghost_inv_at D lo d cenv cx es G tn s)
Proof
  strip_tac >>
  `!sec j. imm_section_dead_mods cenv sec j <=>
           imm_section_dead (cx_tops cx) sec j` by
    (rpt gen_tac >> irule imm_section_dead_mods_singleton >> simp[]) >>
  simp[ghost_inv_at_mods_def, ghost_inv_at_def]
QED

(* The caller-side staging contract of intcall_args_stage_selected.
   The source context belongs to the phase, so the same client rule can
   be used for supplied arguments and for defaults. *)
Theory bodyFullIntCallStageClient
Ancestors
  bodyFullPreds bodyPtrDefs exprSimHypsDefs exprSimDefs exprLoweringProps
  gasContext gasSummary gasExplicitSites gasShadowState gasShadowUnit
  fragGasOrigin fragGasPath unitTransformDefs
  vyperStorageTrace vyperStorageFootprint
  ptrDiscipline allocaHistory valueEncodingDefs valueEncoding
  vyperTyping vyperTypeSystem vyperInterpreter vyperState
  venomState venomInst compileEnv exprLowering

Definition intcall_stage_pre_def:
  intcall_stage_pre
    (keep_sites,clean_words,DF,lo,d,ctx,shadow_ctx,
     PG : (num # num) option list,func,shadow_func,tops,st0)
    (sa,s0,es0,G0,tn0)
    (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
    (ops,ws,vals,ptys,pflags,pin) (esi,s,G,tn) f P R <=>
    body_inv tops ctx cenv chi /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] chi tenv esi /\
    expr_sim_inv cenv chi tenv esi /\
    EVERY (\e. expr_body_pre cenv chi tenv e esi) es /\
    body_exprs_full_ok chi es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv chi)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre cenv chi tenv e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv chi) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si =
      (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shadow_si = (newops,shadow_sf) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv si /\
    ((ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u)) /\
    (!H. dead_lo_ok H (DF H) lo cenv chi) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at si x) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (vyperState$bind (eval_exprs chi es) f)
      (P : 'a + exception -> bool) esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    (! (H : (bool # bytes32 # type_value) list # num list)
       (res : 'a + exception) ee (gt : (string, num # num) fmap # taint) r.
       expr_exit res r /\ halt_exit H chi ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) /\
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (keep_sites ==> !j. j < LENGTH ops /\ ~EL j pflags ==>
       ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
         FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
         sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
         32 <= cap /\
         ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
           inst.inst_id = aid) /\
    (keep_sites ==> !i j b k c l.
       i < j /\ j < LENGTH ops /\ ~EL i pflags /\ ~EL j pflags /\
       op_prov G (EL i ops) = SOME (b,k) /\ op_prov G (EL j ops) = SOME (c,l) ==>
       regions_disjoint b k c l) /\
    (!j rt. j < LENGTH ops /\
       evaluate_type (get_tenv chi) (EL j ptys) = SOME rt ==>
       value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
       val_footprint rt (EL j vals) <= type_memory_size rt /\
       (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
         (clean_words ==> op_prov G (EL j ops) = NONE)) /\
       (~EL j pflags ==>
         ?b cap aid.
           op_prov G (EL j ops) = SOME (b,cap) /\
           FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
           sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
           lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
           w2n (EL j ws) + type_memory_size rt <= b+cap /\
           (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
           (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
             b+cap <= lb \/ lb+sz <= b) /\
           (case pin of NONE => T | SOME (rb,pb,pk) =>
             b+cap <= pb \/ pb+pk <= b))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
       lookup_var rb s = SOME (n2w b) /\
       FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
       not_fresh_at si rb /\
       (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon chi st0 H esi.storage_trace ==>
       stmt_state_rel H ctx func cenv chi esi s /\
       storage_well_formed_on chi esi (FST H) /\
       ghost_inv_at (DF H) lo d cenv chi esi G tn s)
End

Definition intcall_stage_landing_def:
  intcall_stage_landing
    (keep_sites,clean_words,DF,lo,d,ctx,shadow_ctx,PG : (num # num) option list,
     func,shadow_func : ir_function,tops : toplevel list,st0)
    (sa,s0,es0,G0,tn0)
    (cenv,chi,tenv,es,flags,dtys,si : compile_state,sf,
     shadow_si : compile_state,shadow_sf : compile_state,newops)
    (ops,ws : bytes32 list,vals,ptys,pflags,pin)
    (esi : evaluation_state,s,G : (string, num # num) fmap,tn : taint)
    f P (marks,xs,ee,t,G1,tn1) <=>
    (!tail. eval_exprs chi es
       (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL xs, ee with gas_obs := tail)) /\
    gas_origin_path T (gas_explicit_sites ctx shadow_ctx) ctx func s marks (OK t) /\
    gas_path ctx func s (LENGTH marks) (OK t) /\
    storage_trace_domain chi st0 ee.storage_trace /\
    LENGTH xs = LENGTH es /\ expr_sim_inv cenv chi tenv ee /\
    (?ws1.
      LENGTH ws1 = LENGTH (ops ++ newops) /\
      LENGTH (vals ++ xs) = LENGTH (ops ++ newops) /\
      LENGTH (ptys ++ dtys) = LENGTH (ops ++ newops) /\
      LENGTH (pflags ++ flags) = LENGTH (ops ++ newops) /\
      eval_operands (ops ++ newops) t = SOME ws1 /\
      EVERY (\op. op_taint tn1 op = {}) (ops ++ newops) /\
      (!x. MEM (Var x) (ops ++ newops) ==> not_fresh_at sf x) /\
      (keep_sites ==> !j. j < LENGTH (ops ++ newops) /\ ~EL j (pflags ++ flags) ==>
        ?b cap aid. op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
          FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
          sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
          32 <= cap /\
          ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
            inst.inst_id = aid) /\
      (keep_sites ==> !i j b k c l.
        i < j /\ j < LENGTH (ops ++ newops) /\
        ~EL i (pflags ++ flags) /\ ~EL j (pflags ++ flags) /\
        op_prov G1 (EL i (ops ++ newops)) = SOME (b,k) /\
        op_prov G1 (EL j (ops ++ newops)) = SOME (c,l) ==>
        regions_disjoint b k c l) /\
      (!j rt. j < LENGTH (ops ++ newops) /\
        evaluate_type (get_tenv chi) (EL j (ptys ++ dtys)) = SOME rt ==>
        value_has_type rt (EL j (vals ++ xs)) /\
        val_wf rt (EL j (vals ++ xs)) /\
        val_footprint rt (EL j (vals ++ xs)) <= type_memory_size rt /\
        (EL j (pflags ++ flags) ==>
          EL j ws1 = typed_val_to_w256 rt (EL j (vals ++ xs)) /\
          (clean_words ==> op_prov G1 (EL j (ops ++ newops)) = NONE)) /\
        (~EL j (pflags ++ flags) ==>
          ?b cap aid.
            op_prov G1 (EL j (ops ++ newops)) = SOME (b,cap) /\
            FLOOKUP t.vs_allocas aid = SOME (b,cap) /\
            sa.cs_next_id <= aid /\ aid < sf.cs_next_id /\
            lo <= b /\ b+cap <= t.vs_alloca_next /\ b <= w2n (EL j ws1) /\
            w2n (EL j ws1) + type_memory_size rt <= b+cap /\
            (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
              val_in_memory rt (EL j (vals ++ xs)) (w2n (EL j ws1)) mem) /\
            (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
              b+cap <= lb \/ lb+sz <= b) /\
            (case pin of NONE => T | SOME (rb,pb,pk) =>
              b+cap <= pb \/ pb+pk <= b)))) /\
    (case pin of NONE => T | SOME (rb,b,k) =>
       FLOOKUP G1 rb = SOME (b,k) /\ op_taint tn1 (Var rb) = {} /\
       lookup_var rb t = SOME (n2w b) /\
       FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
       sa.cs_next_id < sf.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
       not_fresh_at sf rb /\
       (!n lb sz. local_region cenv ee.scopes t n lb sz ==>
         b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 ee sa s0 t /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1 /\
    alloca_history func t /\ sa.cs_next_id <= sf.cs_next_id /\
    sa.cs_next_var <= sf.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
       local_region cenv ee.scopes t n b sz) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM ee.scopes /\
    return_buf_frame d cenv sf t /\ ~t.vs_halted /\
    t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    (!H. valid_horizon chi st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv chi ee t /\
       storage_well_formed_on chi ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv chi ee G1 tn1 t) /\
    gas_admissible (f xs) P ee
End

Definition intcall_stage_run_def:
  intcall_stage_run Seg J (z : compile_state) cfg orig
    (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
    prior (esi,s,G,tn) f P
    (Q : (bool # bytes32 # type_value) list # num list -> 'a + exception ->
         evaluation_state -> (string, num # num) fmap -> taint -> venom_state -> bool)
    R <=>
    (intcall_stage_pre cfg orig
       (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
       prior (esi,s,G,tn) f P R /\
     (!marks xs ee t G1 tn1.
       intcall_stage_landing cfg orig
         (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
         prior (esi,s,G,tn) f P (marks,xs,ee,t,G1,tn1) /\
       Seg si sf s marks t ==>
       J chi sf z (f xs) (ee,t,G1,tn1) Q R) ==>
     J chi si z (vyperState$bind (eval_exprs chi es) f) (esi,s,G,tn) Q R)
End

Theorem intcall_stage_run_apply:
  !chi. intcall_stage_run Seg J z cfg orig
    (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
    prior (esi,s,G,tn) f P Q R ==>
  intcall_stage_pre cfg orig
    (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
    prior (esi,s,G,tn) f P R ==>
  (!marks xs ee t G1 tn1.
    intcall_stage_landing cfg orig
      (cenv,chi,tenv,es,flags,dtys,si,sf,shadow_si,shadow_sf,newops)
      prior (esi,s,G,tn) f P (marks,xs,ee,t,G1,tn1) /\
    Seg si sf s marks t ==>
    J chi sf z (f xs) (ee,t,G1,tn1) Q R) ==>
  J chi si z (vyperState$bind (eval_exprs chi es) f) (esi,s,G,tn) Q R
Proof
  simp[intcall_stage_run_def, GSYM AND_IMP_INTRO]
QED

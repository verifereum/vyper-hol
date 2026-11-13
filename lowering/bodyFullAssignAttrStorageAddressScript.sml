(* The literal storage-field address is computed before the RHS is forced.
   Keep the expression's original compile boundary in its value post. *)
Theory bodyFullAssignAttrStorageAddress
Ancestors
  bodyFullGhostFrame bodyFullUnwrapRun typedCopyOriginPtrBase
  fragGasOriginPtrDead fragGasOriginPtr bodyPtrDefs exprSimVVFrame
  exprSimMemDefs loweringPosts exprOperandVar exprSimProps
  exprLoweringProps exprLowering emitHelperProps emitHelper freshWrites
  ptrDiscipline venomState venomInst allocaHistory loweringStateRelDefs
  vyperStorageFootprint compileEnv typedMemoryCopy finite_map list
  pred_set ASCIInumbers arithmetic combin venomExecSemantics context

Theorem storage_field_address_full:
  compile_expr cenv ty e sa = (vv,sm) /\
  emit_op ADD [Lit root; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee raw vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee G tn s /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) s = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?out q HG tf.
    dst = Var out /\ not_fresh_at sn out /\
    q = (update_var out (root + n2w off) s
           with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK q,HG,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee raw vv q /\
       ghost_inv_at (DF H) lo d cenv cx ee HG tf q) /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw vv q /\
    ptr_vv_ok cx (post_value_type cenv e) raw vv ee HG tf q /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx raw ee = (INL v,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) q = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==>
                       val_in_memory rt v (w2n w) mem)) /\
    ghost_kept_at lo cenv es sa Gi ti s0 HG tf /\
    alloca_history func q /\
    eval_operand dst q = SOME (root + n2w off) /\ op_taint tf dst = {} /\
    (!x. not_fresh_at sm x ==>
         lookup_var x q = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `allocas_from lo s /\ alloca_inv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     fs[ghost_inv_at_def, vv_post_def, stmt_state_rel_def]) >>
  `?out q HG tf.
     dst = Var out /\ not_fresh_at sn out /\
     q = (update_var out (root + n2w off) s
            with vs_inst_idx := SUC s.vs_inst_idx) /\
     HG = step_prov PG G
       (mk_inst sm.cs_next_id ADD [Lit root;Lit (n2w off)] [out])
       (update_var out (root + n2w off) s) /\
     tf = step_taint
       (mk_inst sm.cs_next_id ADD [Lit root;Lit (n2w off)] [out]) s
       (update_var out (root + n2w off) s) tn /\
     gas_origin_ptr_path
       (<|d_stor := K (K {}); d_trans := K (K {});
          d_imm := K {}; d_ret := K {}|>,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK q,HG,tf) /\
     eval_operand dst q = SOME (root + n2w off) /\
     ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
     q.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (mp_tac (typed_copy_origin_ptr_binop_path |> Q.INST
       [`opc` |-> `ADD`, `left` |-> `Lit root`, `right` |-> `Lit (n2w off)`,
        `a` |-> `sm`, `b` |-> `sn`, `op` |-> `dst`,
        `x` |-> `root`, `y` |-> `n2w off`, `w` |-> `root + n2w off`,
        `D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {}|>`]) >>
     simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `out = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `~not_fresh_at sm out /\
   (!x. not_fresh_at sm x ==> x <> out) /\
   (!x. not_fresh_at sa x ==> not_fresh_at sm x)` by
    (simp[not_fresh_at_def, toString_11] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   op_taint tf (Var out) = {} /\
   (!x. x <> out ==> FLOOKUP HG x = FLOOKUP G x /\
                       op_taint tf (Var x) = op_taint tn (Var x))` by
    (mp_tac (typed_copy_origin_ptr_binop_ghost_frame |> Q.INST
       [`opc` |-> `ADD`, `left` |-> `Lit root`, `right` |-> `Lit (n2w off)`,
        `id` |-> `sm.cs_next_id`, `w` |-> `root + n2w off`]) >> simp[]) >>
  `!x. not_fresh_at sm x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
   op_taint tf (vv_operand vv) = op_taint tn (vv_operand vv) /\
   op_prov HG (vv_operand vv) = op_prov G (vv_operand vv)` by
    (Cases_on `vv_operand vv` >>
     gvs[eval_operand_def, op_taint_def, op_prov_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee raw vv q /\
     ghost_inv_at (DF H) lo d cenv cx ee HG tf q` by
    (qx_gen_tac `H` >> strip_tac >> conj_tac
     >- (simp[] >> irule vv_post_update_var >> simp[] >>
         qexists_tac `sm` >> simp[] >> metis_tac[]) >>
     irule ghost_inv_at_exterior_frame >> simp[] >>
     qexistsl_tac [`G`, `ee`, `s`, `sa`, `tn`] >>
     fs[update_var_def] >> metis_tac[]) >>
  `q.vs_allocas = s.vs_allocas /\
   q.vs_alloca_next = s.vs_alloca_next /\ q.vs_memory = s.vs_memory /\
   q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_call_ctx = s.vs_call_ctx` by simp[update_var_def] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw vv q` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`vv_store_bound _ _ _ _ _ _ s`,
        `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s`,
        `q.vs_alloca_next = s.vs_alloca_next`] >>
     rpt (pop_assum kall_tac) >> Cases_on `vv` >>
     simp[vv_store_bound_def, vv_operand_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> FLOOKUP HG x = FLOOKUP G x` by metis_tac[] >>
  `ptr_vv_ok cx (post_value_type cenv e) raw vv ee HG tf q` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_vv_ok _ _ _ _ _ G tn s`,
        `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s`,
        `op_taint tf (vv_operand vv) = op_taint tn (vv_operand vv)`,
        `op_prov HG (vv_operand vv) = op_prov G (vv_operand vv)`,
        `!x. vv_operand vv = Var x ==> FLOOKUP HG x = FLOOKUP G x`,
        `tf.t_mem = tn.t_mem`, `tf.t_stor = tn.t_stor`,
        `tf.t_trans = tn.t_trans`, `q.vs_memory = s.vs_memory`,
        `q.vs_accounts = s.vs_accounts`, `q.vs_transient = s.vs_transient`,
        `q.vs_call_ctx = s.vs_call_ctx`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `vv` >>
     fs[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, vv_operand_def] >>
     metis_tac[]) >>
  `ghost_kept_at lo cenv es sa Gi ti s0 HG tf` by
    (irule ghost_kept_at_clean_suffix >> simp[] >>
     qexistsl_tac [`G`, `tn`] >> simp[] >> metis_tac[]) >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `alloca_history func q` by
    (qspecl_then
       [`[mk_inst sm.cs_next_id ADD [Lit root;Lit (n2w off)] [out]]`,
        `sm`, `sn`, `s`, `update_var out (root + n2w off) s`]
       mp_tac emitted_alloca_history >>
     (impl_tac >-
       simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
            step_inst_base_def, exec_pure2_def, eval_operand_def]) >> simp[ADD1]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK q,HG,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
              eval_operand (vv_operand vv) q = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _`,
        `eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s`,
        `tf.t_mem = tn.t_mem`, `q.vs_memory = s.vs_memory`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` drule_all >>
     strip_tac >> qexists_tac `v` >> fs[]) >>
  qexistsl_tac [`out`, `q`, `HG`, `tf`] >> asm_rewrite_tac[] >> metis_tac[]
QED

(* The slot-copy run and the other-form run are consumed at their own
   endpoints, before the choice of dead mask or storage horizon. *)
Theory entryStageUnwrapScoped
Ancestors
  entryStageSlotUnwrap entryStageUnwrapOther bodyFullUnwrapSlotSelectedPost
  bodyFullHashKeccakFixed createSizePrefixReplay createSizeCutRegion
  createSizeLocationCode venomExecSemantics fragGasOriginPtr loweringPosts
  bodyPtrDefs exprSimMemDefs venomMemDefs compileEnv context exprLowering
  ptrDiscipline vyperStorageFootprint finite_map

Theorem stage_unwrap_origin_ptr_scoped:
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (!bb i. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH sc.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids sb sc) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    create_expr_prefix sb sc explicit ctx func s [] z /\ create_operand_at sc z /\
    read_result cx tv ee = (INL v, ee) /\
    (!ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
      (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
       p.ptr_location = LocCode) ==>
      vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
        (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type cenv e) ==>
     vv_at cenv cx (post_value_type cenv e) sa sm ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z \/
     vv_at cenv cx (post_value_type cenv e) sb sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `!t p. vv = LocatedValue t p /\
                   (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
                   is_word_type t`
  >- (mp_tac stage_unwrap_other_origin_scoped >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  pop_assum mp_tac >> simp_tac bool_ss [NOT_FORALL_THM, NOT_IMP] >>
  disch_then (qx_choosel_then [`t`,`p`] (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >> simp[vv_post_def]) >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  mp_tac (Q.INST [`exit_ok` |-> `\z. create_expr_prefix sb sc explicit ctx func s [] z /\
                                     create_operand_at sc z`] unwrap_slot_copy_post_with_exit) >>
  BETA_TAC >>
  (impl_tac >-
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all stage_ensure_slot_origin_scoped >>
     disch_then (qspecl_then [`explicit`,`PG`,`G`]
       (qx_choosel_then [`root`,`wd`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`z`,`mid`,`buf`,`u`]
         strip_assume_tac)) >>
     qexistsl [`root`,`wd`,`a`,`G0`,`tn0`,`Gf`,`tnf`,`z`,`mid`,`buf`,`u`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl [`v`,`z`,`G'`,`tn'`] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> simp[]
QED

(* Execute the word read at the place returned by a linked Pop. *)
Theory bodyPopWordLoadMods
Ancestors
  bodyIfExpWordReadMods bodyPopBindMods bodyPopInputsMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullUnwrapRun
  bodyFullPathHistory bodyPtrSignedConvertSourceFrame
  exprSimPopNestedBase exprSimUnwrap exprOperandVar
  fragGasOriginPtrDead representationCleanPtr reasonSourceProps
  loweringPosts loweringStateRelDefs exprSimProps bodyInvSplit
  bodyPtrDefs ptrDiscipline exprLowering exprLoweringProps freshWrites
  stateRelProj emitHelperProps compileEnv context vyperStorageFootprint
  vyperState venomInst venomState finite_map arithmetic words list

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {}|>``;

val pop_word_frame = ``
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP (Gf:string |-> num # num) x = FLOOKUP (G:string |-> num # num) x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_mem = tn.t_mem /\
    tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm``;

Theorem pop_word_load_mods:
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\
  copy_old_operand sm p.ptr_operand /\
  post_value_type ce (Pop ann bt) = t /\
  is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_post_mods H ctx func ce cx (Pop ann bt) es sa sm s0 ee tv
    (LocatedValue t p) s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx t (lowered_value_type ce (Pop ann bt)) ee tv
    (LocatedValue t p) s /\
  ptr_vv_ok cx t tv (LocatedValue t p) ee G tn s /\
  (ce.ce_is_ctor /\ p.ptr_location = LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v u Gf tf.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\
    op_prov Gf op = NONE /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\
    ^pop_word_frame
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p.ptr_location <> LocCalldata` by (drule_all word_arm_location >> simp[]) >>
  qpat_assum `ghost_inv_at_mods Dh _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet)) >>
  disch_then (qspecl_then [`sb`,`rt`,`op`,`PG`] mp_tac) >>
  impl_tac >- simp[post_value_type_def] >>
  disch_then (qx_choosel_then [`v`,`w`,`q`,`Gf`,`tf`] strip_assume_tac) >>
  `alloca_inv s` by
    (qhdtm_assum `vv_post_mods`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`v`,`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

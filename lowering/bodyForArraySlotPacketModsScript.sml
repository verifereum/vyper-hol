(* A slot capture saves an observed array region and its list of places. *)
Theory bodyForArraySlotPacketMods
Ancestors
  bodyForArrayLengthPacketMods bodyForArraySlotLengthMods
  bodyForArrayHeaderInstallMods bodyForArrayEntryMods
  vyperTypeValues vyperValue vyperAST exprSimCopy venomState ptrDiscipline
  vyperStorageTrace vyperStorageFootprint

Theorem slot_install_base[local]:
  for_array_install_frame_mods saL u Gu tu G tn t /\
  copy_old_operand saL op ==>
  eval_operand op t = eval_operand op u /\ op_prov G op = op_prov Gu op
Proof
  Cases_on `op` >>
  simp[for_array_install_frame_mods_def,copy_old_operand_def,
       eval_operand_def,op_prov_def]
QED

Theorem slot_length_bound[local]:
  compatible_bound bd len ==> len <= bound_length bd
Proof
  Cases_on `bd` >> simp[compatible_bound_def,bound_length_def]
QED

Theorem for_array_slot_packet_mods:
  expr_body_pre_mods mods c cx env e es /\
  post_value_type c e = ArrayT sty bd /\
  evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et bd) /\
  bound_length bd <= n /\
  (!tail. eval_expr cx e (es with gas_obs := prefix ++ tail) =
    (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),em with gas_obs := tail)) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
    storage_well_formed_on cx es (FST H) /\
    vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
      (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv r /\
    ghost_inv_at_mods (DF H) lo d c cx em Gr traw r) /\
  ptr_vv_ok cx (post_value_type c e)
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv em Gr traw r /\
  compile_expr c (expr_type e) e sa0 = (vv,sbExpr) /\ local_ptrs_reserved c sa0 /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (case bd of Fixed cnt => comp_return (Lit (n2w cnt))
     | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc
                      (vv_operand vv)) sbExpr = (len_op,saL) /\
  fn_has_code sbExpr saL func /\ copy_old_operand saL (vv_operand vv) /\
  ~r.vs_halted /\ r.vs_current_bb = sbExpr.cs_current_bb /\
  r.vs_inst_idx = LENGTH sbExpr.cs_current_insts /\
  for_array_outer_frame_mods ctx func c sa0 es s0 G0 tn0 em Gr traw r /\
  ret_pc_ok c sa0 r /\ return_buf_frame d c sa0 r /\ return_buf_sep d c em r /\
  (!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst q. frag_reachable ctx func r fn inst q ==> dalloca_fmp_headroom inst q) ==>
  ?vs u Gu tu off root path delta.
    for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
      (explicit,PG) cx env st0 (es,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),item,blocks,addr_cut,body_cut)
      (PlaceR (StoragePlace tr slot (ArrayTV et bd))) n (r,Gr,traw)
      (em,u,Gu,tu,slot,ForArraySlot tr off root path delta,vs)
Proof
  strip_tac >>
  drule_all for_array_slot_length_ready_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`len`,`vs`,`off`,`root`,`path`,`delta`,`u`,`Gu`,`tu`]
         strip_assume_tac))) >>
  `evaluate_type (get_tenv cx) sty = SOME et` by
    (qpat_assum `post_value_type c e = _` (fn eq =>
       qpat_assum `evaluate_type _ (post_value_type _ _) = SOME _`
         (mp_tac o PURE_ONCE_REWRITE_RULE [eq])) >>
     disch_then (strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >> fs[]) >>
  `len <= bound_length bd` by
    (irule slot_length_bound >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
       gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `LENGTH vs = len` (SUBST_ALL_TAC o SYM) >>
  qexistsl_tac [`vs`,`u`,`Gu`,`tu`,`off`,`root`,`path`,`delta`] >>
  pure_rewrite_tac[for_array_length_packet_mods_def] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
          gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
       gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac slot_install_base >>
  simp[NoAsms,for_array_entry_route_mods_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `et` >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
  qexists_tac `[]` >> simp[]
QED

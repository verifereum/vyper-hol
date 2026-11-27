(* Discharge the return decoder interval, before any emitted join jump. *)
Theory bodyFullExtCallReturnSizedDecode
Ancestors
  bodyFullExtCallReturnDecoderEntry bodyFullExtCallReturnDecodedPost
  abiValidAllocatedContract abiMalformedRecursiveInterface abiDecodePtrMemberFrame
  extcallReturnDefaultTypes stateRelProj fragGasOriginPtr fragGasPathMem
  bodyPtrDefs loweringPosts loweringStateRelDefs[qualified,ignore_grammar]
  ptrDiscipline compileEnv exprLowering vyperStorageFootprint vyperABIValid
  vyperABI vyperAST vyperState venomState venomMemDefs words finite_map pred_set list
  exprSimHypsDefs[qualified]

Theorem extcall_return_sized_decode:
  !mods.
  (!H0 ce env sf ty tv v ctx func cenv cx es st en source hi pos output
    B L xs p d dstid live ceiling s G tn lo PG.
    abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
      st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
        d (type_memory_bytes ce ty) s u /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G',tn')) /\
      ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
      abi_decode_ptr_window G' tn' u source (n2w B) L /\
      (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
         val_in_memory tv v d mem) /\
      (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
           ~abi_malformed_site_range
              (abi_malformed_scratch_sites st en func) s u a 1 ==>
           (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
      alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next) ==>
  (!H0 ce env sf ty tv ctx func cenv cx es st en source hi pos output
    B L xs p d dstid live ceiling s G tn lo PG bytes.
    abi_decoder_coherent ce env sf ty tv /\
    abi_decode_bytes_widths env ty /\
    compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (type_to_abi_dec_info sf ce ty) st = ((),en) /\
    fn_has_code st en func /\ fn_inst_ids_distinct func /\
    (?av. has_type (vyper_to_abi_type env ty) av) /\
    assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
    abi_size_bound sf ty < dimword (:256) /\
    abi_malformed_entry H0 ctx func cenv cx es st
      (abi_malformed_scratch_sites st en func) dstid live
      (Var source) hi pos (Var output) B L xs p d (type_memory_bytes ce ty) s /\
    (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => p+32 <= L | _ => T) /\
    fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    bytes = (if is_dynamic (vyper_to_abi_type env ty) then DROP p xs
      else TAKE (static_length (vyper_to_abi_type env ty)) (DROP p xs)) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
      abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes)) /\
    abi_decode_ptr_window G tn s source (n2w B) L /\
    ptr_covers G tn output s (type_memory_bytes ce ty) /\
    op_prov G pos = NONE /\ op_prov G hi = NONE /\
    op_taint tn pos = {} /\ op_taint tn hi = {} /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (Abort Revert_abort u,G',tn'))) ==>
  expr_body_pre_mods mods cenv cx env (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt)
    es /\
  ret_type <> NoneT /\
  evaluate_type (get_tenv cx) ret_type = SOME actual_tv /\
  cap = abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap ret_type then TupleT
    [ret_type] else ret_type) /\
  abi_static_size cenv.ce_struct_fields (if needs_external_call_wrap ret_type then TupleT [ret_type]
    else ret_type) <= LENGTH bs /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD (Var source) hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv (if needs_external_call_wrap ret_type then TupleT
      [ret_type] else ret_type)) hs = ((),de) /\
  fn_has_code hs de func /\ fn_inst_ids_distinct func /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_malformed_entry H ctx func cenv cx ee hs (abi_malformed_scratch_sites hs de func) dstid live
      (Var source) hi (Lit 0w) (Var output) (w2n ro) (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest
        (type_memory_bytes cenv (if needs_external_call_wrap ret_type then TupleT [ret_type] else
        ret_type)) u) /\
  ~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\
  u.vs_inst_idx = LENGTH hs.cs_current_insts /\
  eval_operand (Var source) t = SOME ro /\
  FLOOKUP G source = SOME (prov_base,span) /\
  op_taint tn (Var source) = {} /\
  prov_base <= w2n ro /\ w2n ro + cap <= prov_base + span /\
  alloca_inv t /\ FLOOKUP t.vs_allocas live = SOME (w2n ro,bufsz) /\
  cap <= bufsz /\
  (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH bs) ==> i NOTIN tn.t_mem) /\
  lookup_var source u = lookup_var source t /\
  FLOOKUP Gf source = FLOOKUP G source /\
  op_taint tm (Var source) = op_taint tn (Var source) /\
  (!i. i < t.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  ptr_covers Gf tm output u (type_memory_bytes cenv (if needs_external_call_wrap ret_type then TupleT
    [ret_type] else ret_type)) /\
  op_prov Gf hi = NONE /\
  op_taint tm hi = {} /\
  alloca_history func u /\
  wb_frame cenv es ee sa s0 u /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= dstid /\ dstid < sb.cs_next_id /\
  sa.cs_next_id <= hs.cs_next_id /\ sa.cs_next_var <= hs.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo rb cenv cx ee Gf tm u) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tm ==>
  case evaluate_abi_decode_return (get_tenv cx) ret_type bs of
    INR err => ?z Gr tr. !D explicit.
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gf,tm) [] (Abort Revert_abort z,Gr,tr)
  | INL value => ?z Gd td.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gf,tm) [] (OK z,Gd,td)) /\
      ~z.vs_halted /\ z.vs_current_bb = de.cs_current_bb /\
      z.vs_inst_idx = LENGTH de.cs_current_insts /\ alloca_history func z /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H ctx func cenv cx (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args
          dflt) es sa sb s0 ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) z /\
        vv_store_bound cx (expr_type (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts)
          args dflt)) (lowered_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type)
          opts) args dflt)) ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) z /\
        vv_own cenv cx (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type)
          opts) args dflt)) sa sb ee (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory))
          z /\
        ptr_vv_ok cx (post_value_type cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type)
          opts) args dflt)) (Value value) (LocatedValue ann (mk_ptr (Var output) LocMemory)) ee Gd td
          z /\
        ptr_buf_ok cenv (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) (Var
          output) Gd z /\
        ghost_inv_at (DF H) lo rb cenv cx ee Gd td z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 Gd td /\
        s0.vs_alloca_next <= z.vs_alloca_next)
Proof
  disch_then (mk_asm "valid") >> disch_then (mk_asm "reject") >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `rt = if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type` >>
  qabbrev_tac `tv = if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv` >>
  `rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
   tv = (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv)`
    by simp[Abbr `rt`,Abbr `tv`] >>
  drule_all return_default_wrapped_types >> strip_tac >>
  drule_all return_default_decode_bounds >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> storage_well_formed_on _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `alloca_inv u` by
    (qhdtm_assum `abi_malformed_entry` (mp_tac o REWRITE_RULE [abi_malformed_entry_def]) >>
     strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `gas_path_mem ctx func u 0 (OK u)` by simp[gas_path_mem_rules] >>
  qpat_x_assum `cap = abi_size_bound _ _` SUBST_ALL_TAC >>
  drule_all (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`entry` |-> `u`, `GP` |-> `Gf`, `tp` |-> `tm`]
      extcall_return_allocated_decoder_entry)) >>
  qpat_assum `rt = _` (fn wrap =>
    qpat_assum `abi_size_bound _ _ = vyper_abi_size_bound _ _` (fn bound =>
      disch_then (strip_assume_tac o PURE_REWRITE_RULE [GSYM wrap,GSYM bound]))) >>
  Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type bs` >>
  simp_tac bool_ss [sumTheory.sum_case_def]
  >- (rename1 `evaluate_abi_decode_return _ _ _ = INL value` >>
      qpat_x_assum `!v. INL _ = INL v ==> _`
        (qspec_then `value` (assume_tac o REWRITE_RULE [])) >>
      asm_x "valid" (drule_at_then (Pat `abi_valid_allocated_entry`)
        (drule_all o SIMP_RULE bool_ss [n2w_w2n])) >>
      disch_then (qspec_then `PG` (qx_choose_then `z` (qx_choose_then `Gd`
        (qx_choose_then `td` (map_every assume_tac o CONJUNCTS))))) >>
      qhdtm_assum `abi_valid_allocated_post`
        (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
      qexistsl_tac [`z`,`Gd`,`td`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qhdtm_x_assum `abi_malformed_entry` kall_tac >>
      qhdtm_x_assum `ghost_inv_at` kall_tac >>
      qhdtm_x_assum `storage_well_formed_on` kall_tac >>
      qx_gen_tac `H` >> disch_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` (drule_then assume_tac)) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> storage_well_formed_on _ _ _ /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      qpat_assum `rt = _` (fn wrap => qpat_assum `tv = _` (fn tvwrap =>
        drule_all (SIMP_RULE bool_ss [LET_THM,GSYM wrap,GSYM tvwrap,DE_MORGAN_THM]
          extcall_return_decoded_post))) >>
      disch_then ACCEPT_TAC) >>
  rename1 `evaluate_abi_decode_return _ _ _ = INR err` >>
  qpat_x_assum `!err. INR _ = INR err ==> _`
    (qspec_then `err` (map_every assume_tac o CONJUNCTS o REWRITE_RULE [])) >>
  asm_x "reject" (drule_at_then (Pat `abi_malformed_entry`)
    (drule_at_then (Pat `abi_decoder_coherent`)
      (mp_tac o SIMP_RULE bool_ss [n2w_w2n,DROP_0,arithmeticTheory.ADD_CLAUSES,DE_MORGAN_THM]))) >>
  disch_then (qspecl_then [`ceiling`,`Gf`,`tm`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `z` (qx_choose_then `Gr` (qx_choose_then `tr`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`z`,`Gr`,`tr`] >> first_assum ACCEPT_TAC
QED

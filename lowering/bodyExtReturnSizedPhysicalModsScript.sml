(* Execute the decoder at the successful size-check cut, retaining its physical post. *)
Theory bodyExtReturnSizedPhysicalMods
Ancestors
  abiValidAllocatedContract abiMalformedRecursiveInterface abiDecodePtrMemberFrame
  abiReturnSuccessSource abiReturnReject abiWidthInhabited
  extcallReturnDefaultTypes extcallReturnEntryBridge
  fragGasOriginPtr bodyPtrDefs exprLowering compileEnv ptrDiscipline
  vyperABIValid vyperABI contractABI vyperAST vyperState
  venomState venomMemDefs words finite_map pred_set list arithmetic

Theorem sized_return_valid_source[local]:
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ret_type bs = INL value ==>
  vyper_decode_valid_enc (vyper_to_abi_type env rt) (TAKE cap bs) /\
  abi_to_vyper env rt (dec (vyper_to_abi_type env rt) (TAKE cap bs)) =
    SOME (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value) /\
  (is_dynamic (vyper_to_abi_type env rt) \/
   static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs))
Proof
  strip_tac >>
  `evaluate_abi_decode env rt (TAKE cap bs) =
   INL (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value)` by
    (irule abi_return_source_capped_success >> simp[] >>
     qexistsl_tac [`ret_type`, `value`] >> simp[]) >>
  drule_then assume_tac evaluate_abi_decode_vyper_valid_enc >>
  drule_then assume_tac vyper_valid_enc_static_length_lower >>
  drule_then assume_tac vyper_valid_enc_decode_valid_enc >>
  simp[] >>
  qpat_x_assum `evaluate_abi_decode _ _ _ = INL _` mp_tac >>
  Cases_on `needs_external_call_wrap ret_type` >>
  simp[evaluate_abi_decode_def, decode_abi_value_def, AllCaseEqs()]
QED

Theorem sized_return_head_bound[local]:
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  abi_static_size sf rt <= cap /\ abi_static_size sf rt <= LENGTH bs ==>
  abi_static_size sf rt <= LENGTH (TAKE cap bs) /\
  (case type_to_abi_dec_info sf ce rt of
     DecPrimWord clamp => 32 <= LENGTH (TAKE cap bs) | _ => T)
Proof
  strip_tac >>
  `abi_static_size sf rt <= LENGTH (TAKE cap bs)` by
    (Cases_on `cap <= LENGTH bs` >> gvs[LENGTH_TAKE_EQ]) >>
  simp[] >>
  `(case type_to_abi_dec_info sf ce rt of
      DecPrimWord clamp => 32 <= abi_static_size sf rt | _ => T)` by
    (irule return_default_primitive_minimum >> qexists `ret_type` >> simp[]) >>
  Cases_on `type_to_abi_dec_info sf ce rt` >> gvs[] >> decide_tac
QED

Theorem extcall_sized_physical_mods:
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
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  tv = (if needs_external_call_wrap ret_type then TupleTV [actual_tv] else actual_tv) /\
  cap = vyper_abi_size_bound (get_tenv cx) rt /\
  (~is_dynamic (vyper_to_abi_type (get_tenv cx) rt) ==>
     cap = static_length (vyper_to_abi_type (get_tenv cx) rt)) /\
  abi_static_size cenv.ce_struct_fields rt =
    abi_static_length (vyper_to_abi_type (get_tenv cx) rt) /\
  abi_static_size cenv.ce_struct_fields rt <= cap /\
  abi_static_size cenv.ce_struct_fields rt <= LENGTH bs /\
  abi_decoder_coherent cenv (get_tenv cx) cenv.ce_struct_fields rt tv /\
  abi_decode_bytes_widths (get_tenv cx) rt /\ assignable_type (get_tenv cx) rt /\
  type_memory_size tv < dimword (:256) /\ abi_size_bound cenv.ce_struct_fields rt < dimword (:256) /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD (Var source) hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi (Lit 0w) (Var output) (w2n ro) (LENGTH (TAKE cap bs)) (TAKE cap bs) 0
    dest (type_memory_bytes cenv rt) u /\
  ~u.vs_halted /\ u.vs_current_bb = st.cs_current_bb /\ u.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window Gf tm u source ro (LENGTH (TAKE cap bs)) /\
  ptr_covers Gf tm output u (type_memory_bytes cenv rt) /\
  op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\ alloca_history func u ==>
  case evaluate_abi_decode_return (get_tenv cx) ret_type bs of
    INL value => ?z Gd td ceiling.
      abi_valid_allocated_post tv
        (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value)
        ctx func cenv cx es st en ceiling dstid dest (type_memory_bytes cenv rt) u z /\
      ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\ z.vs_inst_idx = LENGTH en.cs_current_insts /\
      z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
      z.vs_call_ctx = u.vs_call_ctx /\ z.vs_immutables = u.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gf,tm) [] (OK z,Gd,td)) /\
      ptr_covers Gd td output z (type_memory_bytes cenv rt) /\
      abi_decode_ptr_window Gd td z source ro (LENGTH (TAKE cap bs)) /\
      (!mem. mem_agree_outside td.t_mem z.vs_memory mem ==>
         val_in_memory tv
           (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value) dest mem) /\
      (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
         FLOOKUP Gd x = FLOOKUP Gf x /\ op_taint td (Var x) = op_taint tm (Var x)) /\
      td.t_stor = tm.t_stor /\ td.t_trans = tm.t_trans /\ td.t_imm = tm.t_imm /\
      (!a. ~(dest <= a /\ a < dest+type_memory_bytes cenv rt) /\
           ~abi_malformed_site_range
              (abi_malformed_scratch_sites st en func) u z a 1 ==>
           (a IN td.t_mem <=> a IN tm.t_mem)) /\
      alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next
  | INR err => ?z Gr tr.
      z.vs_accounts = u.vs_accounts /\ z.vs_transient = u.vs_transient /\
      z.vs_call_ctx = u.vs_call_ctx /\ z.vs_immutables = u.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gf,tm) [] (Abort Revert_abort z,Gr,tr))
Proof
  disch_then (mk_asm "valid") >> disch_then (mk_asm "reject") >> strip_tac >>
  qspecl_then [`u`, `en`] (qx_choose_then `ceiling` strip_assume_tac)
    return_decoder_ceiling_exists >>
  `op_prov Gf (Lit 0w) = NONE /\ op_taint tm (Lit 0w) = {}` by
    simp[op_prov_def, op_taint_def] >>
  Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type bs` >>
  simp_tac bool_ss [sumTheory.sum_case_def]
  >- (rename1 `evaluate_abi_decode_return _ _ _ = INL value` >>
      drule_all sized_return_valid_source >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `abi_valid_allocated_entry H0 cenv (get_tenv cx) cenv.ce_struct_fields rt tv
         (if needs_external_call_wrap ret_type then ArrayV (TupleV [value]) else value)
         ctx func cenv cx es st en (Var source) hi (Lit 0w) (Var output)
         (w2n ro) (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest dstid live ceiling u` by
        (rewrite_tac[abi_valid_allocated_entry_def, DROP_0, ADD_CLAUSES] >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
      asm_x "valid" (drule_at_then (Pat `abi_valid_allocated_entry`)
        (drule_all o SIMP_RULE bool_ss [n2w_w2n])) >>
      disch_then (qspec_then `PG` (qx_choose_then `z` (qx_choose_then `Gd`
        (qx_choose_then `td` (map_every assume_tac o CONJUNCTS))))) >>
      qhdtm_assum `abi_valid_allocated_post`
        (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
      qexistsl_tac [`z`, `Gd`, `td`, `ceiling`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_static_size cenv.ce_struct_fields rt <= LENGTH (TAKE cap bs) /\
   (case type_to_abi_dec_info cenv.ce_struct_fields cenv rt of
     DecPrimWord clamp => 32 <= LENGTH (TAKE cap bs) | _ => T)` by
    (irule sized_return_head_bound >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexists `ret_type` >> first_assum ACCEPT_TAC) >>
  `abi_static_length (vyper_to_abi_type (get_tenv cx) rt) <= LENGTH (TAKE cap bs)` by
    (qpat_assum `abi_static_size _ _ = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule abi_width_coherent_inhabited >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then assume_tac >>
  qabbrev_tac `bytes = if is_dynamic (vyper_to_abi_type (get_tenv cx) rt) then TAKE cap bs
    else TAKE (static_length (vyper_to_abi_type (get_tenv cx) rt)) (TAKE cap bs)` >>
  `~(vyper_decode_valid_enc (vyper_to_abi_type (get_tenv cx) rt) bytes /\
      abi_vyper_admissible (get_tenv cx) rt (dec (vyper_to_abi_type (get_tenv cx) rt) bytes))` by
    (strip_tac >>
     `?v. evaluate_abi_decode_return (get_tenv cx) ret_type bs = INL v` by
       (irule abi_return_reflected_success >> qexistsl_tac [`cap`, `rt`] >>
        unabbrev_all_tac >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
     gvs[]) >>
  asm_x "reject" (drule_at_then (Pat `abi_malformed_entry`)
    (drule_at_then (Pat `abi_decoder_coherent`)
      (irule o SIMP_RULE bool_ss [n2w_w2n, DROP_0, ADD_CLAUSES]))) >>
  unabbrev_all_tac >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   qpat_assum `~(_ /\ _)` (ACCEPT_TAC o PURE_REWRITE_RULE [DE_MORGAN_THM]) ORELSE
   (qexists `ceiling` >> rpt conj_tac >> first_assum ACCEPT_TAC))
QED

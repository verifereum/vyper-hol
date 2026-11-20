(* Mixed valid-prefix / malformed-child induction over the unrolled table.
   The only execution premise besides the child contracts is one setup slice. *)
Theory abiDecodeRejectMemberPrefix
Ancestors
  abiValidAllocatedContract abiMalformedMemberSetup abiDecoderMemberCons
  abiDecoderMemberCode abiDecoderOffset abiDecodePtrMemberFrame decoderGhostFramePtr
  exprSimAbiDecodePrimitiveOwned abiDecodeRanges abiVyperAdmissible
  abiMalformedBoundedContract abiMalformedRecursiveInterface abiDecoderCoherence abiDecoderContract
  abiDecoderDynamic abiDecoderReentry fragExec exprLoweringProps
  fragGasOriginPtr compileEnv venomState ptrDiscipline list rich_list arithmetic

val worlds = ``\s t. t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables``;
val path = ``\s G tn out H z. !D explicit.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (out,H,z)``;
val abort = ``\s G tn. ?u H z. (^worlds) s u /\ (^path) s G tn (Abort Revert_abort u) H z``;
val pc = ``\st s. fresh_vars_wrt ceiling s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts``;
val ghosts = ``\p x k s G tn. abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn x s k /\ op_prov G p = NONE /\ op_prov G hi = NONE /\
  op_taint tn p = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s``;
val entry = ``\st en p x q a k s.
  abi_malformed_entry H0 ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi p (Var x) B L xs q a k s``;
val old_live = ``\st (G:string |-> num # num) tn H z. !x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
  FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)``;
val source_pos = ``\ty ao. b + (if dec_info_needs_offset (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty)
  then abi_head_word (DROP (b+ao) (xs:word8 list)) else ao)``;
val source_view = ``\ty q. if is_dynamic (vyper_to_abi_type env ty) then DROP q (xs:word8 list)
  else TAKE (static_length (vyper_to_abi_type env ty)) (DROP q xs)``;
val malformed_view = ``\ty bytes. ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes))``;
val child_contract = ``\ty. !st en p x q a s G tn.
  compile_abi_decode_to_buf (Var x) p MLOAD (Var source) hi
    (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty) st = ((),en) /\ fn_has_code st en func /\
  (^entry) st en p x q a (type_memory_bytes ce ty) s /\
  (case type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty of DecPrimWord clamp => q+32 <= L | _ => T) /\
  (^pc) st s /\ en.cs_next_var <= ceiling.cs_next_var /\
  (^malformed_view) ty ((^source_view) ty q) /\
  (^ghosts) p x (type_memory_bytes ce ty) s G tn ==> (^abort) s G tn``;

(* The ordinary child success specification, at the fixed external parameters. *)
val valid_child = ``!ty tv v st en p x q a s G tn.
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es st en
    (Var source) hi p (Var x) B L xs q a dstid live ceiling s /\
  (^ghosts) p x (type_memory_bytes ce ty) s G tn ==>
  ?u H z. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      a (type_memory_bytes ce ty) s u /\ (^worlds) s u /\ (^path) s G tn (OK u) H z /\
    ptr_covers H z x u (type_memory_bytes ce ty) /\
    abi_decode_ptr_window H z u source (n2w B) L /\
    (!mem. mem_agree_outside z.t_mem u.vs_memory mem ==> val_in_memory tv v a mem) /\
    (^old_live) st G tn H z /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!k. ~(a <= k /\ k < a+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u k 1 ==>
      (k IN z.t_mem <=> k IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;

val setup_cut = ``!ty ao vo st mid child en ops s G tn.
  abi_decode_member_setup (Var output) pos MLOAD (Var source) hi
    (dec_info_needs_offset (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty)) ao vo st = (ops,mid) /\
  fn_has_code st mid func /\ cs_extends st mid /\
  st.cs_next_id < mid.cs_next_id /\ mid.cs_next_id <= child.cs_next_id /\
  child.cs_next_id <= en.cs_next_id /\ mid.cs_next_var <= ceiling.cs_next_var /\
  (^entry) st en pos output b d outsz s /\ (^pc) st s /\
  (^ghosts) pos output outsz s G tn /\ vo + type_memory_bytes ce ty <= outsz /\
  (if dec_info_needs_offset (type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty) then b+ao+32 <= L
   else b+ao <= L) ==>
  (^abort) s G tn \/
  ?r H z x. SND ops = Var x /\
    (^entry) mid child (FST ops) x ((^source_pos) ty ao) (d+vo) (type_memory_bytes ce ty) r /\
    (^pc) mid r /\ (^ghosts) (FST ops) x (type_memory_bytes ce ty) r H z /\
    (^worlds) s r /\ (^path) s G tn (OK r) H z /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s r /\ (^old_live) st G tn H z``;

val head_sum = ``\ts. SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) ts))``;
val dest_sum = ``\ts. SUM (MAP (type_memory_bytes ce) ts)``;
val good_view = ``\ty ao.
  (^source_pos) ty ao <= L /\
  (is_dynamic (vyper_to_abi_type env ty) \/
   (^source_pos) ty ao + static_length (vyper_to_abi_type env ty) <= L) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP ((^source_pos) ty ao) xs) /\
  (?v. abi_to_vyper env ty
         (dec (vyper_to_abi_type env ty) (DROP ((^source_pos) ty ao) xs)) = SOME v)``;

Theorem malformed_table_prefix_reject_joint:
  fn_inst_ids_distinct func /\ (^valid_child) /\ (^setup_cut) ==>
  !i ts ao vo st en s G tn.
    i < LENGTH ts /\ b + ao + (^head_sum) ts <= L /\
    (!j. j <= i ==>
      (?tv. abi_decoder_coherent ce env sf (EL j ts) tv /\ assignable_type env (EL j ts) /\
        (?av. has_type (vyper_to_abi_type env (EL j ts)) av) /\
        abi_decode_bytes_widths env (EL j ts) /\
        type_memory_size tv < dimword (:256) /\ abi_size_bound sf (EL j ts) < dimword (:256) /\
        (^child_contract) (EL j ts)) /\
      vo + (^dest_sum) (TAKE j ts) + type_memory_bytes ce (EL j ts) <= outsz /\
      (if j = i then (^malformed_view) (EL j ts) ((^source_view) (EL j ts) ((^source_pos) (EL j ts)
        (ao + (^head_sum) (TAKE j ts))))
       else (^good_view) (EL j ts) (ao + (^head_sum) (TAKE j ts)))) /\
    compile_abi_decode_complex_elems (Var output) pos MLOAD (Var source) hi
      (abi_decoder_member_infos sf ce ts) ao vo st = ((),en) /\ fn_has_code st en func /\
    en.cs_next_var <= ceiling.cs_next_var /\ (^entry) st en pos output b d outsz s /\
    (^pc) st s /\ (^ghosts) pos output outsz s G tn ==>
    (^abort) s G tn
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "valid") (mk_asm "setup"))) >>
  completeInduct_on `i` >>
  qpat_x_assum `!m. m < i ==> _` (mk_asm "ih") >>
  qx_gen_tac `ts` >> namedCases_on `ts` ["", "ty tys"] >- simp[] >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "members") (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  asm "members" (qspec_then `0` mp_tac) >>
  simp_tac bool_ss [EL, HD, TAKE, MAP, SUM, ADD_0, ZERO_LESS_EQ] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "view"))) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_member_cons_trace >>
  disch_then (qx_choose_then `ops` (qx_choose_then `mid` (qx_choose_then `child`
    (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `b + ao + abi_member_head_size (vyper_to_abi_type env ty) <= L` by
    (qpat_assum `b + ao + SUM _ <= L` mp_tac >> simp_tac bool_ss [MAP, SUM] >> decide_tac) >>
  `if dec_info_needs_offset (type_to_abi_dec_info sf ce ty) then b+ao+32 <= L
   else b+ao <= L` by
    (drule abi_decoder_coherent_dynamic >> strip_tac >>
     Cases_on `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` >>
     fs[abi_decoder_needs_offset_iff, abi_member_head_size_def] >> decide_tac) >>
  `fn_has_code st mid func /\ fn_has_code mid child func` by
    (qspecl_then [`st`, `mid`, `child`, `func`] mp_tac fn_has_code_split >>
     asm_simp_tac bool_ss []) >>
  `mid.cs_next_var <= ceiling.cs_next_var /\ child.cs_next_var <= ceiling.cs_next_var` by
    decide_tac >>
  asm "setup" (qspecl_then [`ty`, `ao`, `vo`, `st`, `mid`, `child`, `en`, `ops`, `s`, `G`, `tn`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC
    (qx_choose_then `r` (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `x` strip_assume_tac))))) >>
  Cases_on `i` >- (
    `case type_to_abi_dec_info sf ce ty of
       DecPrimWord clamp => (^source_pos) ty ao + 32 <= L | _ => T` by
      (BETA_TAC >> Cases_on `type_to_abi_dec_info sf ce ty` >> simp[] >>
       drule_all abi_decode_scalar_source_shape >> strip_tac >>
       fs[abi_decoder_needs_offset_iff, abi_decoder_dynamic_def, abi_member_head_size_def]) >>
    qpat_assum `!st en p x q a s G tn. _` (qspecl_then
      [`mid`, `child`, `FST ops`, `x`, `(^source_pos) ty ao`, `d+vo`, `r`, `G1`, `tn1`] mp_tac) >>
    (impl_tac >- (asm "view" mp_tac >> simp_tac bool_ss [] >> strip_tac >>
      asm_simp_tac bool_ss [] >> gvs[])) >>
    disch_then (qx_choose_then `u` (qx_choose_then `H` (qx_choose_then `z` strip_assume_tac))) >>
    qexistsl_tac [`u`, `H`, `z`] >> simp[] >> rpt gen_tac >>
    qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
      (qspecl_then [`D`, `explicit`] mp_tac) >>
    qpat_assum `!D explicit. gas_origin_ptr_path _ (r,G1,tn1) [] _`
      (qspecl_then [`D`, `explicit`] mp_tac) >>
    POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  asm_x "view" mp_tac >> simp_tac bool_ss [EQ_SYM_EQ, numTheory.NOT_SUC, LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `value` assume_tac)))) >>
  qpat_assum `SND ops = Var x` (fn th =>
    qpat_assum `compile_abi_decode_to_buf (SND ops) _ _ _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  asm_x "valid" (qspecl_then [`ty`, `tv`, `value`, `mid`, `child`,
     `FST ops`, `x`, `(^source_pos) ty ao`, `d+vo`, `r`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [abi_valid_allocated_entry_def] >> asm_simp_tac bool_ss [])) >>
  disch_then (qx_choose_then `t` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qhdtm_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  `abi_malformed_scratch_sites mid child func SUBSET abi_malformed_scratch_sites st en func /\
   abi_malformed_scratch_sites child en func SUBSET abi_malformed_scratch_sites st en func` by
    (conj_tac >> irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid r t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`mid.cs_next_var`, `abi_malformed_scratch_sites mid child func`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid s t` by
    (irule abi_malformed_resource_trans >> qexists `r` >> simp[]) >>
  `local_ptrs_reserved cenv child` by
    (irule local_ptrs_reserved_next_var >> qexists `st` >>
     fs[abi_malformed_entry_def] >> decide_tac) >>
  `(^entry) child en pos output b d outsz t` by
    (BETA_TAC >> irule abi_malformed_aggregate_reentry >> simp[] >>
     qexistsl_tac [`s`, `abi_malformed_scratch_sites st en func`, `st`] >>
     simp[] >> decide_tac) >>
  `!q. abi_decoder_operand_live st.cs_next_var (Var q) ==>
       FLOOKUP G2 q = FLOOKUP G q /\ op_taint tn2 (Var q) = op_taint tn (Var q)` by
    (gen_tac >> disch_tac >>
     `abi_decoder_operand_live mid.cs_next_var (Var q)` by
       (irule abi_decoder_operand_live_mono >> qexists `st.cs_next_var` >> simp[]) >>
     qpat_assum `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==> _`
       (qspec_then `q` mp_tac) >>
     qpat_assum `!x. abi_decoder_operand_live mid.cs_next_var (Var x) ==> _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live st.cs_next_var (Var output) /\
   abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
   lookup_var output t = lookup_var output s` by
    (qpat_assum `(^entry) child en pos output b d outsz t`
       (mp_tac o PURE_REWRITE_RULE [BETA_THM, abi_malformed_entry_def]) >>
     fs[abi_malformed_entry_def, eval_operand_def]) >>
  `ptr_covers G2 tn2 output t outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     qpat_assum `!q. abi_decoder_operand_live st.cs_next_var (Var q) ==>
                   FLOOKUP G2 q = FLOOKUP G q /\ _` (qspec_then `output` mp_tac) >> simp[]) >>
  `op_prov G2 pos = NONE /\ op_prov G2 hi = NONE /\
   op_taint tn2 pos = {} /\ op_taint tn2 hi = {}` by
    (qpat_assum `!q. abi_decoder_operand_live st.cs_next_var (Var q) ==>
                   FLOOKUP G2 q = FLOOKUP G q /\ _` mp_tac >>
     Cases_on `pos` >> Cases_on `hi` >> fs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  asm_x "ih" (qspec_then `n` mp_tac) >> simp_tac bool_ss [prim_recTheory.LESS_SUC_REFL] >>
  disch_then (qspecl_then [`tys`, `ao + abi_embedded_static_size ce.ce_struct_fields ty`,
     `vo + type_memory_bytes ce ty`, `child`, `en`, `t`, `G2`, `tn2`] mp_tac) >>
  (impl_tac >- (
     `n < LENGTH tys` by fs[] >>
     `abi_embedded_static_size ce.ce_struct_fields ty =
        abi_member_head_size (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
     `b + (ao + abi_embedded_static_size ce.ce_struct_fields ty) + (^head_sum) tys <= L` by
       (qpat_assum `b + ao + SUM _ <= L` mp_tac >> BETA_TAC >>
        qpat_assum `abi_embedded_static_size _ ty = _` (fn th =>
          simp_tac bool_ss [MAP, SUM, th, ADD_ASSOC])) >>
     qpat_x_assum `b + (ao + abi_embedded_static_size _ ty) + (^head_sum) tys <= L`
       (assume_tac o BETA_RULE) >>
     qpat_x_assum `(^entry) child en pos output b d outsz t` (assume_tac o BETA_RULE) >>
     asm_simp_tac bool_ss [IgnAsm `abi_embedded_static_size _ ty = _`] >>
     gen_tac >> disch_tac >>
     asm_x "members" (qspec_then `SUC j` mp_tac) >>
     asm_simp_tac bool_ss [TAKE, EL, HD, TL, MAP, SUM, LESS_EQ_MONO,
        prim_recTheory.INV_SUC_EQ, AC ADD_ASSOC ADD_COMM])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `H` (qx_choose_then `z` strip_assume_tac))) >>
  qexistsl_tac [`u`, `H`, `z`] >> conj_tac >- (
    rpt conj_tac
    >- (qpat_assum `u.vs_accounts = t.vs_accounts` SUBST1_TAC >>
        qpat_assum `t.vs_accounts = r.vs_accounts` SUBST1_TAC >>
        qpat_assum `r.vs_accounts = s.vs_accounts` (fn th => simp_tac bool_ss [th]))
    >- (qpat_assum `u.vs_transient = t.vs_transient` SUBST1_TAC >>
        qpat_assum `t.vs_transient = r.vs_transient` SUBST1_TAC >>
        qpat_assum `r.vs_transient = s.vs_transient` (fn th => simp_tac bool_ss [th]))
    >- (qpat_assum `u.vs_call_ctx = t.vs_call_ctx` SUBST1_TAC >>
        qpat_assum `t.vs_call_ctx = r.vs_call_ctx` SUBST1_TAC >>
        qpat_assum `r.vs_call_ctx = s.vs_call_ctx` (fn th => simp_tac bool_ss [th]))
    >- (qpat_assum `u.vs_immutables = t.vs_immutables` SUBST1_TAC >>
        qpat_assum `t.vs_immutables = r.vs_immutables` SUBST1_TAC >>
        qpat_assum `r.vs_immutables = s.vs_immutables` (fn th => simp_tac bool_ss [th]))) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (r,G1,tn1) [] _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (t,G2,tn2) [] _`
    (qspecl_then [`D`, `explicit`] mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

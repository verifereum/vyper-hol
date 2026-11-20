(* Lift the constructor-specific joint decoder contracts to a coherent entry. *)
Theory abiDecodeValidCoherentCases
Ancestors
  abiDecodePtrMemberFrame abiValidAllocatedContract abiDecoderCoherence
  abiDecoderReentry abiMalformedSiteFrame fragGasOriginPtr allocaHistory
  exprLowering bodyPtrDefs ptrDiscipline valueEncoding list

(* The child contract is polymorphic in the entry, ghosts, and descending
   maps. In particular both map parameters change for struct members. *)
local
val C = ``\ce env sf ty tv.
 !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
 abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
   st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
 !G tn PG lo.
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
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
   tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
   alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;
in
Theorem abi_valid_allocated_joint_from_cases:
  ((!ce env sf ty tv clamp.
      type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
      (^C) ce env sf ty tv) /\
   (!ce env sf ty tv n.
      (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
      (^C) ce env sf ty tv) /\
   (!ce env sf tys tvs.
      LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
      LIST_REL ((^C) ce env sf) tys tvs ==>
      (^C) ce env sf (TupleT tys) (TupleTV tvs)) /\
   (!ce env sf ty tv n.
      abi_decoder_coherent ce env sf ty tv /\ (^C) ce env sf ty tv ==>
      (^C) ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))) /\
   (!ce env sf nsid args fields tvs.
      FLOOKUP env nsid = SOME (StructArgs args) /\
      FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
      MAP (\(name,ty,sz). (name,ty)) fields = args /\
      LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
        (MAP SND args) tvs /\
      LIST_REL ((^C) ce (env \\ nsid) (sf \\ nsid_to_string nsid)) (MAP SND args) tvs ==>
      (^C) ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))) /\
   (!ce env sf ty tv n ei abi_sz mem_sz.
      type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) = DecDynArray ei abi_sz mem_sz F n /\
      ~dec_info_needs_clamp ei ==>
      (^C) ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))) /\
   (!ce env sf ty tv n.
      abi_decoder_coherent ce env sf ty tv /\ (^C) ce env sf ty tv /\
      abi_decoder_header ce env (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) /\
      (is_abi_dynamic ce.ce_struct_fields ty \/
       dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
      (^C) ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)))) ==>
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s
  ==>
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
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next
Proof
  BETA_TAC >> disch_then (fn th =>
    map_every (fn (label,case_th) => mk_asm label case_th)
      (ListPair.zip (["word", "bytes", "tuple", "fixed", "struct", "bulk", "finite"],
        CONJUNCTS th))) >>
  qsuff_tac `!ce env sf ty tv.
      abi_decoder_coherent ce env sf ty tv ==> (^C) ce env sf ty tv`
  >- (BETA_TAC >> strip_tac >> strip_tac >>
      `abi_decoder_coherent ce env sf ty tv` by fs[abi_valid_allocated_entry_def] >>
      first_x_assum drule >> disch_then drule >> simp[]) >>
  BETA_TAC >> ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple" >>
  suspend "struct"
QED

Resume abi_valid_allocated_joint_from_cases[base]:
  rpt gen_tac >> strip_tac >>
  Cases_on `?n. BaseT bt = BaseT (BytesT (Dynamic n)) \/ BaseT bt = BaseT (StringT n)`
  >- (asm "bytes" match_mp_tac >> simp[]) >>
  asm "word" match_mp_tac >>
  Cases_on `bt` >> gvs[type_to_abi_dec_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> gvs[type_to_abi_dec_info_def]
QED

Resume abi_valid_allocated_joint_from_cases[flag]:
  rpt gen_tac >> strip_tac >> asm "word" match_mp_tac >> simp[type_to_abi_dec_info_def]
QED

Resume abi_valid_allocated_joint_from_cases[array]:
  rpt gen_tac >> strip_tac >> Cases_on `bound`
  >- (asm "fixed" match_mp_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
            dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (asm "finite" match_mp_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "bulk" match_mp_tac >> gvs[type_to_abi_dec_info_def, DE_MORGAN_THM]
QED

Resume abi_valid_allocated_joint_from_cases[tuple]:
  rpt gen_tac >> strip_tac >> asm "tuple" match_mp_tac >>
  fs[LIST_REL_CONJ, SF ETA_ss] >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_valid_allocated_joint_from_cases[struct]:
  rpt gen_tac >> strip_tac >> asm "struct" match_mp_tac >>
  qexists_tac `fields` >> fs[LIST_REL_CONJ, SF ETA_ss] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_valid_allocated_joint_from_cases
end

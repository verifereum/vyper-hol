(* Recursive transports retain the canonical typed memory-decoder boundary. *)
Theory abiDecodeMemTypedRecursive
Ancestors
  abiDecodeMemTyped abiDecodeMemComplexGuard abiDecodeMemActualFrame
  abiDecoderCoherence abiDecoderReentry abiDecoderSiteEffect
  actualDecoderSites allocationGrowth abiCallerAllocation abiDecoderFrame
  calldataChildFrame placeMemoryTypedBase valueEncodingProofs valueEncodingProps
  valueEncodingTyping vyperTypeDefaults abiValidMember abiValidAggregateHeads
  exprSimAbiDecodeComplexOutcome exprSimAbiDecodeWidthBoundary
  abiDecoderMemberInfos abiDecodeMemMembers
  exprSimAbiDecodeMemberExecute extcallDecoderStaticSuffix
  vyperABI contractABI vyperTypeABI vyperTyping
  exprLoweringProps loweringStateRelDefs compileEnv venomState venomInst
  valueEncodingDefs valueEncoding words list rich_list arithmetic finite_map
  abiDecoderOffset abiDecodeMemLayout typeLayoutProps

fun decoder_entry inst = fst (dest_conj (fst (dest_imp (concl
  (Q.INST inst abi_decode_typed_scalar_memory)))));

val parent_entry = decoder_entry [];
val parent_result = snd (dest_imp (concl abi_decode_typed_scalar_memory));
val decoder_good =
  let
    val normal = fst (dest_disj (concl (BETA_RULE (ASSUME parent_result))));
    val body = snd (strip_exists normal)
  in fst (dest_conj (snd (dest_conj body))) end;
val child_entry = decoder_entry
  [`env` |-> `child_env`, `sf` |-> `child_sf`,
   `ty` |-> `child_ty`, `tv` |-> `child_tv`,
   `dst` |-> `cd`, `src` |-> `cs`, `st` |-> `q`, `fin` |-> `r`,
   `s` |-> `u`, `sb` |-> `cb`, `d` |-> `dd`,
   `keep_word` |-> `keep_child`];

Theorem abi_decode_typed_child_entry[local]:
  ^parent_entry /\
  abi_decoder_coherent ce child_env child_sf child_ty child_tv /\
  assignable_type child_env child_ty /\ abi_decode_bytes_widths child_env child_ty /\
  compile_abi_decode_to_buf cd cs MLOAD base_op hi
    (type_to_abi_dec_info child_sf ce child_ty) q = ((),r) /\
  fn_has_code q r func /\ st.cs_next_id <= q.cs_next_id /\
  r.cs_next_id <= fin.cs_next_id /\ r.cs_next_var <= fin.cs_next_var /\
  allocation_growth s u /\ decode_site_resources ctx func u /\
  alloca_history func u /\ fresh_vars_wrt limit u /\
  EVERY (abi_decoder_operand_live q.cs_next_var) [cs;cd;base_op;hi] /\
  eval_operand base_op u = SOME (n2w B) /\ eval_operand hi u = SOME (n2w H) /\
  eval_operand cs u = SOME (n2w cb) /\ eval_operand cd u = SOME (n2w dd) /\
  mem_bytes_at B P u.vs_memory = snap /\ cb < dimword(:256) /\
  d <= dd /\ dd + type_memory_bytes ce child_ty <= d + type_memory_bytes ce ty /\
  (!clamp. type_to_abi_dec_info child_sf ce child_ty = DecPrimWord clamp ==>
    cb+32 <= H) /\
  (!p. keep_child p ==> (B <= p /\ p+32 <= B+P) \/
    ?id. id < q.cs_next_id /\ FLOOKUP u.vs_allocas id = SOME (p,32)) /\
  (!p. keep_child p ==> p+32 <= dd \/ dd+type_memory_bytes ce child_ty <= p) /\
  ~u.vs_halted /\ u.vs_current_bb = q.cs_current_bb /\
  u.vs_inst_idx = LENGTH q.cs_current_insts ==>
  ^child_entry
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `r.cs_next_var <= limit.cs_next_var /\
   B+P <= u.vs_alloca_next /\
   dd + type_memory_bytes ce child_ty < dimword(:256)` by
    (fs[allocation_growth_def] >> decide_tac) >>
  `alloca_inv u /\ alloca_room ctx func u /\ fmp_room ctx func u /\
   (!inst w p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_operands = [Lit w] /\
     FLOOKUP u.vs_allocas inst.inst_id = SOME (p,n) ==> n = w2n w)` by
    (fs[decode_site_resources_def] >> first_assum ACCEPT_TAC) >>
  `?oid root sz. oid < q.cs_next_id /\
    FLOOKUP u.vs_allocas oid = SOME (root,sz) /\
    root <= dd /\ dd+type_memory_bytes ce child_ty <= root+sz` by
    (qexistsl_tac [`oid`,`root`,`sz`] >>
     `FLOOKUP u.vs_allocas oid = SOME (root,sz)` by
       metis_tac[allocation_growth_old] >> simp[] >> decide_tac) >>
  `B+P <= dd \/ dd+type_memory_bytes ce child_ty <= B` by decide_tac >>
  suspend "scratch"
QED

Resume abi_decode_typed_child_entry[scratch]:
  markerLib.RESUME_TAC >>
  `!id p n. q.cs_next_id <= id /\ id < r.cs_next_id /\
    FLOOKUP u.vs_allocas id = SOME (p,n) ==> B+P <= p \/ p+n <= B` by
    (rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
     >- (`s.vs_alloca_next <= p` by metis_tac[allocation_growth_new] >> decide_tac) >>
     `FLOOKUP u.vs_allocas id = SOME x` by metis_tac[allocation_growth_old] >>
     gvs[] >>
     `st.cs_next_id <= id /\ id < fin.cs_next_id` by decide_tac >>
     qpat_x_assum `!id p n. st.cs_next_id <= id /\ id < fin.cs_next_id /\
       FLOOKUP s.vs_allocas id = SOME (p,n) ==> B+P <= p \/ n+p <= B`
       drule_all >> simp[]) >>
  asm_rewrite_tac[] >>
  qmatch_assum_rename_tac `FLOOKUP u.vs_allocas child_oid = SOME (child_root,child_size)` >>
  qexistsl_tac [`child_oid`,`child_root`,`child_size`] >> asm_rewrite_tac[]
QED

Finalise abi_decode_typed_child_entry[local]

Theorem abi_decode_typed_good_view[local]:
  evaluate_type env ty = SOME tv ==>
  (^decoder_good <=>
   sb <= H /\
   (is_dynamic (vyper_to_abi_type env ty) \/
     static_length (vyper_to_abi_type env ty) <= LENGTH (DROP sb (TAKE H snap))) /\
   abi_decode_source_accepts env ty
     (abi_decode_source_view (vyper_to_abi_type env ty) (TAKE H snap) sb) v)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (simp[abi_decode_source_view_def, abi_decode_source_accepts_def] >>
      eq_tac >> strip_tac >> simp[] >>
      irule (cj 1 abi_to_vyper_well_typed) >> metis_tac[]) >>
  Cases_on `sb <= H` >> fs[LENGTH_DROP] >>
  Cases_on `static_length (vyper_to_abi_type env ty) <= LENGTH (DROP sb (TAKE H snap))` >>
  fs[LENGTH_DROP] >>
  mp_tac (Q.SPECL [`vyper_to_abi_type env ty`, `DROP sb (TAKE H snap)`]
    static_decode_valid_suffix) >>
  (impl_tac >- simp[LENGTH_DROP]) >> strip_tac >>
  Cases_on `vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP sb (TAKE H snap))` >>
  simp[abi_decode_source_view_def, abi_decode_source_accepts_def] >>
  mp_tac (Q.SPECL [`vyper_to_abi_type env ty`, `DROP sb (TAKE H snap)`]
    static_dec_suffix) >>
  (impl_tac >- simp[LENGTH_DROP]) >> strip_tac >> simp[] >>
  eq_tac >> strip_tac >> simp[] >>
  irule (cj 1 abi_to_vyper_well_typed) >> metis_tac[]
QED

(* The observation retains ambient state while Members owns operand frames. *)
val recursive_state = ``\u:venom_state.
  fmp_room ctx func u /\ allocation_growth s u /\ decode_static_frame s u /\
  mem_bytes_at B P u.vs_memory = snap /\
  (!p. keep_word p ==> mload p u = mload p s) /\
  (?fp. (!p n. MEM (p,n) fp <=> ?inst.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      st.cs_next_id <= inst.inst_id /\ inst.inst_id < fin.cs_next_id /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME(p,n)) /\
    abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::fp) s u)``;

val child_result = snd (dest_imp (concl (Q.INST
  [`env` |-> `child_env`, `sf` |-> `child_sf`,
   `ty` |-> `child_ty`, `tv` |-> `child_tv`,
   `dst` |-> `cd`, `src` |-> `cs`, `st` |-> `q`, `fin` |-> `r`,
   `s` |-> `u`, `sb` |-> `cb`, `d` |-> `dd`]
  abi_decode_typed_scalar_memory)));
val child_normal = snd (strip_exists
  (fst (dest_disj (concl (BETA_RULE (ASSUME child_result))))));

Theorem abi_decode_typed_recursive_state_initial[local]:
  ^parent_entry ==> ^recursive_state s
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  asm_rewrite_tac[allocation_growth_refl, decode_static_frame_refl] >>
  qspecl_then [`func`,`st.cs_next_id`,`fin.cs_next_id`,`s.vs_allocas`]
    (strip_assume_tac o BETA_RULE) abi_decode_actual_footprint_exists >>
  qexists_tac `fp` >> fs[abi_decode_footprint_frame_refl]
QED

Theorem abi_decode_typed_recursive_state_admin[local]:
  ^recursive_state u /\ u.vs_memory = v.vs_memory /\ decode_static_frame u v /\
  v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next ==>
  ^recursive_state v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `v.vs_fmp = u.vs_fmp /\ v.vs_call_ctx = u.vs_call_ctx /\
   v.vs_data_section = u.vs_data_section` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `fmp_room ctx func v` by metis_tac[fmp_room_fields] >>
  `allocation_growth s v` by
    (fs[allocation_growth_def] >> first_assum ACCEPT_TAC) >>
  `decode_static_frame s v` by metis_tac[decode_static_frame_trans] >>
  `mem_bytes_at B P v.vs_memory = snap` by fs[] >>
  `!p. keep_word p ==> mload p v = mload p s` by fs[mload_def] >>
  asm_rewrite_tac[] >>
  qexists_tac `fp` >> fs[abi_decode_footprint_frame_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_decode_typed_recursive_state_child[local]:
  ^recursive_state u /\ ^child_normal /\
  st.cs_next_id <= q.cs_next_id /\ r.cs_next_id <= fin.cs_next_id /\
  d <= dd /\ dd+type_memory_bytes ce child_ty <= d+type_memory_bytes ce ty ==>
  ^recursive_state t
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `allocation_growth s t` by metis_tac[allocation_growth_trans] >>
  `decode_static_frame s t` by metis_tac[decode_static_frame_trans] >>
  `!p. keep_word p ==> mload p t = mload p s` by metis_tac[] >>
  asm_rewrite_tac[] >>
  irule (BETA_RULE abi_decode_actual_frame_accumulate) >>
  goal_assum (drule_at (Pat `abi_decode_footprint_frame _ s u`)) >>
  goal_assum (drule_at (Pat `abi_decode_footprint_frame _ u t`)) >>
  qexistsl_tac [`r.cs_next_id`,`q.cs_next_id`] >> asm_rewrite_tac[]
QED
Theorem abi_decode_typed_prefix_append[local]:
  tuple_in_memory vs tvs d u.vs_memory /\ values_have_types tvs vs /\
  val_in_memory tv v (d+type_memory_size_list tvs) t.vs_memory /\
  abi_decode_footprint_frame ((d+type_memory_size_list tvs,m)::scratch) u t /\
  alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP u.vs_allocas id) /\
  oid < lo /\ FLOOKUP u.vs_allocas oid = SOME(root,cap) /\
  root <= d /\ d+type_memory_size_list tvs <= root+cap /\
  (!p n. MEM(p,n) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME(p,n)) ==>
  tuple_in_memory (vs++[v]) (tvs++[tv]) d t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at d (type_memory_size_list tvs) t.vs_memory =
   mem_bytes_at d (type_memory_size_list tvs) u.vs_memory` by
    (irule (cj 2 calldata_child_preserves_allocated_region) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`root`,`cap`,`d+type_memory_size_list tvs`,`hi`,`lo`,`oid`,`scratch`,`m`] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `tuple_val_wf vs tvs` by metis_tac[cj 2 value_has_type_val_wf] >>
  `tuple_in_memory vs tvs d t.vs_memory` by
    (irule (cj 5 val_in_memory_mem_agree_proof) >> asm_rewrite_tac[] >>
     qexists_tac `u.vs_memory` >> asm_rewrite_tac[]) >>
  `LENGTH vs = LENGTH tvs` by fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  simp[typed_memory_tuple_append, val_in_memory_def]
QED
val member_source_position = ``sb + abi_decode_member_offset
  (vyper_to_abi_type env ty) (DROP sb (TAKE H snap)) ao``;
val member_source_good = concl (INST [``sb:num`` |-> member_source_position]
  (ASSUME decoder_good));

Theorem abi_decode_typed_member_good_view[local]:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty /\
  LENGTH snap = P /\ H <= P /\ sb <= H /\
  sb+ao+abi_member_head_size (vyper_to_abi_type env ty) <= H ==>
  (^member_source_good <=>
   abi_decode_source_accepts env ty
     (abi_decode_member_bytes (vyper_to_abi_type env ty)
       (DROP sb (TAKE H snap)) (DROP ao (DROP sb (TAKE H snap)))) v)
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  mp_tac (INST [``sb:num`` |-> member_source_position] abi_decode_typed_good_view) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then SUBST1_TAC >>
  `abi_decode_member_bytes (vyper_to_abi_type env ty)
     (DROP sb (TAKE H snap)) (DROP ao (DROP sb (TAKE H snap))) =
   abi_decode_source_view (vyper_to_abi_type env ty) (TAKE H snap)
     ^member_source_position` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     simp[abi_decode_member_bytes_def, abi_decode_source_view_def,
       abi_decode_member_offset_def, DROP_DROP_T, ADD_COMM]) >>
  asm_rewrite_tac[] >> Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (simp[abi_decode_member_offset_def] >> eq_tac >- simp[] >>
      strip_tac >>
      `!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem` by
        metis_tac[abi_decode_coherent_no_zero_array] >>
      `32 <= LENGTH (abi_decode_source_view (vyper_to_abi_type env ty)
          (TAKE H snap) ^member_source_position)` by
        (irule abi_valid_dynamic_head_min >>
         fs[abi_decode_source_accepts_def] >> metis_tac[]) >>
      fs[abi_decode_source_view_def, LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >>
      decide_tac) >>
  simp[abi_decode_member_offset_def] >>
  `sb+ao <= H /\ static_length (vyper_to_abi_type env ty) <=
    LENGTH (DROP (sb+ao) (TAKE H snap))` by
    (fs[abi_member_head_size_def, LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >> decide_tac) >>
  simp[]
QED

Theorem abi_decode_typed_snapshot_head_word[local]:
  H <= P /\ sb+ao+32 <= H /\ mem_bytes_at B P u.vs_memory = snap ==>
  w2n (mload (B+sb+ao) u) =
    abi_head_word (DROP ao (DROP sb (TAKE H snap)))
Proof
  strip_tac >>
  `mem_bytes_at (B+(sb+ao)) 32 u.vs_memory =
   TAKE 32 (DROP (sb+ao) snap)` by
    (qspecl_then [`B`,`sb+ao`,`32`,`P`,`u.vs_memory`] mp_tac mem_bytes_at_window >>
     simp[] >> decide_tac) >>
  `TAKE 32 (DROP ao (DROP sb (TAKE H snap))) =
   TAKE 32 (DROP (sb+ao) snap)` by
    (simp_tac (srw_ss()) [DROP_DROP_T, DROP_TAKE, TAKE_TAKE_MIN, ADD_COMM] >>
     `MIN 32 (H-(sb+ao)) = 32` by simp[MIN_DEF] >> simp[]) >>
  fs[abi_head_word_def, dec_number_def, dest_NumV_def, mem_bytes_at_def,
    mload_def, ADD_ASSOC]
QED

Theorem abi_decode_typed_coarse_frame[local]:
  (?afp. (!p n. MEM(p,n) afp <=> ?inst.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      st.cs_next_id <= inst.inst_id /\ inst.inst_id < fin.cs_next_id /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME(p,n)) /\
    abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::afp) s t) ==>
  ?fp. (!p n. MEM(p,n) fp <=> ?id.
      st.cs_next_id <= id /\ id < fin.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME(p,n)) /\
    abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::fp) s t
Proof
  strip_tac >>
  qspecl_then [`st.cs_next_id`,`fin.cs_next_id`,`t.vs_allocas`]
    strip_assume_tac abi_decode_mem_owned_footprint_exists >>
  qexists_tac `fp` >> asm_rewrite_tac[] >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `(d,type_memory_bytes ce ty)::afp` >> asm_rewrite_tac[] >>
  simp[] >> rpt strip_tac
  >- (qexistsl_tac [`d`,`type_memory_bytes ce ty`] >> simp[]) >>
  qexistsl_tac [`d'`,`sz`] >> simp[] >> metis_tac[]
QED

Theorem abi_decode_typed_recursive_normal[local]:
  ^recursive_state t /\ gas_path_mem ctx func s 0 (OK t) /\ ^decoder_good /\
  val_in_memory tv v d t.vs_memory /\ decode_site_resources ctx func t /\
  alloca_history func t /\ fresh_vars_wrt limit t /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s) /\
  (!id. id < st.cs_next_id \/ fin.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  t.vs_current_bb = fin.cs_current_bb /\
  t.vs_inst_idx = LENGTH fin.cs_current_insts /\ ~t.vs_halted ==>
  ^parent_result
Proof
  simp_tac bool_ss [LET_THM, decode_site_resources_def] >> strip_tac >>
  `?fp. (!p n. MEM(p,n) fp <=> ?id.
      st.cs_next_id <= id /\ id < fin.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME(p,n)) /\
    abi_decode_footprint_frame ((d,type_memory_bytes ce ty)::fp) s t` by
    (irule abi_decode_typed_coarse_frame >> metis_tac[]) >>
  disj1_tac >> qexistsl_tac [`t`,`v`] >> asm_rewrite_tac[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val typed_prefix_observation = ``\(G:num -> vyperValue$value -> bool) j (u:venom_state).
  ^recursive_state u /\
  ?vs. LENGTH vs = j /\ j <= LENGTH tvs /\
    (!i. i < j ==> G i (EL i vs)) /\
    tuple_in_memory vs (TAKE j tvs) d u.vs_memory``;

Theorem abi_decode_typed_prefix_initial[local]:
  ^parent_entry ==> ^typed_prefix_observation G 0 s
Proof
  strip_tac >> drule abi_decode_typed_recursive_state_initial >> strip_tac >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >>
  qexists_tac `[]` >> simp[val_in_memory_def]
QED

Theorem abi_decode_typed_prefix_admin[local]:
  ^typed_prefix_observation G j u /\ u.vs_memory = v.vs_memory /\
  decode_static_frame u v /\ v.vs_allocas = u.vs_allocas /\
  v.vs_alloca_next = u.vs_alloca_next ==>
  ^typed_prefix_observation G j v
Proof
  simp_tac bool_ss [] >> strip_tac >>
  `^recursive_state v` by
    (irule abi_decode_typed_recursive_state_admin >>
     qexists_tac `u` >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> qexists_tac `vs` >> fs[]
QED

Theorem abi_decode_typed_member_metadata[local]:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  EVERY (assignable_type env) tys /\ EVERY (abi_decode_bytes_widths env) tys /\
  infos = abi_decoder_member_infos sf ce tys /\
  infos = pre++(di,a,m)::post /\ i = LENGTH pre ==>
  i < LENGTH tys /\ i < LENGTH tvs /\
  abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
  assignable_type env (EL i tys) /\ abi_decode_bytes_widths env (EL i tys) /\
  di = type_to_abi_dec_info sf ce (EL i tys) /\
  a = abi_embedded_static_size ce.ce_struct_fields (EL i tys) /\
  m = type_memory_bytes ce (EL i tys) /\
  pre = abi_decoder_member_infos sf ce (TAKE i tys) /\
  SUM (MAP (\(di,a,m). m) pre) = type_memory_size_list (TAKE i tvs) /\
  SUM (MAP (\(di,a,m). a) pre)+a <= SUM (MAP (\(di,a,m). a) infos) /\
  SUM (MAP (\(di,a,m). m) pre)+m <= SUM (MAP (\(di,a,m). m) infos)
Proof
  strip_tac >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH infos = LENGTH tys /\ LENGTH infos = LENGTH pre + SUC(LENGTH post)` by
    metis_tac[abi_decoder_member_infos_def, LENGTH_MAP, LENGTH_APPEND, LENGTH] >>
  `i < LENGTH tys /\ i < LENGTH tvs` by decide_tac >>
  `EL i infos = (di,a,m)` by fs[EL_APPEND_EQN] >>
  `di = type_to_abi_dec_info sf ce (EL i tys) /\
   a = abi_embedded_static_size ce.ce_struct_fields (EL i tys) /\
   m = type_memory_bytes ce (EL i tys)` by fs[abi_decoder_member_infos_def, EL_MAP] >>
  `abi_decoder_coherent ce env sf (EL i tys) (EL i tvs) /\
   assignable_type env (EL i tys) /\ abi_decode_bytes_widths env (EL i tys)` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[]) >>
  `pre = abi_decoder_member_infos sf ce (TAKE i tys)` by
    (`pre = TAKE i infos` by fs[TAKE_LENGTH_APPEND] >>
     simp[abi_decoder_member_infos_def, GSYM MAP_TAKE]) >>
  `LIST_REL (abi_decoder_coherent ce env sf) (TAKE i tys) (TAKE i tvs)` by
    metis_tac[LIST_REL_TAKE] >>
  mp_tac (Q.SPECL [`TAKE i tys`,`TAKE i tvs`] abi_decoder_member_infos_layout) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  fs[abi_decoder_member_infos_def, MAP_MAP_o, combinTheory.o_DEF,
    pairTheory.LAMBDA_PROD, MAP_APPEND, SUM_APPEND]
QED

Theorem abi_decode_typed_members_layout[local]:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  EVERY (assignable_type env) tys ==>
  SUM (MAP (\(di,a,m). a) (abi_decoder_member_infos sf ce tys)) <=
    SUM (MAP (\(di,a,m). m) (abi_decoder_member_infos sf ce tys)) /\
  EVERY (\(di,a,m). (dec_info_needs_offset di ==> 32 <= a) /\
    (!c. di = DecPrimWord c ==> 32 <= a)) (abi_decoder_member_infos sf ce tys)
Proof
  Induct_on `tys` >> Cases_on `tvs` >>
  simp[abi_decoder_member_infos_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all abi_decode_embedded_head_le_memory >>
  drule abi_decode_mem_descriptor_head >> simp[] >> strip_tac >> decide_tac
QED

val members_entry = ``\q (u:venom_state).
  mem_bytes_at B H u.vs_memory = mem_bytes_at B H prepared.vs_memory /\
  u.vs_call_ctx = prepared.vs_call_ctx /\
  u.vs_data_section = prepared.vs_data_section /\
  fresh_vars_wrt limit u /\ alloca_inv u /\ alloca_room ctx func u /\
  alloca_history func u /\
  (!inst w p n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME(p,n) ==> n = w2n w) /\
  allocation_growth prepared u /\ ~u.vs_halted /\
  u.vs_current_bb = q.cs_current_bb /\
  u.vs_inst_idx = LENGTH q.cs_current_insts /\ B+H <= u.vs_alloca_next /\
  eval_operand src u = SOME(n2w sb) /\ eval_operand dst u = SOME(n2w d) /\
  eval_operand base_op u = SOME(n2w B) /\ eval_operand hi u = SOME(n2w H)``;

Theorem abi_decode_typed_members_entry_child[local]:
  H <= P /\ ^members_entry q u /\ mem_bytes_at B P u.vs_memory = snap /\
  ^child_normal /\
  EVERY (abi_decoder_operand_live q.cs_next_var) [src;dst;base_op;hi] ==>
  ^members_entry r t
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `mem_bytes_at B H t.vs_memory = mem_bytes_at B H u.vs_memory` by
    (mp_tac (Q.SPECL [`B`,`B`,`P`,`t.vs_memory`,`u.vs_memory`,`0`,`H`]
      valueEncodingPropsTheory.mem_bytes_at_translated_window) >> simp[]) >>
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_data_section = u.vs_data_section` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `allocation_growth prepared t` by metis_tac[allocation_growth_trans] >>
  `B+H <= t.vs_alloca_next` by metis_tac[allocation_growth_next, LESS_EQ_TRANS] >>
  `eval_operand src t = SOME(n2w sb) /\ eval_operand dst t = SOME(n2w d) /\
   eval_operand base_op t = SOME(n2w B) /\ eval_operand hi t = SOME(n2w H)` by
    (fs[EVERY_DEF] >> metis_tac[]) >>
  asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_typed_prefix_success[local]:
  ^parent_entry /\ ^typed_prefix_observation G j u /\ ^child_normal /\
  st.cs_next_id <= q.cs_next_id /\ r.cs_next_id <= fin.cs_next_id /\
  j < LENGTH tvs /\ child_tv = EL j tvs /\
  dd = d+type_memory_size_list (TAKE j tvs) /\
  dd+type_memory_bytes ce child_ty <= d+type_memory_bytes ce ty /\
  G j v /\ (!i w. i < LENGTH tvs /\ G i w ==> value_has_type (EL i tvs) w) ==>
  ^typed_prefix_observation G (SUC j) t
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `^recursive_state u` by (simp_tac bool_ss [] >> asm_rewrite_tac[]) >>
  `^recursive_state t` by
    (mp_tac abi_decode_typed_recursive_state_child >>
     simp_tac bool_ss [] >>
     (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  qpat_x_assum `?vs. LENGTH vs = j /\ _` strip_assume_tac >>
  `LENGTH vs = LENGTH (TAKE j tvs)` by simp[LENGTH_TAKE, MIN_DEF] >>
  `values_have_types (TAKE j tvs) vs` by
    (simp[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
     rpt strip_tac >> fs[EL_TAKE, LENGTH_TAKE, MIN_DEF] >> metis_tac[]) >>
  qpat_assum `?oid root sz. _`
    (qx_choosel_then [`outid`,`outroot`,`outcap`] strip_assume_tac) >>
  `FLOOKUP u.vs_allocas outid = SOME(outroot,outcap)` by
    metis_tac[allocation_growth_old] >>
  `outid < q.cs_next_id /\ outroot <= d /\
   d+type_memory_size_list (TAKE j tvs) <= outroot+outcap` by decide_tac >>
  qpat_x_assum `?fp. (!p n. MEM(p,n) fp <=> ?id.
    q.cs_next_id <= id /\ id < r.cs_next_id /\
    FLOOKUP t.vs_allocas id = SOME(p,n)) /\
    abi_decode_footprint_frame ((dd,type_memory_bytes ce child_ty)::fp) u t`
    (qx_choose_then `scratch` strip_assume_tac) >>
  `tuple_in_memory (vs++[v]) ((TAKE j tvs)++[child_tv]) d t.vs_memory` by
    (mp_tac (Q.INST
       [`vs` |-> `vs`, `tvs` |-> `TAKE j tvs`, `tv` |-> `child_tv`,
        `lo` |-> `q.cs_next_id`, `hi` |-> `r.cs_next_id`,
        `oid` |-> `outid`, `root` |-> `outroot`, `cap` |-> `outcap`,
        `m` |-> `type_memory_bytes ce child_ty`]
       abi_decode_typed_prefix_append) >>
     simp_tac bool_ss [] >> impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >> simp[]) >>
  suspend "append"
QED
Resume abi_decode_typed_prefix_success[append]:
  markerLib.RESUME_TAC >>
  `TAKE (SUC j) tvs = TAKE j tvs++[child_tv]` by
    (simp[GSYM SNOC_EL_TAKE, SNOC_APPEND]) >>
  simp_tac bool_ss [] >> asm_rewrite_tac[] >>
  qexists_tac `vs++[v]` >> simp[LENGTH_APPEND] >>
  conj_tac >- decide_tac >>
  rpt strip_tac >> Cases_on `i < j`
  >- (simp[EL_APPEND_EQN] >> metis_tac[]) >>
  `i = j` by decide_tac >> simp[EL_APPEND_EQN]
QED
Finalise abi_decode_typed_prefix_success[local]

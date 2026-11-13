(* Recursive transports retain the canonical typed memory-decoder boundary. *)
Theory abiDecodeMemTypedRecursive
Ancestors
  abiDecodeMemTyped abiDecoderCoherence abiDecoderReentry abiDecoderSiteEffect
  actualDecoderSites allocationGrowth abiCallerAllocation
  exprSimAbiDecodeMemberExecute extcallDecoderStaticSuffix
  vyperABI contractABI vyperTypeABI vyperTyping
  exprLoweringProps loweringStateRelDefs compileEnv venomState venomInst
  valueEncodingDefs valueEncoding words list arithmetic finite_map

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

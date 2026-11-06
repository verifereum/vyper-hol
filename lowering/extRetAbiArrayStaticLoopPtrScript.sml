(* Finite static-element array loop; concrete compiler phase interfaces. *)
Theory extRetAbiArrayStaticLoopPtr
Ancestors
  extRetAbiArrayHeaderPtr extRetAbiArrayStaticBodyPtr extRetAbiArrayBackedgePtr
  abiEncoderArrayPhaseAppend abiEncoderArrayHeader abiEncoderArrayBodyCode
  abiEncoderCounters abiDecoderLoopEmit fragExec fragGasPathPtr compileEnv emitHelperProps
  ptrDiscipline bodyPtrDefs venomState venomExecSemantics words finite_map
  list rich_list arithmetic pred_set

Theorem abi_array_static_loop_phase_code:
  abi_encode_array_header ip count_op sh = ((hdr,body_lbl,exit_lbl),sb) /\
  abi_encode_array_static_body ip src dst ei asz msz sb = (idx,st) /\
  abi_decode_loop_suffix ip idx hdr exit_lbl st = ((),se) /\
  fn_has_code sh se fn ==>
  fn_has_code sh sb fn /\ fn_has_code sb st fn /\ fn_has_code st se fn /\
  sb.cs_current_bb = body_lbl /\ sb.cs_current_insts = [] /\
  sh.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= st.cs_next_var
Proof
  strip_tac >>
  `cs_extends sh sb /\ cs_extends sb st /\ cs_extends st se` by
    metis_tac[abi_encoder_appends_result, abi_encode_array_phase_append] >>
  `fn_has_code sh sb fn /\ fn_has_code sb st fn /\ fn_has_code st se fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `sb.cs_next_var <= st.cs_next_var` by
    (drule abi_encode_array_static_body_trace >> strip_tac >>
     drule abi_encode_array_addresses_shape >> strip_tac >>
     mp_tac abi_encoder_counters_mono_static_info >>
     simp[abi_encoder_counters_mono_def] >>
     disch_then (qspecl_then [`SND (SND coords)`, `SND (FST coords)`, `ei`, `prepared`] mp_tac) >>
     simp[] >> decide_tac) >>
  gvs[abi_encode_array_header_shape]
QED

Theorem abi_array_static_prefix_suc:
  j < LENGTH avs ==>
  header ++ FLAT (MAP f (TAKE (j+1) avs)) =
    (header ++ FLAT (MAP f (TAKE j avs))) ++ f (EL j avs)
Proof
  strip_tac >> simp[TAKE_EL_SNOC, MAP_SNOC, FLAT_SNOC, APPEND_ASSOC]
QED

(* Header execution exports the old-variable frame, unlike the smaller scalar
   convenience corollary. No memory or allocation is changed in this phase. *)
Theorem abi_array_loop_header_frame:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  fn_has_code sh sb fn /\ not_fresh_at sh cv /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ptr_covers G tn ip s 32 /\ lookup_var ip s = SOME p /\
  ~ctx_has_dalloca ctx /\
  (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  lookup_var cv s = SOME (n2w n) /\
  mload (w2n p) s = n2w j /\ j <= n /\ n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = (if j<n then body_lbl else exit_lbl) /\
    sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qabbrev_tac `iv = STRING #"%" (toString sh.cs_next_var)` >>
  qabbrev_tac `cmp = STRING #"%" (toString (sh.cs_next_var+1))` >>
  qabbrev_tac `done = STRING #"%" (toString (sh.cs_next_var+2))` >>
  `!v. not_fresh_at sh v ==> v <> iv /\ v <> cmp /\ v <> done` by
    (gvs[not_fresh_at_def, Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  drule_all abi_encode_array_header_code_ptr >> strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w n) /\ cv <> iv` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `bb.bb_instructions = abi_encode_array_header_insts (sh.cs_next_id+1)
    (Var ip) (Var cv) iv cmp done body_lbl exit_lbl` by
    simp[Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all (abi_encode_array_header_counted_ptr |>
    Q.INST [`count_op` |-> `Var cv`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`,
    `jump_to (if j<n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done j n s)`] >>
  simp[jump_to_def, abi_encode_array_header_state_def, update_var_def] >>
  rpt strip_tac >>
  `v <> iv /\ v <> cmp /\ v <> done` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

(* PC-independent invariant: only the index and encoded prefix advance. *)
Definition abi_array_static_loop_inv_def:
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j G tn s <=>
    ~s.vs_halted /\
    lookup_var ip s = SOME p /\ lookup_var src s = SOME a /\
    lookup_var dst s = SOME b /\ lookup_var cv s = SOME (n2w (LENGTH avs)) /\
    ptr_covers G tn ip s 32 /\ ptr_covers G tn src s scap /\ ptr_covers G tn dst s dcap /\
    mload (w2n p) s = n2w j /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN tn.t_mem) /\
    op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    (!mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
      abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
        (w2n a) scap mem') /\
    mem_bytes_at (w2n b) (32+j*asz) s.vs_memory =
      header ++ FLAT (MAP (enc ty) (TAKE j avs)) /\
    (!i. w2n b <= i /\ i < w2n b+32+j*asz ==> i NOTIN tn.t_mem)
End

Theorem abi_array_static_loop_inv_memory_frame[local]:
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j G tn s /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  ~sf.vs_halted /\ sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
  (!v. not_fresh_at sh v ==>
    lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)) ==>
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j Gf tnf sf
Proof
  simp[abi_array_static_loop_inv_def, mload_def, ptr_covers_def, op_prov_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_array_static_loop_step:
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei asz msz sb = (idx,st) /\
  abi_decode_loop_suffix (Var ip) idx hdr exit_lbl st = ((),se) /\
  fn_has_code sh se fn /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\
  ~ctx_has_dalloca ctx /\
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j G tn s /\
  s.vs_current_bb = body_lbl /\ s.vs_inst_idx = 0 /\
  j < LENGTH avs /\ LENGTH avs < dimword(:256) /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= dcap /\
  32+(j+1)*asz <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  w2n p+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= w2n p \/ w2n p+32 <= w2n a) /\
  (w2n p+32 <= w2n b \/ w2n b+dcap <= w2n p) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = hdr /\ sf.vs_inst_idx = 0 /\
    abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header (j+1) Gf tnf sf /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  `!v. not_fresh_at sh v ==> not_fresh_at sb v /\ not_fresh_at st v` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qpat_assum `abi_array_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_array_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
   not_fresh_at sb ip /\ not_fresh_at sb src /\ not_fresh_at sb dst` by (simp[] >> metis_tac[]) >>
  drule_all compile_abi_array_static_body_counted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all abi_array_static_body_prefix_frame >> strip_tac >>
  `mem_bytes_at (w2n b) (32+(j+1)*asz) sf.vs_memory =
    header ++ FLAT (MAP (enc ty) (TAKE (j+1) avs))` by
    (asm_simp_tac bool_ss [abi_array_static_prefix_suc]) >>
  `lookup_var ip sf = SOME p /\ lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b` by metis_tac[] >>
  Q.SUBGOAL_THEN
   `?Gh th h.
    gas_path_ptr D 0 ctx fn PG Gf tnf sf 0 Gh th (OK h) /\
    h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\ ~h.vs_halted /\
    h.vs_allocas = sf.vs_allocas /\ h.vs_alloca_next = sf.vs_alloca_next /\
    h.vs_fmp = sf.vs_fmp /\
    lookup_var ip h = SOME p /\ ptr_covers Gh th ip h 32 /\
    mload (w2n p) h = n2w (j+1) /\
    (!i. w2n p <= i /\ i < w2n p+32 ==> i NOTIN th.t_mem) /\
    lookup_var src h = SOME a /\ ptr_covers Gh th src h scap /\
    lookup_var dst h = SOME b /\ ptr_covers Gh th dst h dcap /\
    mem_bytes_at (w2n b) (32+(j+1)*asz) h.vs_memory =
      header ++ FLAT (MAP (enc ty) (TAKE (j+1) avs)) /\
    (!i. w2n b <= i /\ i < w2n b+(32+(j+1)*asz) ==> i NOTIN th.t_mem) /\
    mem_agree_outside {i | w2n p <= i /\ i < w2n p+32} h.vs_memory sf.vs_memory /\
    (!i. i NOTIN {i | w2n p <= i /\ i < w2n p+32} ==>
      (i IN th.t_mem <=> i IN tnf.t_mem)) /\
    th.t_stor = tnf.t_stor /\ th.t_trans = tnf.t_trans /\
    (!v. not_fresh_at st v ==>
      lookup_var v h = lookup_var v sf /\ FLOOKUP Gh v = FLOOKUP Gf v /\
      op_taint th (Var v) = op_taint tnf (Var v)) /\
    (!mem'. mem_agree_outside th.t_mem h.vs_memory mem' ==>
      abi_encoder_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
        (w2n a) scap mem')` strip_assume_tac
  >- (irule abi_decode_loop_suffix_source_prefix_counted_ptr >>
      `j+1 < dimword(:256)` by decide_tac >>
      `!i. w2n b <= i /\ i < w2n b+(32+(j+1)*asz) ==> i NOTIN tnf.t_mem` by
        (pure_rewrite_tac[ADD_ASSOC] >> first_assum MATCH_ACCEPT_TAC) >>
      Q.SUBGOAL_THEN
        `w2n b+(32+(j+1)*asz) <= w2n p \/ w2n p+32 <= w2n b` assume_tac
      >- (qpat_x_assum `w2n p+32 <= w2n b \/ _` mp_tac >> decide_tac) >>
      asm_simp_tac bool_ss [] >> metis_tac[]) >>
  qexistsl_tac [`Gh`,`th`,`h`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[]) >>
  `lookup_var cv h = SOME (n2w (LENGTH avs)) /\
   op_taint th (Var cv) = {} /\ op_prov Gh (Var cv) = NONE` by
    (simp[op_prov_def] >> gvs[op_prov_def] >> metis_tac[]) >>
  asm_simp_tac bool_ss [abi_array_static_loop_inv_def, ADD_ASSOC] >>
  metis_tac[]
QED

Theorem abi_array_static_loop_counted_ptr:
  !r j G tn s.
  abi_encode_array_header (Var ip) (Var cv) sh = ((hdr,body_lbl,exit_lbl),sb) /\
  abi_encode_array_static_body (Var ip) (Var src) (Var dst) ei asz msz sb = (idx,st) /\
  abi_decode_loop_suffix (Var ip) idx hdr exit_lbl st = ((),se) /\
  fn_has_code sh se fn /\
  not_fresh_at sh ip /\ not_fresh_at sh src /\
  not_fresh_at sh dst /\ not_fresh_at sh cv /\ ~ctx_has_dalloca ctx /\
  abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j G tn s /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  LENGTH avs = r+j /\ LENGTH avs < dimword(:256) /\
  ((ei = AbiPrimWord /\ asz = 32) \/ ei = AbiCopy asz) /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= dcap /\
  32+LENGTH avs*asz <= dcap /\
  w2n a+scap < dimword(:256) /\ w2n b+dcap < dimword(:256) /\
  w2n p+32 < dimword(:256) /\
  (w2n a+scap <= w2n b \/ w2n b+dcap <= w2n a) /\
  (w2n a+scap <= w2n p \/ w2n p+32 <= w2n a) /\
  (w2n p+32 <= w2n b \/ w2n b+dcap <= w2n p) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = exit_lbl /\ sf.vs_inst_idx = 0 /\
    abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header
      (LENGTH avs) Gf tnf sf /\
    mem_bytes_at (w2n b) (32+LENGTH avs*asz) sf.vs_memory =
      header ++ FLAT (MAP (enc ty) avs) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. not_fresh_at sh v ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  Induct >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- suspend "exit"
  >> suspend "more"
QED

Resume abi_array_static_loop_counted_ptr[exit]:
  `j = LENGTH avs` by decide_tac >>
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  qpat_assum `abi_array_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_array_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `j <= LENGTH avs` by decide_tac >>
  drule_all abi_array_loop_header_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j Gf tnf sf` by
    (irule abi_array_static_loop_inv_memory_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`G`,`s`,`sh`,`tn`] >> simp[]) >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >>
  qpat_x_assum `LENGTH avs = 0+j` kall_tac >>
  gvs[abi_array_static_loop_inv_def]
QED

Resume abi_array_static_loop_counted_ptr[more]:
  drule_all abi_array_static_loop_phase_code >> strip_tac >>
  qpat_assum `abi_array_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_array_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `j < LENGTH avs /\ j <= LENGTH avs` by decide_tac >>
  drule_all abi_array_loop_header_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `abi_array_static_loop_inv ip src dst cv p a b scap dcap ei ty avs asz msz header j Gf tnf sf` by
    (irule abi_array_static_loop_inv_memory_frame >>
     conj_tac >- simp[] >> qexistsl_tac [`G`,`s`,`sh`,`tn`] >> simp[]) >>
  `sf.vs_current_bb = body_lbl` by simp[] >>
  `32+(j+1)*asz <= dcap` by
    (`j+1 <= LENGTH avs` by decide_tac >>
     `(j+1)*asz <= LENGTH avs*asz` by simp[] >> decide_tac) >>
  drule_all abi_array_static_loop_step >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `LENGTH avs = SUC remaining+j` >>
  `LENGTH avs = remaining+(j+1)` by decide_tac >>
  qpat_x_assum `!j G tn s. _` (qspecl_then [`j+1`,`Gf'`,`tnf'`,`sf'`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  strip_tac >>
  qexistsl_tac [`Gf''`,`tnf''`,`sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`,`sf`,`tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`,`sf'`,`tnf'`] >> simp[]) >>
  qpat_x_assum `abi_array_static_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Gf'' tnf'' sf''` mp_tac >>
  pure_rewrite_tac[abi_array_static_loop_inv_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Finalise abi_array_static_loop_counted_ptr

(* Conditional complex-member execution and endpoint-owned allocation frames. *)
Theory abiDecodeMemMembers
Ancestors
  abiDecodeMemMemberPointer abiDecoderFrame abiDecoderEffect abiDecoderMemberSetup abiDecoderMemberCode abiDecoderMemberCons
  abiEncoder fragGasPathMem fragGasMode fragExec allocaHistory
  abiDecodeMemBytesGuards venomExecSemantics venomState
  finite_map pred_set list rich_list arithmetic words compileEnv emitHelper
  emitHelperProps exprLoweringProps loweringStateRelDefs

Theorem abi_decode_mem_owned_footprint_exists[local]:
  !lo hi (m:num |-> (num # num)).
    ?fp. !p n. MEM (p,n) fp <=>
      ?id. lo <= id /\ id < hi /\ FLOOKUP m id = SOME (p,n)
Proof
  rpt gen_tac >>
  qexists_tac `MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
    (fmap_to_alist m))` >>
  simp[MEM_MAP, MEM_FILTER, alistTheory.MEM_fmap_to_alist_FLOOKUP] >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >> qexists_tac `FST y` >> simp[]) >>
  strip_tac >> qexists_tac `(id,(p,n))` >> simp[]
QED

Theorem abi_decode_mem_owned_frame_widen[local]:
  abi_decode_footprint_frame ((d,n)::fp) s t /\
  (!p k. MEM (p,k) fp ==>
    ?id. child_lo <= id /\ id < child_hi /\
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
  (!id. child_lo <= id /\ id < child_hi ==>
    FLOOKUP u.vs_allocas id = FLOOKUP t.vs_allocas id) /\
  (!p k. MEM (p,k) final_fp <=>
    ?id. lo <= id /\ id < hi /\ FLOOKUP u.vs_allocas id = SOME (p,k)) /\
  lo <= child_lo /\ child_hi <= hi /\
  out <= d /\ d+n <= out+sz ==>
  abi_decode_footprint_frame ((out,sz)::final_fp) s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `(d,n)::fp` >> simp[] >>
  rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`out`,`sz`] >> simp[]) >>
  qexistsl_tac [`d'`,`sz'`] >> simp[] >>
  first_x_assum drule >> strip_tac >>
  disj2_tac >> qexists_tac `id` >> simp[] >> decide_tac
QED

Theorem abi_decode_mem_owned_frames_compose:
  abi_decode_footprint_frame ((d1,n1)::fp1) s t /\
  abi_decode_footprint_frame ((d2,n2)::fp2) t u /\
  (!p n. MEM (p,n) fp1 <=> ?id. lo <= id /\ id < mid /\
    FLOOKUP t.vs_allocas id = SOME (p,n)) /\
  (!p n. MEM (p,n) fp2 <=> ?id. mid <= id /\ id < hi /\
    FLOOKUP u.vs_allocas id = SOME (p,n)) /\
  (!id. lo <= id /\ id < mid ==>
    FLOOKUP u.vs_allocas id = FLOOKUP t.vs_allocas id) /\
  lo <= mid /\ mid <= hi /\
  out <= d1 /\ d1+n1 <= out+sz /\ out <= d2 /\ d2+n2 <= out+sz ==>
  ?fp. (!p n. MEM (p,n) fp <=> ?id. lo <= id /\ id < hi /\
      FLOOKUP u.vs_allocas id = SOME (p,n)) /\
    abi_decode_footprint_frame ((out,sz)::fp) s u
Proof
  strip_tac >>
  qspecl_then [`lo`,`hi`,`u.vs_allocas`] strip_assume_tac
    abi_decode_mem_owned_footprint_exists >>
  qexists_tac `fp` >> simp[] >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `t` >> conj_tac
  >- (irule abi_decode_mem_owned_frame_widen >>
      goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`mid`,`lo`] >> simp[]) >>
  irule abi_decode_mem_owned_frame_widen >>
  goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
      goal_assum (drule_at Any) >>
  qexistsl_tac [`hi`,`mid`] >> simp[]
QED

Theorem abi_decode_member_setup_path_mem:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword (:256) /\
  fresh_vars_wrt st s /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+ao < dimword (:256) /\ B+sb+ao+32 <= s.vs_alloca_next) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((dyn ==> sb + w2n (mload (B+sb+ao) s) < dimword (:256)) ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand (FST ops) t = SOME
        (n2w (sb + if dyn then w2n (mload (B+sb+ao) s) else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (dyn /\ dimword (:256) <= sb + w2n (mload (B+sb+ao) s) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao MLOAD base_op hi st = (child_src,mid)` >>
  rename1 `emit_op ADD [dst;Lit (n2w vo)] mid = (child_dst,st')` >>
  drule abi_decode_mem_member_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `fn_has_code st mid func /\ fn_has_code mid st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def, same_blocks_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all (SRULE [AC ADD_ASSOC ADD_COMM] abi_decode_mload_member_path_mem) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- suspend "accept" >>
  strip_tac >> first_x_assum irule >> simp[]
QED
Resume abi_decode_member_setup_path_mem[accept]:
  strip_tac >> gvs[] >>
  `eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit (n2w vo)) t = SOME (n2w vo)` by simp[eval_operand_def] >>
  `alloca_inv t` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> metis_tac[]) >>
  `t.vs_current_bb = mid.cs_current_bb /\
   t.vs_inst_idx = LENGTH mid.cs_current_insts` by simp[] >>
  drule_all abi_decode_add_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func s 0 (OK t')` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  qexists_tac `t'` >> gvs[word_add_n2w] >> metis_tac[]
QED
Finalise abi_decode_member_setup_path_mem

Theorem abi_decode_mem_members_anchored[local]:
  !(K:num -> bool). let AS = (\xs. SUM (MAP (\(di,a,m). a) xs));
      MS = (\xs. SUM (MAP (\(di,a,m). m) xs));
      P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H anchor.vs_memory /\
                (!p. K p ==> mload p u = mload p anchor) /\
                u.vs_call_ctx = anchor.vs_call_ctx /\
                u.vs_data_section = anchor.vs_data_section);
      E = (\q u. P u /\ fresh_vars_wrt q u /\ alloca_inv u /\
                alloca_room ctx func u /\ alloca_history func u /\
                ~u.vs_halted /\ u.vs_current_bb = q.cs_current_bb /\
                u.vs_inst_idx = LENGTH q.cs_current_insts /\
                B + H <= u.vs_alloca_next /\
                eval_operand src u = SOME (n2w sb) /\
                eval_operand dst u = SOME (n2w d) /\
                eval_operand bop u = SOME (n2w B) /\
                eval_operand hi u = SOME (n2w H));
      R = (\q r out sz u v.
                E r v /\ u.vs_alloca_next <= v.vs_alloca_next /\
                (!op w. eval_operand op u = SOME w ==> eval_operand op v = SOME w) /\
                (!id. id < q.cs_next_id \/ r.cs_next_id <= id ==>
                   FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
                ?fp. (!p n. MEM (p,n) fp <=>
                        ?id. q.cs_next_id <= id /\ id < r.cs_next_id /\
                             FLOOKUP v.vs_allocas id = SOME (p,n)) /\
                     abi_decode_footprint_frame ((out,sz)::fp) u v);
      Q = (\q r out sz u.
                (?v. gas_path_mem ctx func u 0 (OK v) /\ R q r out sz u v) \/
                (?v. gas_marked_path T ctx func u 0 (Abort Revert_abort v)))
  in
    compile_abi_decode_complex_elems dst src MLOAD bop hi elems ao vo st = ((),final) /\
    hi <> Lit 0w /\ fn_has_code st final func /\ fn_inst_ids_distinct func /\
    E st s /\ sb < dimword (:256) /\ B + H < dimword (:256) /\
    sb + ao + AS elems <= H /\ d + vo + MS elems < dimword (:256) /\
    d + vo + MS elems <= s.vs_alloca_next /\
    EVERY (\(di,a,m). (dec_info_needs_offset di ==> 32 <= a) /\
                          (!c. di = DecPrimWord c ==> 32 <= a)) elems /\
    (!pre di a m post q r cs cd u.
        elems = pre ++ (di,a,m)::post /\
        st.cs_next_id <= q.cs_next_id /\ r.cs_next_id <= final.cs_next_id /\
        compile_abi_decode_to_buf cd cs MLOAD bop hi di q = ((),r) /\
        fn_has_code q r func /\ E q u /\
        abi_decoder_operand_live q.cs_next_var cs /\
        abi_decoder_operand_live q.cs_next_var cd /\
        eval_operand cd u = SOME (n2w (d + vo + MS pre)) /\
        (let off = if dec_info_needs_offset di
                   then w2n (mload (B + sb + ao + AS pre) u)
                   else ao + AS pre
         in sb + off < dimword (:256) /\
            eval_operand cs u = SOME (n2w (sb + off)))
        ==> Q q r (d + vo + MS pre) m u)
    ==> Q st final (d + vo) (MS elems) s
Proof
  map_every qid_spec_tac [`s`,`st`,`final`,`ao`,`vo`] >>
  Induct_on `elems`
  >- suspend "nil" >>
  suspend "cons"
QED
Resume abi_decode_mem_members_anchored[nil]:
  rpt gen_tac >> rpt BasicProvers.LET_ELIM_TAC >>
  gvs[Once compile_abi_decode_to_buf_def, comp_return_def] >>
  simp[Abbr `Q`, Abbr `R`] >> disj1_tac >>
  qexists_tac `s` >> simp[] >>
  conj_tac >- (irule (cj 1 gas_path_mem_rules) >> gvs[Abbr `E`]) >>
  qexists_tac `[]` >> simp[abi_decode_footprint_frame_refl]
QED
Resume abi_decode_mem_members_anchored[cons]:
  pop_assum (mk_asm "ih") >>
  rpt gen_tac >> PairCases_on `h` >> rpt BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `abi_decode_source_opcode MLOAD` by simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code st cs' func` by metis_tac[fn_has_code_split] >>
  `fresh_vars_wrt st s /\ alloca_inv s /\ alloca_history func s /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts /\
   eval_operand src s = SOME (n2w sb) /\
   eval_operand dst s = SOME (n2w d) /\
   eval_operand bop s = SOME (n2w B) /\ B+H <= s.vs_alloca_next` by
    fs[Abbr `E`] >>
  `B+sb+ao < dimword (:256) /\
   (dec_info_needs_offset h0 ==> B+sb+ao+32 <= s.vs_alloca_next)` by
    (Cases_on `dec_info_needs_offset h0` >> fs[Abbr `AS`] >> decide_tac) >>
  `sb < dimword (:256)` by (fs[Abbr `AS`] >> decide_tac) >>
  `(dec_info_needs_offset h0 ==> eval_operand bop s = SOME (n2w B) /\
      B+sb+ao < dimword (:256) /\ B+sb+ao+32 <= s.vs_alloca_next)` by
    metis_tac[] >>
  drule_all abi_decode_member_setup_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `dec_info_needs_offset h0 /\
    dimword (:256) <= sb + w2n (mload (B+sb+ao) s)`
  >- (simp[Abbr `Q`] >> metis_tac[]) >>
  `dec_info_needs_offset h0 ==>
    sb + w2n (mload (B+sb+ao) s) < dimword (:256)` by
      (strip_tac >> fs[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  suspend "child_entry"
QED
Resume abi_decode_mem_members_anchored[child_entry]:
  `alloca_inv t` by metis_tac[localPtrsPropsTheory.alloca_inv_fields] >>
  `alloca_room ctx func t` by
    (irule alloca_room_fields >> qexists_tac `s` >> fs[Abbr `E`]) >>
  `P t` by (fs[Abbr `P`, Abbr `E`] >> metis_tac[mload_def]) >>
  `E cs' t` by (fs[Abbr `E`] >> metis_tac[]) >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `fn_has_code cs' cs'' func` by metis_tac[fn_has_code_split] >>
  `Q cs' cs'' (d+vo) h2 t` by
    (qpat_assum `!pre di a m post q r cs cd u off. _`
      (qspec_then `[]` mp_tac) >>
     simp_tac (srw_ss()) [Abbr `AS`, Abbr `MS`] >>
     disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     disch_then (qspec_then `t` mp_tac) >>
     simp[markerTheory.Abbrev_def, AC ADD_ASSOC ADD_COMM] >>
     disch_then irule >>
     Cases_on `dec_info_needs_offset h0` >> fs[mload_def] >> decide_tac) >>
  qpat_x_assum `Q cs' cs'' _ _ t` mp_tac >>
  qpat_assum `Abbrev (Q = _)`
    (fn th => rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> strip_tac
  >- suspend "child_success" >>
  disj2_tac >>
  fs[gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
Resume abi_decode_mem_members_anchored[child_success]:
  rename1 `R cs' cs'' (d+vo) h2 t v` >>
  `E cs'' v /\ s.vs_alloca_next <= v.vs_alloca_next` by
    (fs[Abbr `R`] >> decide_tac) >>
  `Q cs'' final (d+(h2+vo)) (MS elems) v` by
    (asm "ih" (qspecl_then [`h2+vo`,`ao+h1`,`final`,`cs''`,`v`,`K'`] mp_tac) >>
     simp_tac bool_ss [LET_THM] >>
     impl_tac
     >- suspend "tail_premises" >>
     simp[Abbr `Q`, Abbr `R`, Abbr `E`, Abbr `P`]) >>
  suspend "compose_endpoints"
QED
Resume abi_decode_mem_members_anchored[tail_premises]:
  `sb + (ao+h1) + AS elems <= H /\
   d + (h2+vo) + MS elems < dimword (:256) /\
   d + (h2+vo) + MS elems <= v.vs_alloca_next` by
    (fs[Abbr `AS`, Abbr `MS`] >> decide_tac) >>
  simp[Abbr `E`, Abbr `P`] >>
  conj_tac >- fs[] >>
  suspend "tail_children"
QED
Resume abi_decode_mem_members_anchored[tail_children]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!pre di a m post q r cs cd u off. _`
    (qspec_then `(h0,h1,h2)::pre` mp_tac) >>
  simp_tac (srw_ss()) [markerTheory.Abbrev_def, Abbr `AS`, Abbr `MS`,
    Abbr `Q`, Abbr `R`, AC ADD_ASSOC ADD_COMM] >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`a`,`m`,`post`,`u`] mp_tac) >>
  fs[AC ADD_ASSOC ADD_COMM] >>
  disch_then irule >> decide_tac
QED
Resume abi_decode_mem_members_anchored[compose_endpoints]:
  qpat_x_assum `Q cs'' final _ _ v` mp_tac >>
  simp[Abbr `Q`] >> strip_tac
  >- suspend "compose_success" >>
  disj2_tac >> fs[gas_marked_path_def] >>
  `gas_path_mem ctx func s 0 (OK v)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
Resume abi_decode_mem_members_anchored[compose_success]:
  rename1 `R cs'' final _ _ v z` >>
  `gas_path_mem ctx func s 0 (OK z)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  disj1_tac >> qexists_tac `z` >> simp[] >>
  qpat_x_assum `R cs' cs'' _ _ t v` mp_tac >>
  qpat_x_assum `R cs'' final _ _ v z` mp_tac >>
  simp[Abbr `R`] >> ntac 2 strip_tac >>
  suspend "compose_resources"
QED
Resume abi_decode_mem_members_anchored[compose_resources]:
  asm_x "ih" kall_tac >>
  qpat_x_assum `!pre di a m post q r cs cd u off. _` kall_tac >>
  conj_tac
  >- (rpt strip_tac >>
      `id < cs'.cs_next_id \/ cs''.cs_next_id <= id` by decide_tac >>
      `id < cs''.cs_next_id \/ final.cs_next_id <= id` by decide_tac >>
      metis_tac[]) >>
  `?owned. (!p n. MEM (p,n) owned <=>
      ?id. cs'.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP z.vs_allocas id = SOME (p,n)) /\
    abi_decode_footprint_frame ((d+vo,MS ((h0,h1,h2)::elems))::owned) t z` by
    (irule abi_decode_mem_owned_frames_compose >>
     goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
     goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
     qexists_tac `cs''.cs_next_id` >>
     simp[Abbr `MS`] >> rpt conj_tac >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  suspend "setup_frame"
QED
Resume abi_decode_mem_members_anchored[setup_frame]:
  qspecl_then [`st.cs_next_id`,`final.cs_next_id`,`z.vs_allocas`]
    strip_assume_tac abi_decode_mem_owned_footprint_exists >>
  qexists_tac `fp''` >> simp[] >>
  `abi_decode_footprint_frame ((d+vo,MS ((h0,h1,h2)::elems))::fp'') t z` by
    (irule abi_decode_mem_owned_frame_widen >>
     goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`final.cs_next_id`,`cs'.cs_next_id`] >> simp[] >>
     metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  fs[abi_decode_footprint_frame_def]
QED
Finalise abi_decode_mem_members_anchored


Theorem abi_decode_mem_members:
  !(K:num -> bool). let AS = (\xs. SUM (MAP (\(di,a,m). a) xs));
      MS = (\xs. SUM (MAP (\(di,a,m). m) xs));
      P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H s.vs_memory /\
                (!p. K p ==> mload p u = mload p s) /\
                u.vs_call_ctx = s.vs_call_ctx /\
                u.vs_data_section = s.vs_data_section);
      E = (\q u. P u /\ fresh_vars_wrt q u /\ alloca_inv u /\
                alloca_room ctx func u /\ alloca_history func u /\
                ~u.vs_halted /\ u.vs_current_bb = q.cs_current_bb /\
                u.vs_inst_idx = LENGTH q.cs_current_insts /\
                B + H <= u.vs_alloca_next /\
                eval_operand src u = SOME (n2w sb) /\
                eval_operand dst u = SOME (n2w d) /\
                eval_operand bop u = SOME (n2w B) /\
                eval_operand hi u = SOME (n2w H));
      R = (\q r out sz u v.
                E r v /\ u.vs_alloca_next <= v.vs_alloca_next /\
                (!op w. eval_operand op u = SOME w ==> eval_operand op v = SOME w) /\
                (!id. id < q.cs_next_id \/ r.cs_next_id <= id ==>
                   FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
                ?fp. (!p n. MEM (p,n) fp <=>
                        ?id. q.cs_next_id <= id /\ id < r.cs_next_id /\
                             FLOOKUP v.vs_allocas id = SOME (p,n)) /\
                     abi_decode_footprint_frame ((out,sz)::fp) u v);
      Q = (\q r out sz u.
                (?v. gas_path_mem ctx func u 0 (OK v) /\ R q r out sz u v) \/
                (?v. gas_marked_path T ctx func u 0 (Abort Revert_abort v)))
  in
    compile_abi_decode_complex_elems dst src MLOAD bop hi elems ao vo st = ((),final) /\
    hi <> Lit 0w /\ fn_has_code st final func /\ fn_inst_ids_distinct func /\
    E st s /\ sb < dimword (:256) /\ B + H < dimword (:256) /\
    sb + ao + AS elems <= H /\ d + vo + MS elems < dimword (:256) /\
    d + vo + MS elems <= s.vs_alloca_next /\
    EVERY (\(di,a,m). (dec_info_needs_offset di ==> 32 <= a) /\
                          (!c. di = DecPrimWord c ==> 32 <= a)) elems /\
    (!pre di a m post q r cs cd u.
        elems = pre ++ (di,a,m)::post /\
        st.cs_next_id <= q.cs_next_id /\ r.cs_next_id <= final.cs_next_id /\
        compile_abi_decode_to_buf cd cs MLOAD bop hi di q = ((),r) /\
        fn_has_code q r func /\ E q u /\
        abi_decoder_operand_live q.cs_next_var cs /\
        abi_decoder_operand_live q.cs_next_var cd /\
        eval_operand cd u = SOME (n2w (d + vo + MS pre)) /\
        (let off = if dec_info_needs_offset di
                   then w2n (mload (B + sb + ao + AS pre) u)
                   else ao + AS pre
         in sb + off < dimword (:256) /\
            eval_operand cs u = SOME (n2w (sb + off)))
        ==> Q q r (d + vo + MS pre) m u)
    ==> Q st final (d + vo) (MS elems) s
Proof
  irule abi_decode_mem_members_anchored
QED

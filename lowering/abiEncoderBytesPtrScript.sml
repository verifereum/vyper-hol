(* Pointer execution of the bytestring encoder phases. *)
Theory abiEncoderBytesPtr
Ancestors wordLoadStorePtr
  abiEncoderBytesCode abiEncoderRounding abiEncoderMemory typedCopyPtr decoderNavigationPtr
  bodyPtrDefs fragExecPtr ghostPcTransportPtr emitHelperProps exprLoweringProps ptrDiscipline venomState
  venomExecSemantics finite_map pred_set words arithmetic list rich_list venomInst codegenRel context emitHelper compileEnv

Theorem abi_encode_round_frag_ptr:
  !sa sb len out s cnt G tn cx ctx PG R.
    abi_encode_round len sa = (out,sb) /\
    eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
    cnt + 31 < dimword(:256) ==>
    ?H u t.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g = G /\ z = tn /\ v = s)
        (\g z v. g = H /\ z = u /\ v = t) R /\
      eval_operand out t = SOME (n2w (contractABI$ceil32 cnt)) /\
      op_taint u out = {} /\ op_prov H out = NONE /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\ t.vs_logs = s.vs_logs /\
      t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encode_round _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [Lit 31w;len] sa = (arg,sc)` >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op AND _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  gvs[] >>
  qabbrev_tac `v1 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `v2 = STRING #"%" (toString sc.cs_next_var)` >>
  qabbrev_tac `s1 = update_var v1 (31w + n2w cnt) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst sa.cs_next_id ADD [Lit 31w;len] [v1]) s1` >>
  qabbrev_tac `t1 = step_taint (mk_inst sa.cs_next_id ADD [Lit 31w;len] [v1]) s s1 tn` >>
  qabbrev_tac `s2 = update_var v2 (n2w (contractABI$ceil32 cnt)) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = step_prov PG g1 (mk_inst sc.cs_next_id AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;Var v1] [v2]) s2` >>
  qabbrev_tac `t2 = step_taint (mk_inst sc.cs_next_id AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;Var v1] [v2]) s1 s2 t1` >>
  `sc.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sc.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    (imp_res_tac emit_op_extends >> fs[cs_extends_def, same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `frag_exec_ptr cx ctx PG sa sc
    (\g z v. g=G /\ z=tn /\ v=s) (\g z v. g=g1 /\ z=t1 /\ v=s1) R` by
    (irule copy_len_binop_frag_ptr >> simp[] >>
     qexistsl_tac [`word_add`, `sa.cs_next_id`, `Lit 31w`, `ADD`, `len`, `v1`] >>
     simp[mk_inst_def, eval_operand_def, op_taint_def, Abbr `v1`,
       Abbr `g1`, Abbr `t1`, Abbr `s1`, step_prov_def, step_taint_def,
       update_var_def]) >>
  `op_taint t1 (Var v1) = {}` by
    simp[Abbr `t1`, Abbr `s1`, step_taint_def, mk_inst_def, out_taint_def,
      set_var_taint_def, op_taint_def, eval_operand_def, FLOOKUP_UPDATE] >>
  `frag_exec_ptr cx ctx PG sc sb
    (\g z v. g=g1 /\ z=t1 /\ v=s1) (\g z v. g=g2 /\ z=t2 /\ v=s2) R` by
    (irule copy_len_binop_frag_ptr >> simp[] >>
     qexistsl_tac [`word_and`, `sc.cs_next_id`,
       `Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w`,
       `AND`, `Var v1`, `v2`] >>
     simp[Abbr `v2`, mk_inst_def, eval_operand_def, op_taint_def,
       Abbr `g2`, Abbr `t2`, Abbr `s2`, Abbr `s1`,
       step_prov_def, step_taint_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, abi_encoder_round_ceil32]) >>
  qexistsl_tac [`g2`,`t2`,`s2`] >> conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sc _ _ _` (irule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> v1 /\ x <> v2` by
    (simp[not_fresh_at_def, Abbr `v1`, Abbr `v2`] >> rpt strip_tac >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_SUC_REFL]) >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `v2`, lookup_var_def, eval_operand_def,
    update_var_def, FLOOKUP_UPDATE] >>
  `!q w v k. update_var q w (v with vs_inst_idx := k) =
    (update_var q w v with vs_inst_idx := k)` by simp[update_var_def] >>
  simp[Abbr `t2`, Abbr `g2`, Abbr `t1`, Abbr `g1`,
    copy_len_binop_ghost_frame] >>
  conj_tac >-
    simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
      FLOOKUP_DRESTRICT] >>
  conj_tac >-
    simp[step_taint_def, imm_taint_def, mk_inst_def, update_var_def,
      step_writes_def] >>
  gen_tac >> strip_tac >>
  `x <> v1 /\ x <> STRING #"%" (toString (sa.cs_next_var+1))` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame]
QED

(* A zero store clears precisely its destination word, with no allocator or
   ambient-variable effects. *)
Theorem emit_zero_store_frag_ptr:
  !sa sb dst s d G tn cx ctx PG R.
    emit_void MSTORE [Var dst;Lit 0w] sa = ((),sb) /\
    lookup_var dst s = SOME (n2w d) /\ d < dimword(:256) /\
    ptr_covers G tn dst s 32 ==>
    ?u.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g=G /\ z=tn /\ v=s)
        (\g z v. g=G /\ z=u /\
          v=(mstore d 0w s with vs_inst_idx := SUC s.vs_inst_idx)) R /\
      u.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d+32} /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst;Lit 0w] []]` by
    gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  qabbrev_tac `u = step_taint
    (mk_inst sa.cs_next_id MSTORE [Var dst;Lit 0w] []) s (mstore d 0w s) tn` >>
  `step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;Lit 0w] [])
      (mstore d 0w s) = G /\ u.t_var = tn.t_var /\
    u.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d+32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans` by
    (mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`sa.cs_next_id`,`dst`,`Lit 0w`,
       `n2w d`,`0w`] mstore_ghost_frame) >>
     simp[eval_operand_def, op_taint_def, Abbr `u`, w2n_n2w, LESS_MOD]) >>
  qexists_tac `u` >> conj_tac >-
    (irule mstore_frag_ptr >> simp[] >>
     qexistsl_tac [`dst`,`sa.cs_next_id`,`Lit 0w`] >>
     simp[eval_operand_def, op_taint_def, w2n_n2w, LESS_MOD, Abbr `u`]) >>
  simp[op_taint_def] >>
  simp[Abbr `u`, step_taint_def, imm_taint_def, mk_inst_def,
    step_writes_def, mstore_def]
QED

Theorem abi_encode_bytes_suffix_frag_ptr:
  !sa sb len out s cnt G tn cx ctx PG R.
    abi_encode_bytes_suffix len sa = (out,sb) /\
    eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
    cnt+31 < dimword(:256) ==>
    ?H u t.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g=G /\ z=tn /\ v=s)
        (\g z v. g=H /\ z=u /\ v=t) R /\
      eval_operand out t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
      op_taint u out = {} /\ op_prov H out = NONE /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\ t.vs_logs = s.vs_logs /\
      t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encode_bytes_suffix _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_encode_bytes_suffix_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_encode_round len sa = (rounded,sc)` >>
  drule_all abi_encode_round_frag_ptr >>
  disch_then (qspecl_then [`G`,`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac)))) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  gvs[] >>
  qabbrev_tac `q = STRING #"%" (toString sc.cs_next_var)` >>
  qabbrev_tac `s2 = update_var q (n2w (32+contractABI$ceil32 cnt)) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = step_prov PG g1 (mk_inst sc.cs_next_id ADD [Lit 32w;rounded] [q]) s2` >>
  qabbrev_tac `t2 = step_taint (mk_inst sc.cs_next_id ADD [Lit 32w;rounded] [q]) s1 s2 t1` >>
  `cs_extends sa sc` by
    (drule abi_encode_round_shape >> simp[inst_extends_def, cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[]) >>
  `cs_extends sc sb /\ sb.cs_current_bb = sc.cs_current_bb` by
    (drule emit_op_extends >> drule emit_op_same_blocks >>
     simp[cs_extends_def, same_blocks_def] >> rpt strip_tac >> qexists_tac `[]` >> simp[]) >>
  `frag_exec_ptr cx ctx PG sc sb
    (\g z v. g=g1 /\ z=t1 /\ v=s1) (\g z v. g=g2 /\ z=t2 /\ v=s2) R` by
    (irule copy_len_binop_frag_ptr >> simp[] >>
     qexistsl_tac [`word_add`,`sc.cs_next_id`,`Lit 32w`,`ADD`,`rounded`,`q`] >>
     simp[mk_inst_def, op_taint_def, eval_operand_def, Abbr `q`,
       Abbr `g2`, Abbr `t2`, Abbr `s2`, word_add_n2w,
       step_prov_def, step_taint_def, update_var_def]) >>
  qexistsl_tac [`g2`,`t2`,`s2`] >> conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sc _ _ _` (irule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ x <> q` by
    (drule abi_encode_round_shape >> strip_tac >>
     simp[not_fresh_at_def, Abbr `q`] >> rpt strip_tac >>
     simp[not_fresh_at_def, Abbr `q`] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `s2`, Abbr `q`, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `t2`, Abbr `g2`, copy_len_binop_ghost_frame] >>
  conj_tac >-
    (Cases_on `rounded` >> gvs[op_prov_def] >>
     simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  conj_tac >-
    simp[step_taint_def, imm_taint_def, mk_inst_def, update_var_def, step_writes_def] >>
  metis_tac[lookup_var_def]
QED

Theorem abi_encode_bytes_prefix_frag_ptr:
  !sa sb src dst len last s p d cnt G tn cx ctx PG R.
    abi_encode_bytes_prefix (Var dst) (Var src) sa = ((len,last),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME (n2w p) /\ lookup_var dst s = SOME (n2w d) /\
    mload p s = n2w cnt /\ ptr_covers G tn src s 32 /\
    ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
    cnt+31 < dimword(:256) /\ p < dimword(:256) /\
    d+32+contractABI$ceil32 cnt < dimword(:256) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) ==>
    ?H u t q.
      last = Var q /\
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g=G /\ z=tn /\ v=s)
        (\g z v. g=H /\ z=u /\ v=t) R /\
      eval_operand len t = SOME (n2w cnt) /\ op_taint u len = {} /\
      lookup_var q t = SOME (n2w (d+contractABI$ceil32 cnt)) /\
      ptr_covers H u q t 32 /\
      u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\ t.vs_logs = s.vs_logs /\
      t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encode_bytes_prefix _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_encode_bytes_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> ntac 2 (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [Var src] sa = (len,sc)` >>
  rename1 `abi_encode_round len sc = (rounded,sd)` >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  gvs[] >>
  qabbrev_tac `lv = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `loaded = update_var lv (n2w cnt) s` >>
  `run_inst_seq (emitted_insts sa sc) s = OK loaded` by
    simp[Abbr `loaded`, run_inst_seq_def, step_inst_base_def, mk_inst_def,
      exec_read1_def, eval_operand_def, w2n_n2w, LESS_MOD] >>
  `!i. w2n (n2w p : 256 word) <= i /\
    i < w2n (n2w p : 256 word)+32 ==> i NOTIN tn.t_mem` by
    simp[w2n_n2w, LESS_MOD] >>
  drule_all emit_mload_clean_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `g1` (qx_choose_then `t1` strip_assume_tac))) >>
  qabbrev_tac `s1 = loaded with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand (Var lv) s1 = SOME (n2w cnt)` by
    simp[Abbr `s1`, Abbr `loaded`, eval_operand_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE] >>
  drule_all abi_encode_round_frag_ptr >>
  disch_then (qspecl_then [`g1`,`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `g2` (qx_choose_then `t2` (qx_choose_then `s2` strip_assume_tac)))) >>
  rename1 `emit_op ADD [Var dst;rounded] sd = (last,sb)` >>
  `sc.cs_next_var <= sd.cs_next_var` by
    (drule abi_encode_round_shape >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x /\ not_fresh_at sd x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `not_fresh_at sc lv` by
    simp[not_fresh_at_def, Abbr `lv`] >>
  `lookup_var dst s2 = SOME (n2w d) /\
   ptr_covers g2 t2 dst s2 (32+contractABI$ceil32 cnt)` by
    (fs[ptr_covers_def] >>
     `lookup_var dst s1 = lookup_var dst s` by
       (simp[Abbr `s1`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
     metis_tac[]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  gvs[] >>
  qabbrev_tac `q = STRING #"%" (toString sd.cs_next_var)` >>
  qabbrev_tac `actual = update_var q (n2w (d+contractABI$ceil32 cnt)) s2` >>
  `run_inst_seq (emitted_insts sd sb) s2 = OK actual` by
    simp[Abbr `actual`, run_inst_seq_def, step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def, word_add_n2w] >>
  `contractABI$ceil32 cnt + 32 <= 32+contractABI$ceil32 cnt /\
   w2n (n2w d : 256 word) + contractABI$ceil32 cnt < dimword(:256)` by
    (`d < dimword(:256)` by decide_tac >> simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  `lookup_var dst s2 = SOME (n2w d)` by metis_tac[] >>
  `contractABI$ceil32 cnt + 32 <= contractABI$ceil32 cnt+32` by simp[] >>
  drule_all emit_ptr_offset_endpoint_ptr_core >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  gvs[] >>
  `cs_extends sa sc /\ cs_extends sd sb /\ cs_extends sc sd` by
    (imp_res_tac emit_op_extends >> imp_res_tac emit_op_same_blocks >>
     fs[same_blocks_def] >> drule abi_encode_round_shape >>
     simp[inst_extends_def, cs_extends_def, same_blocks_def] >>
     rpt strip_tac >> qexists_tac `[]` >> simp[]) >>
  qexistsl_tac [`H`,`u`,`actual with vs_inst_idx := SUC s2.vs_inst_idx`] >>
  conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sc _ _ _` (irule_at Any) >> simp[] >>
     conj_tac >- metis_tac[cs_extends_trans] >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sc sd _ _ _` (irule_at Any) >> simp[]) >>
  `not_fresh_at sd lv` by
    (simp[not_fresh_at_def, Abbr `lv`] >> decide_tac) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x s2 = lookup_var x s /\ FLOOKUP g2 x = FLOOKUP G x /\
    op_taint t2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sc x` by metis_tac[] >>
     qpat_x_assum `!x. not_fresh_at sc x ==> _` (qspec_then `x` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ FLOOKUP g1 x = _ /\ _` (qspec_then `x` mp_tac) >>
     simp[Abbr `s1`, lookup_var_def]) >>
  `lookup_var lv s2 = SOME (n2w cnt) /\ op_taint t2 (Var lv) = {}` by
    (qpat_x_assum `!x. not_fresh_at sc x ==> _` (qspec_then `lv` mp_tac) >>
     simp[Abbr `s1`, Abbr `loaded`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lv <> q /\ (!x. not_fresh_at sa x ==> x <> q)` by
    (fs[not_fresh_at_def, Abbr `q`] >> metis_tac[LESS_EQ_REFL]) >>
  simp[eval_operand_def, lookup_var_def, Abbr `actual`, Abbr `s1`,
    Abbr `loaded`, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[lookup_var_def]

QED

Theorem abi_encode_bytes_copy_frag_ptr:
  !sa sb src dst len last s p d cnt G tn cx ctx PG R.
    abi_encode_bytes_copy (Var dst) (Var src) len (Var last) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME (n2w p) /\ lookup_var dst s = SOME (n2w d) /\
    lookup_var last s = SOME (n2w (d+contractABI$ceil32 cnt)) /\
    eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
    ptr_covers G tn src s (32+cnt) /\ ptr_covers G tn dst s (32+cnt) /\
    ptr_covers G tn last s 32 /\
    32+cnt < dimword(:256) /\ p < dimword(:256) /\
    d+32+contractABI$ceil32 cnt < dimword(:256) /\
    (!i. p <= i /\ i < p+32+cnt ==> i NOTIN tn.t_mem) ==>
    ?H u t.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g=G /\ z=tn /\ v=s)
        (\g z v. g=H /\ z=u /\ v=t) R /\
      u.t_mem = tn.t_mem DIFF
        ({i | d+contractABI$ceil32 cnt <= i /\ i < d+contractABI$ceil32 cnt+32} UNION
         {i | d <= i /\ i < d+32+cnt}) /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      t.vs_memory = (mcopy d p (32+cnt) (mstore (d+contractABI$ceil32 cnt) 0w s)).vs_memory /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
      t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_encode_bytes_copy _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_void MSTORE _ sa = ((),sc)` >>
  rename1 `emit_op ADD _ sc = (copylen,sd)` >>
  `d+contractABI$ceil32 cnt < dimword(:256)` by decide_tac >>
  drule_all emit_zero_store_frag_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`] (qx_choose_then `t1` strip_assume_tac)) >>
  qabbrev_tac `s1 = mstore (d+contractABI$ceil32 cnt) 0w s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  gvs[] >>
  qabbrev_tac `q = STRING #"%" (toString sc.cs_next_var)` >>
  qabbrev_tac `s2 = update_var q (n2w (32+cnt)) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `g2 = step_prov PG G (mk_inst sc.cs_next_id ADD [Lit 32w;len] [q]) s2` >>
  qabbrev_tac `t2 = step_taint (mk_inst sc.cs_next_id ADD [Lit 32w;len] [q]) s1 s2 t1` >>
  `eval_operand len s1 = SOME (n2w cnt) /\ op_taint t1 len = {}` by
    (Cases_on `len` >> gvs[eval_operand_def, op_taint_def, Abbr `s1`, mstore_def, lookup_var_def]) >>
  `sd.cs_current_bb = sc.cs_current_bb` by metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `frag_exec_ptr cx ctx PG sc sd
    (\g z v. g=G /\ z=t1 /\ v=s1) (\g z v. g=g2 /\ z=t2 /\ v=s2) R` by
    (irule copy_len_binop_frag_ptr >> simp[] >>
     qexistsl_tac [`word_add`,`sc.cs_next_id`,`Lit 32w`,`ADD`,`len`,`q`] >>
     simp[mk_inst_def, op_taint_def, eval_operand_def, Abbr `q`,
       Abbr `g2`, Abbr `t2`, Abbr `s2`, word_add_n2w,
       step_prov_def, step_taint_def, update_var_def]) >>
  `sc.cs_next_var = sa.cs_next_var` by
    gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  `!x. not_fresh_at sa x ==> x <> q` by
    (simp[not_fresh_at_def, Abbr `q`] >> metis_tac[LESS_EQ_REFL]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x s2 = lookup_var x s /\ FLOOKUP g2 x = FLOOKUP G x /\
    op_taint t2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> q` by metis_tac[] >>
     `!a w v k. update_var a w (v with vs_inst_idx := k) =
       (update_var a w v with vs_inst_idx := k)` by simp[update_var_def] >>
     simp[Abbr `g2`, Abbr `t2`, Abbr `s2`, copy_len_binop_ghost_frame] >>
     simp[Abbr `s1`, lookup_var_def, update_var_def, mstore_def, FLOOKUP_UPDATE]) >>
  `lookup_var src s2 = SOME (n2w p) /\ lookup_var dst s2 = SOME (n2w d) /\
   eval_operand (Var q) s2 = SOME (n2w (32+cnt)) /\ op_taint t2 (Var q) = {} /\
   ptr_covers g2 t2 src s2 (32+cnt) /\ ptr_covers g2 t2 dst s2 (32+cnt)` by
    (conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     conj_tac >- simp[eval_operand_def, Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- simp[Abbr `t2`, Abbr `s2`, copy_len_binop_ghost_frame] >>
     fs[ptr_covers_def] >> metis_tac[]) >>
  qabbrev_tac `s3 = mcopy d p (32+cnt) s2 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `g3 = step_prov PG g2 (mk_inst sd.cs_next_id MCOPY [Var dst;Var src;Var q] []) s3` >>
  qabbrev_tac `t3 = step_taint (mk_inst sd.cs_next_id MCOPY [Var dst;Var src;Var q] []) s2 s3 t2` >>
  `d < dimword(:256)` by decide_tac >>
  `lookup_var q s2 = SOME (n2w (32+cnt))` by fs[eval_operand_def] >>
  `frag_exec_ptr cx ctx PG sd sb
    (\g z v. g=g2 /\ z=t2 /\ v=s2) (\g z v. g=g3 /\ z=t3 /\ v=s3) R` by
    (irule mcopy_operand_frag_ptr >>
     conj_tac >- metis_tac[emit_void_same_blocks, same_blocks_def] >>
     qexistsl_tac [`Var q`,`dst`,`sd.cs_next_id`,`src`] >>
     simp[Abbr `g3`, Abbr `t3`, Abbr `s3`, eval_operand_def,
       w2n_n2w, LESS_MOD] >>
     gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]) >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    (imp_res_tac emit_void_extends >> imp_res_tac emit_op_extends >>
     imp_res_tac emit_void_same_blocks >> imp_res_tac emit_op_same_blocks >>
     fs[cs_extends_def, same_blocks_def] >> rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  qexistsl_tac [`g3`,`t3`,`s3`] >> conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sc _ _ _` (irule_at Any) >> simp[] >>
     conj_tac >- metis_tac[cs_extends_trans] >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sc sd _ _ _` (irule_at Any) >> simp[]) >>
  `eval_operand (Var dst) s2 = SOME (n2w d) /\
   eval_operand (Var src) s2 = SOME (n2w p)` by simp[eval_operand_def] >>
  qpat_assum `eval_operand (Var dst) s2 = _`
    (mp_then Any mp_tac mcopy_operand_ghost_frame) >>
  disch_then (qspecl_then [`PG`,`g2`,`t2`,`sd.cs_next_id`] mp_tac) >>
  disch_then (qspecl_then [`Var src`,`Var q`,`n2w p`,`n2w (32+cnt)`] mp_tac) >>
  simp[w2n_n2w, LESS_MOD] >>
  strip_tac >>
  `g3 = g2 /\ t3.t_stor = t2.t_stor /\ t3.t_trans = t2.t_trans /\
   t3.t_var = t2.t_var /\
   t3.t_mem = (t2.t_mem DIFF {i | d <= i /\ i < d+(32+cnt)}) UNION
     {d+i | i < 32+cnt /\ p+i IN t2.t_mem}` by
    simp[Abbr `g3`, Abbr `t3`, Abbr `s3`] >>
  `t2.t_mem = t1.t_mem /\ t2.t_stor = t1.t_stor /\ t2.t_trans = t1.t_trans` by
    simp[Abbr `t2`, Abbr `s2`, copy_len_binop_ghost_frame] >>
  conj_tac >-
    (`{d+i | i < 32+cnt /\ p+i IN t2.t_mem} = {}` by
       (simp[EXTENSION] >> rpt gen_tac >> CCONTR_TAC >> gvs[] >>
        qpat_x_assum `!i. p <= i /\ _ ==> _` (qspec_then `p+i` mp_tac) >>
        simp[] >> decide_tac) >>
     qpat_x_assum `t3.t_mem = _` (fn th => pure_rewrite_tac [th]) >>
     simp[] >> SET_TAC[]) >>
  simp[] >>
  conj_tac >-
    simp_tac (srw_ss()) [Abbr `s3`, Abbr `s2`, Abbr `s1`, mcopy_def,
      write_memory_with_expansion_def, update_var_def, LET_THM, ADD_COMM] >>
  simp_tac (srw_ss()) [Abbr `s3`, Abbr `s2`, Abbr `s1`, mcopy_def,
    write_memory_with_expansion_def, update_var_def, mstore_def, LET_THM] >>
  gen_tac >> strip_tac >>
  `x <> q` by metis_tac[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ FLOOKUP g2 x = _ /\ _`
    (qspec_then `x` mp_tac) >>
  simp[lookup_var_def, update_var_def, mstore_def, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem abi_encode_bytes_prefix_shape:
  abi_encode_bytes_prefix dst src sa = ((len,last),sb) ==>
  sb.cs_next_var = sa.cs_next_var + 4 /\
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  len = Var (STRING #"%" (toString sa.cs_next_var)) /\ inst_extends sa sb
Proof
  simp[abi_encode_bytes_prefix_def, abi_encode_round_def, comp_bind_def,
    comp_return_def, comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem compile_abi_encode_bytestring_exact_frag_ptr:
  !sa sb src dst maxlen out s p d cnt G tn cx ctx PG R.
    compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME (n2w p) /\ lookup_var dst s = SOME (n2w d) /\
    mload p s = n2w cnt /\ ptr_covers G tn src s (32+cnt) /\
    ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
    cnt+31 < dimword(:256) /\ 32+contractABI$ceil32 cnt < dimword(:256) /\
    p+32+cnt < dimword(:256) /\ d+32+contractABI$ceil32 cnt < dimword(:256) /\
    (p+32+cnt <= d \/ d+32+contractABI$ceil32 cnt <= p) /\
    (!i. p <= i /\ i < p+32+cnt ==> i NOTIN tn.t_mem) ==>
    ?H u t.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g=G /\ z=tn /\ v=s)
        (\g z v. g=H /\ z=u /\ v=t) R /\
      eval_operand out t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
      op_taint u out = {} /\
      (!i. d <= i /\ i < d+32+contractABI$ceil32 cnt ==> i NOTIN u.t_mem) /\
      t.vs_memory = (mcopy d p (32+cnt) (mstore (d+contractABI$ceil32 cnt) 0w s)).vs_memory /\
      u.t_mem = tn.t_mem DIFF
        ({i | d+contractABI$ceil32 cnt <= i /\ i < d+contractABI$ceil32 cnt+32} UNION
         {i | d <= i /\ i < d+32+cnt}) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
      t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  drule abi_encode_bytes_trace >> strip_tac >> PairCases_on `ops` >> gvs[] >>
  rename1 `abi_encode_bytes_prefix _ _ sa = ((len,last),ready)` >>
  `p < dimword(:256)` by decide_tac >>
  `ptr_covers G tn src s 32` by (fs[ptr_covers_def] >> metis_tac[DECIDE ``32 <= 32+cnt``]) >>
  `!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> qpat_x_assum `!i. p <= i /\ _ ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `cnt+31 < dimword(:256) /\
   ptr_covers G tn dst s (32+contractABI$ceil32 cnt)` by
    (mp_tac abi_encoder_ceil32_bounds >> simp[] >> decide_tac) >>
  `d+32+contractABI$ceil32 cnt < dimword(:256)` by decide_tac >>
  drule_all abi_encode_bytes_prefix_frag_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` (qx_choose_then `q` strip_assume_tac))))) >>
  gvs[] >>
  drule abi_encode_bytes_prefix_shape >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at ready x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var src s1 = SOME (n2w p) /\ lookup_var dst s1 = SOME (n2w d) /\
   ptr_covers g1 t1 src s1 (32+cnt) /\ ptr_covers g1 t1 dst s1 (32+cnt)` by
    (conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     `lookup_var src s1 = lookup_var src s /\ FLOOKUP g1 src = FLOOKUP G src /\
      op_taint t1 (Var src) = op_taint tn (Var src) /\
      lookup_var dst s1 = lookup_var dst s /\ FLOOKUP g1 dst = FLOOKUP G dst /\
      op_taint t1 (Var dst) = op_taint tn (Var dst)` by metis_tac[] >>
     gvs[ptr_covers_def] >> mp_tac abi_encoder_ceil32_bounds >> decide_tac) >>
  `32+cnt < dimword(:256) /\ p < dimword(:256) /\
   d+32+contractABI$ceil32 cnt < dimword(:256)` by
    (mp_tac abi_encoder_ceil32_bounds >> decide_tac) >>
  `!i. p <= i /\ i < p+32+cnt ==> i NOTIN t1.t_mem` by simp[] >>
  `not_fresh_at ready src /\ not_fresh_at ready dst` by metis_tac[] >>
  drule_all abi_encode_bytes_copy_frag_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `g2` (qx_choose_then `t2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `not_fresh_at ready (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `eval_operand len s2 = SOME (n2w cnt) /\ op_taint t2 len = {}` by
    (qpat_x_assum `!x. not_fresh_at ready x ==> _`
       (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
     gvs[eval_operand_def]) >>
  `cnt+31 < dimword(:256)` by decide_tac >>
  drule_all abi_encode_bytes_suffix_frag_ptr >>
  disch_then (qspecl_then [`g2`,`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `g3` (qx_choose_then `t3` (qx_choose_then `s3` strip_assume_tac)))) >>
  `cs_extends sa ready /\ cs_extends ready copied /\ cs_extends copied sb` by
    (drule abi_encode_bytes_copy_shape >> drule abi_encode_bytes_suffix_shape >>
     rpt strip_tac >> fs[inst_extends_def, cs_extends_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  qexistsl_tac [`g3`,`t3`,`s3`] >> conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa ready _ _ _` (irule_at Any) >> simp[] >>
     conj_tac >- metis_tac[cs_extends_trans] >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ ready copied _ _ _` (irule_at Any) >> simp[]) >>
  simp[] >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >>
     mp_tac abi_encoder_ceil32_bounds >>
     simp[] >> decide_tac) >>
  conj_tac >-
    (irule (SIMP_RULE arith_ss [] abi_encoder_bytes_write_memory_cong) >> simp[]) >>
  drule abi_encode_bytes_copy_shape >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at copied x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gen_tac >> strip_tac >> metis_tac[]
QED

(* Preserve the established interface as a projection of the shared execution. *)
Theorem compile_abi_encode_bytestring_frag_ptr:
  !sa sb src dst maxlen out s p d cnt G tn cx ctx PG R.
    compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME (n2w p) /\ lookup_var dst s = SOME (n2w d) /\
    mload p s = n2w cnt /\ ptr_covers G tn src s (32+cnt) /\
    ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
    cnt+31 < dimword(:256) /\ 32+contractABI$ceil32 cnt < dimword(:256) /\
    p+32+cnt < dimword(:256) /\ d+32+contractABI$ceil32 cnt < dimword(:256) /\
    (p+32+cnt <= d \/ d+32+contractABI$ceil32 cnt <= p) /\
    (!i. p <= i /\ i < p+32+cnt ==> i NOTIN tn.t_mem) ==>
    ?H u t.
      frag_exec_ptr cx ctx PG sa sb
        (\g z v. g=G /\ z=tn /\ v=s)
        (\g z v. g=H /\ z=u /\ v=t) R /\
      eval_operand out t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
      op_taint u out = {} /\
      (!i. d <= i /\ i < d+32+contractABI$ceil32 cnt ==> i NOTIN u.t_mem) /\
      t.vs_memory = (mcopy d p (32+cnt) (mstore (d+contractABI$ceil32 cnt) 0w s)).vs_memory /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
      t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
      t.vs_pending_deletions = s.vs_pending_deletions /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_abi_encode_bytestring_exact_frag_ptr >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`R`]
    (qx_choose_then `H` (qx_choose_then `u` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`H`,`u`,`t`] >> asm_rewrite_tac[]
QED

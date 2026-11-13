(* One robust bytestring field, not recursive normalization. *)
Theory assignBasePtrBytesField
Ancestors assignBasePtrFieldOffsets assignBasePtrBytesPost exprSimBufferStore stmtFragPtr
  exprLoweringProps context compileEnv fragExec fragGasPathPtr
  typedMemoryCopy venomState words finite_map list rich_list
  bodyPtrDefs ptrDiscipline venomExecSemantics

Theorem assign_base_store_bytestring_extends[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> drule buffer_store_bytestring_shape >> strip_tac >> simp[] >>
  irule cs_extends_same_block >> simp[same_blocks_def, IS_PREFIX_APPEND] >>
  metis_tac[same_blocks_def]
QED

Theorem assign_base_bytestring_field_robust_counted:
  !dst src doff soff sa dop sm sop sc sb fn s d a dtot stot n len
    G tn D ctx PG tv v.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sc) /\
    compile_store_bytestring sop dop sc = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtot /\ ptr_covers G tn src s stot /\
    doff < dtot /\ doff+n <= dtot /\ soff < stot /\ soff+n <= stot /\
    w2n d+doff < dimword (:256) /\ w2n a+soff < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ n = 32 + 32 * word_size len /\
    n < dimword (:256) /\ mload (w2n a+soff) s = n2w len /\
    (!i. w2n a+soff <= i /\ i < w2n a+soff+32 ==> i NOTIN tn.t_mem) /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a+soff) m) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      typed_copy_state_frame sa (w2n d+doff) n s u /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d+doff) m) /\
      (!i. i < n ==>
           (w2n d+doff+i IN tf.t_mem <=> w2n a+soff+i IN tn.t_mem)) /\
      (!i. i < w2n d+doff \/ w2n d+doff+n <= i ==>
           (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!i. i < w2n d+doff \/ w2n d+doff+n <= i ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var` by
    metis_tac[assign_base_offset_extends] >>
  `cs_extends sc sb /\ sc.cs_next_var <= sb.cs_next_var` by
    metis_tac[assign_base_store_bytestring_extends] >>
  `cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
   cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS] >> simp[] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all assign_base_field_offsets_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gp tp (OK q)` >>
  rename1 `dop = Var dp` >> rename1 `sop = Var sp` >>
  suspend "copy"
QED

Resume assign_base_bytestring_field_robust_counted[copy]:
  `q.vs_memory = s.vs_memory` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `mload (w2n a+soff) q = mload (w2n a+soff) s` by
    (simp[NoAsms, mload_def] >> simp[]) >>
  `ptr_covers Gp tp sp q 32` by
    (fs[ptr_covers_def] >> decide_tac) >>
  `compile_store_bytestring (Var sp) (Var dp) sc = ((),sb)` by metis_tac[] >>
  `mload (w2n (n2w (w2n a+soff) : bytes32)) q = n2w len /\
   (!i. w2n (n2w (w2n a+soff) : bytes32) <= i /\
        i < w2n (n2w (w2n a+soff) : bytes32)+32 ==> i NOTIN tp.t_mem) /\
   (!m. mem_agree_outside tp.t_mem q.vs_memory m ==>
     val_in_memory tv v (w2n (n2w (w2n a+soff) : bytes32)) m)` by
    (gs[] >> metis_tac[]) >>
  `ptr_covers Gp tp sp q (32 + 32 * word_size len) /\
   ptr_covers Gp tp dp q (32 + 32 * word_size len)` by metis_tac[] >>
  `32 + 32 * word_size len < dimword (:256) /\
   val_footprint tv v <= 32 + 32 * word_size len` by metis_tac[] >>
  drule_all assign_base_store_bytestring_robust_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gp tp q 0 Gf tf (OK u)` >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> suspend "post"
QED

Resume assign_base_bytestring_field_robust_counted[post]:
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  gs[] >> conj_tac >- suspend "frame" >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume assign_base_bytestring_field_robust_counted[frame]:
  irule typed_copy_state_frame_trans >> qexists_tac `q` >>
  reverse conj_tac
  >- (qpat_x_assum `typed_copy_state_frame sc _ _ q u` mp_tac >>
      simp[typed_copy_state_frame_def] >>
      metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[typed_copy_state_frame_def] >>
  qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = _` mp_tac >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Finalise assign_base_bytestring_field_robust_counted

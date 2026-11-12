Theory extRetNormalizeAmbientPtr
Ancestors
  extRetNormalizeWordPtr extRetScalarCopyCountedPtr typedCopyPtr fragGasSeqPtr
  fragExec fragExecPtr bodyPtrDefs fragGasPathPtr venomExecSemantics venomInstProofs
  venomInst venomState ptrSafeRun ptrDiscipline finite_map compileEnv emitHelper
  arithmetic wordLoadStorePtr representationCleanPtr robustCopyTransportPtr
  valueEncoding valueEncodingProofs valueEncodingProps list venomMemProofs valueEncodingDefs

(* A concrete execution boundary: unlike the old scalar endpoint, this
   retains the immutable taint and the whole ambient runtime record. *)
Theorem compile_store_word_ambient_counted_ptr:
  is_word_type ty /\
  compile_store_memory_typed ce (Var dst) ty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
      sf.vs_memory s.vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
       vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
       vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all compile_store_word_code >> strip_tac >>
  `tmp <> dst` by metis_tac[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst; Var tmp] []]` by simp[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by simp[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `s1 = update_var tmp (mload (w2n a) s) s` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) s1` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var src] [tmp]) s s1 tn` >>
  qabbrev_tac `v1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers G1 tn1 dst s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `s1`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  `lookup_var dst v1 = SOME b /\
   eval_operand (Var tmp) v1 = SOME (mload (w2n a) s)` by
    (simp[Abbr `v1`, Abbr `s1`, update_var_def, lookup_var_def,
          eval_operand_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n b) (mload (w2n a) s) v1` >>
  qabbrev_tac `G2 = step_prov PG G1
    (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) s2` >>
  qabbrev_tac `tn2 = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
    v1 s2 tn1` >>
  qexistsl_tac [`G2`, `tn2`, `s2 with vs_inst_idx := SUC v1.vs_inst_idx`] >>
  conj_tac
  >- (`get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp])` by
        (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
      `get_instruction bb v1.vs_inst_idx =
        SOME (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])` by
        (qpat_x_assum `!i. _` (qspec_then `1` mp_tac) >> simp[Abbr `v1`, ADD1]) >>
      `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK s1` by
        (pure_once_rewrite_tac[step_inst_base_def] >>
         simp[mk_inst_def, exec_read1_def, eval_operand_def, Abbr `s1`]) >>
      `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) v1 = OK s2` by
        (pure_once_rewrite_tac[step_inst_base_def] >>
         simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `s2`]) >>
      irule (gas_path_ptr_step |> Q.INST
        [`i` |-> `mk_inst id MLOAD [Var src] [tmp]`, `n` |-> `0`] |>
        SRULE [mk_inst_def]) >>
      simp[is_terminator_def] >> qexistsl_tac [`id`, `src`, `tmp`, `s1`] >>
      simp[GSYM mk_inst_def] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
      `s1 with vs_inst_idx := SUC (LENGTH sa.cs_current_insts) = v1` by
        simp[Abbr `v1`] >> asm_rewrite_tac[] >>
      irule (gas_path_ptr_step |> Q.INST
        [`i` |-> `mk_inst j MSTORE [Var dst; Var tmp] []`, `n` |-> `0`] |>
        SRULE [mk_inst_def, is_terminator_def]) >>
      `~v1.vs_halted /\ v1.vs_current_bb = sa.cs_current_bb` by
        simp[Abbr `v1`, Abbr `s1`, update_var_def] >>
      simp[] >> qexistsl_tac [`dst`, `id+1`, `tmp`, `s2`] >>
      simp[GSYM mk_inst_def] >> conj_tac
      >- (irule ptr_inst_ok_mstore >> simp[] >>
          qpat_x_assum `s1 with vs_inst_idx := _ = v1` kall_tac >>
          qpat_x_assum `ptr_covers G1 tn1 dst s1 32` mp_tac >>
          fs[Abbr `v1`, ptr_covers_def, lookup_var_def]) >>
      simp[Abbr `G2`, Abbr `tn2`] >>
      irule (cj 1 gas_path_ptr_rules) >>
      simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def]) >>
  `s2.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory` by
    simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
  conj_tac >- simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
  conj_tac >- simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
  conj_tac >- simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
  simp[mstore_memory_frame, Abbr `tn2`, Abbr `s2`, mstore_ghost_frame] >>
  conj_tac
  >- simp[Abbr `tn1`, step_taint_def, mk_inst_def, imm_taint_def, adopt_reset_def] >>
  conj_tac
  >- simp[Abbr `v1`, Abbr `s1`, mstore_def, update_var_def,
          venom_state_component_equality] >>
  rpt strip_tac >> `tmp <> p` by metis_tac[] >>
  simp[Abbr `G2`, Abbr `G1`, Abbr `tn1`, Abbr `v1`, Abbr `s1`,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
       lookup_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED


(* The extra BytesV case is necessary for the AddressT/fixed-bytes word
   dispatch. Its representation type is explicit: dynamic bytes are not words. *)
Theorem normalize_word_ambient_counted_ptr:
  is_word_type ty /\
  compile_store_memory_typed ce (Var dst) ty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
   (?x. v = FlagV x) \/ (?x. v = DecimalV x) \/
   (?bs. v = BytesV bs /\
     (tv = BaseTV AddressT \/ ?k. tv = BaseTV (BytesT (Fixed k))))) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
      sf.vs_memory s.vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
       vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
       vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    (!ft fv p. val_wf ft fv /\
      (!i. p <= i /\ i < p + val_footprint ft fv ==>
        ~(w2n b <= i /\ i < w2n b + 32)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_val_in_memory_prim_clean, robust_val_in_memory_bytes_clean] >>
  drule_all compile_store_word_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at (w2n b) 32 m = mem_bytes_at (w2n b) 32 sf.vs_memory` by
        (irule LIST_EQ >> simp[] >> rpt strip_tac >>
         rename1 `j < 32` >>
         `w2n b + j NOTIN tnf.t_mem` by simp[] >>
         `mem_bytes_at (w2n b+j) 1 sf.vs_memory = mem_bytes_at (w2n b+j) 1 m` by
           (fs[mem_agree_outside_def] >> metis_tac[]) >>
         qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
         simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
      `val_in_memory tv v (w2n a) s.vs_memory` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      `mem_word_at (w2n b) m = mem_word_at (w2n b) sf.vs_memory` by
        asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
      `mem_word_at (w2n b) m = mload (w2n a) s` by
        metis_tac[mstore_mem_word_at_same] >>
      gvs[val_in_memory_def, mem_word_at_eq_mload]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b + 32}`] >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

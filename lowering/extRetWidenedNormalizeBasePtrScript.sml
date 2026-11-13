Theory extRetWidenedNormalizeBasePtr
Ancestors
  extRetNormalizeBytesChildPtr bodyPtrIfExpStoreContract
  assignTuplePtrLoadStep assignTuplePtrStoreWord stmtSimDeclStore
  typedCopyPtr typedCopyAgreement wordLoadStorePtr fragGasSeqPtr fragGasPathPtr
  ghostPcTransportPtr fragExec fragExecPtr bodyPtrDefs compileEnv context emitHelper emitHelperProps
  venomExecSemantics venomInstProofs venomInst venomState venomMemProofs
  ptrDiscipline ptrCoverage robustCopyTransportPtr valueEncoding
  valueEncodingProofs valueEncodingProps exprSimProps finite_map
  list rich_list arithmetic pred_set

(* The common child endpoint permits control-flow changes, but no change to
   allocations, storage, transient storage, immutables, or other ambient
   machine fields.  Exterior resources are quantified, not enumerated. *)
Definition widened_normalize_outcome_def:
  widened_normalize_outcome D ctx fn PG sa sb dtv v b G tn s <=>
    (?a t. gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (Abort a t)) \/
    (?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_size dtv) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
        vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!ft fv p. val_wf ft fv /\
        (!i. p <= i /\ i < p + val_footprint ft fv ==>
          ~(w2n b <= i /\ i < w2n b + type_memory_size dtv)) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv p m))
End

Theorem widened_normalize_base_counted_ptr:
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n a) m) /\
  ptr_covers G tn src s
    (if is_word_type dty then 32 else val_store_size stv v) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  w2n a + val_footprint stv v < dimword(:256) /\
  w2n b + type_memory_size dtv < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a + val_footprint stv v ==>
    ~(w2n b <= i /\ i < w2n b + type_memory_size dtv)) /\
  (is_bytestring_type dty /\ is_bytestring_type sty ==>
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    len+31 < dimword(:256) /\
    32 + 32 * ((len+31) DIV 32) < dimword(:256)) /\
  (is_word_type dty \/
   (is_bytestring_type dty /\ is_bytestring_type sty) \/
   (~is_word_type dty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
    ~acyclic_struct_metadata ce.ce_struct_fields)) ==>
  widened_normalize_outcome D ctx fn PG sa sb dtv v b G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type dty`
  >- (`sty = dty` by metis_tac[type_widens_to_word] >> gvs[] >>
      `type_memory_size dtv = 32` by metis_tac[typed_word_store] >>
      `ptr_covers G tn dst s 32` by metis_tac[] >>
      drule_all robust_typed_word_clean >> strip_tac >>
      `mload (w2n a) s = typed_val_to_w256 dtv v` by
        metis_tac[mem_word_at_eq_mload, mem_agree_outside_def] >>
      drule_all compile_store_word_code >> strip_tac >>
      `tmp <> dst` by metis_tac[] >>
      `sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst id MLOAD [Var src] [tmp];
         mk_inst (id+1) MSTORE [Var dst; Var tmp] []]` by simp[] >>
      `sb.cs_current_bb = sa.cs_current_bb` by simp[] >>
      drule_all fn_has_code_same_block >> strip_tac >>
      qabbrev_tac `u = update_var tmp (mload (w2n a) s) s` >>
      qabbrev_tac `G1 = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) u` >>
      qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn` >>
      qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
      `lookup_var dst t = SOME b /\
       eval_operand (Var tmp) t = SOME (mload (w2n a) s)` by
        (simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def,
              eval_operand_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
      `ptr_covers G1 tn1 dst t 32` by
        (simp[NoAsms, Abbr `G1`, Abbr `tn1`, Abbr `t`, Abbr `u`] >>
         rewrite_tac [ptr_covers_inst_idx] >>
         irule mload_preserves_ptr_covers >> simp[]) >>
      `op_taint tn1 (Var tmp) = {}` by
        (simp[NoAsms, Abbr `tn1`, Abbr `u`] >>
         irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]) >>
      qabbrev_tac `z = mstore (w2n b) (mload (w2n a) s) t` >>
      qabbrev_tac `G2 = step_prov PG G1
        (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) z` >>
      qabbrev_tac `tn2 = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
        t z tn1` >>
      simp[widened_normalize_outcome_def] >> disj2_tac >>
      qexistsl_tac [`G2`, `tn2`, `z with vs_inst_idx := SUC t.vs_inst_idx`] >>
      conj_tac
      >- (`get_instruction bb s.vs_inst_idx =
            SOME (mk_inst id MLOAD [Var src] [tmp])` by
            (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
          `get_instruction bb t.vs_inst_idx =
            SOME (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])` by
            (qpat_x_assum `!i. _` (qspec_then `1` mp_tac) >> simp[Abbr `t`, ADD1]) >>
          `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u` by
            (pure_once_rewrite_tac[step_inst_base_def] >>
             simp[mk_inst_def, exec_read1_def, eval_operand_def, Abbr `u`]) >>
          `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) t = OK z` by
            (pure_once_rewrite_tac[step_inst_base_def] >>
             simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `z`]) >>
          irule (gas_path_ptr_step |> Q.INST
            [`i` |-> `mk_inst id MLOAD [Var src] [tmp]`, `n` |-> `0`] |>
            SRULE [mk_inst_def, is_terminator_def]) >>
          conj_tac >- simp[] >>
          qexistsl_tac [`bb`, `id`, `src`, `tmp`, `u`] >>
          simp[GSYM mk_inst_def] >>
          conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
          `u with vs_inst_idx := SUC (LENGTH sa.cs_current_insts) = t` by
            simp[Abbr `t`] >> asm_rewrite_tac[] >>
          irule (gas_path_ptr_step |> Q.INST
            [`i` |-> `mk_inst j MSTORE [Var dst; Var tmp] []`, `n` |-> `0`] |>
            SRULE [mk_inst_def, is_terminator_def]) >>
          `~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb` by
            simp[Abbr `t`, Abbr `u`, update_var_def] >> simp[] >>
          qexistsl_tac [`dst`, `id+1`, `tmp`, `z`] >> simp[GSYM mk_inst_def] >>
          conj_tac >- (irule ptr_inst_ok_mstore >> simp[]) >>
          simp[Abbr `G2`, Abbr `tn2`] >>
          irule (cj 1 gas_path_ptr_rules) >>
          simp[Abbr `z`, Abbr `t`, Abbr `u`, mstore_def, update_var_def]) >>
      `G2 = G1 /\ tn2.t_var = tn1.t_var /\
       tn2.t_mem = tn1.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
       tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans` by
        (simp[NoAsms, Abbr `G2`, Abbr `tn2`, Abbr `z`] >>
         metis_tac[mstore_ghost_frame]) >>
      `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
       tn1.t_trans = tn.t_trans` by
        (simp[NoAsms, Abbr `tn1`, Abbr `u`] >>
         conj_tac >- (irule (cj 2 mload_ghost_clean) >> simp[eval_operand_def]) >>
         conj_tac >- (irule (cj 3 mload_ghost_clean) >> simp[eval_operand_def]) >>
         irule (cj 4 mload_ghost_clean) >> simp[eval_operand_def]) >>
      `z.vs_current_bb = s.vs_current_bb /\ ~z.vs_halted /\
       t.vs_inst_idx = SUC s.vs_inst_idx /\
       z.vs_memory = (mstore (w2n b) (typed_val_to_w256 dtv v) s).vs_memory /\
       (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
         vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
         vs_inst_idx := s.vs_inst_idx|>) = s` by
        (simp[Abbr `z`, Abbr `t`, Abbr `u`, mstore_def, update_var_def] >>
         gvs[venom_state_component_equality]) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> irule typed_word_store_robust_ptr >>
          simp[] >> metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> `tmp <> p` by metis_tac[] >>
          simp[Abbr `z`, Abbr `t`, Abbr `u`, lookup_var_def,
               update_var_def, mstore_def, FLOOKUP_UPDATE, op_taint_def] >>
          simp[Abbr `G1`, Abbr `tn1`, step_prov_def, set_prov_def,
               out_prov_def, step_taint_def, set_var_taint_def,
               op_taint_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
      conj_tac
      >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
      conj_tac
      >- simp[Abbr `tn2`, Abbr `tn1`, step_taint_def, imm_taint_def,
              mk_inst_def, step_writes_def] >>
      conj_tac
      >- (simp[Abbr `z`, Abbr `t`, Abbr `u`, mstore_def, update_var_def] >>
          gvs[venom_state_component_equality]) >>
      rpt strip_tac >>
      qpat_x_assum `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory ft fv p mem`
        (mp_then Any mp_tac robust_val_in_memory_exterior_frame) >>
      simp[] >> disch_then irule >>
      qexistsl_tac [`(mstore (w2n b) (typed_val_to_w256 dtv v) s).vs_memory`,
        `tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32}`,
        `{i | w2n b <= i /\ i < w2n b+32}`] >>
      simp[] >> rpt strip_tac >>
      irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  Cases_on `is_bytestring_type dty /\ is_bytestring_type sty`
  >- (gnvs[] >>
      qpat_x_assum `is_bytestring_type dty /\ is_bytestring_type sty`
        (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `(_ \/ _) /\ _` (map_every assume_tac o CONJUNCTS) >>
      `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
        metis_tac[compile_store_memory_typed_bytes] >>
      `?n. n = 32 + 32 * ((len+31) DIV 32)` by simp[] >>
      `n < dimword(:256)` by simp[] >>
      drule_all normalize_bytes_child_counted_ptr >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      simp[widened_normalize_outcome_def] >> disj2_tac >>
      qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
      qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _;
        vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  `?a' t. step_inst_base (mk_inst sa.cs_next_id INVALID [] []) s = Abort a' t` by
    metis_tac[step_invalid] >>
  `~acyclic_struct_metadata ce.ce_struct_fields` by metis_tac[] >>
  drule_all store_memory_typed_invalid_counted >> strip_tac >>
  simp[widened_normalize_outcome_def] >> metis_tac[]
QED

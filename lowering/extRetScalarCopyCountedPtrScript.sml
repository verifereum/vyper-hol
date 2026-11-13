Theory extRetScalarCopyCountedPtr
Ancestors
  extRetCopyCountedPtr typedCopyPtr fragGasSeqPtr fragExec
  fragExecPtr bodyPtrDefs fragGasPathPtr
  venomExecSemantics venomInstProofs venomInst venomState
  ptrSafeRun ptrDiscipline finite_map compileEnv emitHelper arithmetic wordLoadStorePtr
(* Concrete emitted word copy.  Source cleanliness is an actual read-window
   premise, not a consequence of ghost buffer coverage. *)
Theorem compile_store_word_counted_ptr:
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
        (qpat_x_assum `!i. _` (qspec_then `1` mp_tac) >>
         simp[Abbr `v1`, ADD1]) >>
      `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK s1` by
        (pure_once_rewrite_tac[step_inst_base_def] >>
         simp[mk_inst_def, exec_read1_def, eval_operand_def, Abbr `s1`]) >>
      `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) v1 = OK s2` by
        (pure_once_rewrite_tac[step_inst_base_def] >>
         simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `s2`]) >>
      irule (gas_path_ptr_step |> Q.INST
        [`i` |-> `mk_inst id MLOAD [Var src] [tmp]`, `n` |-> `0`] |>
        SRULE [mk_inst_def]) >>
      simp[is_terminator_def] >>
      qexistsl_tac [`id`, `src`, `tmp`, `s1`] >>
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
  rpt strip_tac >> `tmp <> p` by metis_tac[] >>
  simp[Abbr `G2`, Abbr `G1`, Abbr `tn1`, Abbr `v1`, Abbr `s1`,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
       lookup_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED


(* Singleton-entry form for the zero-count sequential composition interface. *)
Theorem compile_store_word_copy_path_ptr:
  is_word_type ty /\
  compile_store_memory_typed ce (Var dst) ty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  copy_path_ptr D 0 ctx fn PG
    (\g t v. g = G /\ t = tn /\ v = s)
    (\g t v.
      v.vs_current_bb = sb.cs_current_bb /\
      v.vs_inst_idx = LENGTH sb.cs_current_insts /\
      v.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
        v.vs_memory s.vs_memory /\
      t.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
      t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p v = lookup_var p s /\
        FLOOKUP g p = FLOOKUP G p /\
        op_taint t (Var p) = op_taint tn (Var p))) R
Proof
  strip_tac >> drule_all compile_store_word_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  simp[copy_path_ptr_def] >>
  qexistsl_tac [`Gf`, `tnf`, `OK sf`] >> simp[]
QED

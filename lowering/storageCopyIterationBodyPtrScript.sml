(* Finite checked chunks for the storage/transient word-copy loop. *)
Theory storageCopyIterationBodyPtr
Ancestors
  storageCopyInvariantPtr storageCopyBodyPtr stmtAppendStorageRunPtr
  fragGasPathPtr ptrDiscipline ptrSafeRun bodyPtrDefs exprSimStorageCopy
  venomState venomInst finite_map pred_set words

Theorem storage_copy_load_pair_path_ptr:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  (loc = LocStorage \/ loc = LocTransient) /\
  sv IN scratch /\ vv IN scratch /\ sv <> vv /\
  sv <> cv /\ vv <> cv /\ sv <> root /\ vv <> root /\
  src <> Var sv /\ src <> Var vv /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src; Var cv] [sv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G' tn' t /\
    lookup_var vv t = SOME (copy_runtime_word loc s (a+n2w k)) /\
    op_taint tn' (Var vv) = key_taint
      (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) (a+n2w k) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    ~t.vs_halted
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `storage_copy_inv_ptr` mp_tac >>
  rewrite_tac[Once storage_copy_inv_ptr_def] >> strip_tac >>
  qabbrev_tac `u = update_var sv (a+n2w k) s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `i = mk_inst id ADD [src;Var cv] [sv]` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (sv,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, Abbr `u`, Abbr `s1`] >>
     irule storage_copy_arith_path_ptr >>
     simp[eval_operand_def] >> metis_tac[]) >>
  suspend "finish"
QED

Resume storage_copy_load_pair_path_ptr[finish]:
  all_tac >>
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G1 tn1 s1` by
    (simp[Abbr `s1`, Abbr `u`, Abbr `tn1`] >>
     irule storage_copy_inv_ptr_scratch >> simp[] >> qexists_tac `G` >> simp[] >>
     simp[Abbr `G1`, Abbr `i`, scalar_step_old_prov]) >>
  qabbrev_tac `v = update_var vv (copy_runtime_word loc s (a+n2w k)) s1` >>
  qabbrev_tac `t = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {vv})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+
    (vv,key_taint (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) (a+n2w k))` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK t)` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `t`, Abbr `v`, copy_runtime_word_def] >>
     `tnbase.t_stor = tn1.t_stor /\ tnbase.t_trans = tn1.t_trans` by
       simp[Abbr `tn1`] >>
     `sload (a+n2w k) s = sload (a+n2w k) s1 /\
      tload (a+n2w k) s = tload (a+n2w k) s1` by
       simp[Abbr `s1`, Abbr `u`, update_var_def, tload_def, sload_def,
            contract_storage_def, contract_transient_def] >>
     simp[] >>
     Cases_on `loc = LocStorage`
     >- (gvs[] >> irule (SRULE[] (Q.INST [`tr` |-> `F`] storage_copy_load_path_ptr)) >>
         simp[Abbr `s1`, Abbr `u`, Abbr `tn1`, update_var_def, lookup_var_def,
              eval_operand_def, op_taint_def, FLOOKUP_UPDATE] >>
         qexistsl_tac [`id+1`, `Var sv`] >>
         simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
     gvs[] >> irule (SRULE[] (Q.INST [`tr` |-> `T`] storage_copy_load_path_ptr)) >>
     simp[Abbr `s1`, Abbr `u`, Abbr `tn1`, update_var_def, lookup_var_def,
          eval_operand_def, op_taint_def, FLOOKUP_UPDATE] >>
     qexistsl_tac [`id+1`, `Var sv`] >>
     simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G2 tn2 t` by
    (simp[Abbr `t`, Abbr `v`, Abbr `tn2`] >>
     irule storage_copy_inv_ptr_scratch >> simp[] >> qexists_tac `G1` >> simp[] >>
     simp[Abbr `G2`, FLOOKUP_DRESTRICT]) >>
  qexistsl_tac [`G2`, `tn2`, `t`] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[Abbr `tn2`, Abbr `t`, Abbr `v`, Abbr `s1`, Abbr `u`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]
QED

Finalise storage_copy_load_pair_path_ptr

Theorem storage_copy_increment_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var cv; Lit 1w] [nv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) ASSIGN [Var nv] [cv]) /\
  lookup_var cv s = SOME (n2w k) /\
  op_prov G (Var cv) = NONE /\ op_taint tn (Var cv) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {nv})) (COMPL {cv}))
    (tn with t_var := (tn.t_var |+ (nv,{})) |+ (cv,{}))
    (OK (update_var cv (n2w (k+1)) (update_var nv (n2w (k+1)) s)
      with vs_inst_idx := s.vs_inst_idx+2))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var nv (n2w (k+1)) s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {nv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (nv,{})` >>
  `step_prov PG G (mk_inst id ADD [Var cv; Lit 1w] [nv]) u = G1` by
    (simp[Abbr `G1`, step_prov_def, set_prov_def, out_prov_def,
          first_prov_def, op_prov_def, mk_inst_def] >> gvs[op_prov_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (simp[Abbr `s1`, Abbr `u`, Abbr `tn1`] >>
     mp_tac (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`,
                    `left` |-> `Var cv`, `right` |-> `Lit 1w`, `out` |-> `nv`,
                    `a` |-> `n2w k`, `b` |-> `1w`] storage_copy_arith_path_ptr) >>
     simp[eval_operand_def, GSYM word_add_n2w] >>
     gvs[op_taint_def, GSYM word_add_n2w]) >>
  suspend "assign"
QED

Resume storage_copy_increment_path_ptr[assign]:
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0
    (DRESTRICT G1 (COMPL {cv})) (tn1 with t_var := tn1.t_var |+ (cv,{}))
    (OK (update_var cv (n2w (k+1)) s1 with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule storage_copy_counter_assign_path_ptr >>
     simp[Abbr `s1`, Abbr `u`, Abbr `G1`, Abbr `tn1`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
          op_prov_def, op_taint_def] >>
     qexistsl_tac [`id+1`, `nv`] >> simp[]) >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`, Abbr `u`, update_var_def,
       arithmeticTheory.ADD1]
QED

Finalise storage_copy_increment_path_ptr

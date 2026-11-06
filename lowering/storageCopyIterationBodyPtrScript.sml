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
    lookup_var vv t = SOME (copy_runtime_word loc sbase (a+n2w k)) /\
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
  `copy_runtime_word loc s (a+n2w k) = copy_runtime_word loc sbase (a+n2w k)` by
    (irule copy_runtime_word_static >> gvs[copy_prefix_def]) >>
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

Theorem storage_copy_destination_pair_path_ptr:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  mv IN scratch /\ dv IN scratch /\ mv <> dv /\
  mv <> cv /\ dv <> cv /\ mv <> root /\ dv <> root /\
  src <> Var mv /\ src <> Var dv /\
  k < n /\ b+32*n < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var cv; Lit 32w] [mv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) ADD [Var root; Var mv] [dv]) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G' tn' t /\
    ptr_covers G' tn' dv t 32 /\ lookup_var dv t = SOME (n2w (b+32*k)) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
    ~t.vs_halted /\
    (!x. x <> mv /\ x <> dv ==>
      lookup_var x t = lookup_var x s /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt strip_tac >>
  qhdtm_assum `storage_copy_inv_ptr` mp_tac >>
  rewrite_tac[Once storage_copy_inv_ptr_def] >> strip_tac >>
  qabbrev_tac `u = update_var mv (n2w (32*k)) s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `i = mk_inst id MUL [Var cv; Lit 32w] [mv]` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (mv,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, Abbr `u`, Abbr `s1`] >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     simp[GSYM word_mul_n2w] >>
     irule storage_copy_arith_path_ptr >> simp[eval_operand_def, op_taint_def] >>
     gvs[op_taint_def]) >>
  suspend "destination"
QED

Resume storage_copy_destination_pair_path_ptr[destination]:
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G1 tn1 s1` by
    (simp[Abbr `s1`, Abbr `u`, Abbr `tn1`] >>
     irule storage_copy_inv_ptr_scratch >> simp[] >> qexists_tac `G` >> simp[] >>
     simp[Abbr `G1`, Abbr `i`, scalar_step_old_prov]) >>
  qabbrev_tac `v = update_var dv (n2w b + n2w (32*k)) s1` >>
  qabbrev_tac `t = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `j = mk_inst (id+1) ADD [Var root; Var mv] [dv]` >>
  qabbrev_tac `G2 = step_prov PG G1 j v` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (dv,{})` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK t)` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `j`, Abbr `v`, Abbr `t`] >>
     irule storage_copy_arith_path_ptr >>
     simp[Abbr `s1`, Abbr `u`, Abbr `tn1`, update_var_def, lookup_var_def,
          eval_operand_def, FLOOKUP_UPDATE, op_taint_def] >>
     gvs[ptr_covers_def, op_taint_def, lookup_var_def]) >>
  suspend "coverage"
QED

Resume storage_copy_destination_pair_path_ptr[coverage]:
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G2 tn2 t` by
    (simp[Abbr `t`, Abbr `v`, Abbr `tn2`] >>
     irule storage_copy_inv_ptr_scratch >> simp[] >> qexists_tac `G1` >> simp[] >>
     simp[Abbr `G2`, Abbr `j`, scalar_step_old_prov]) >>
  `ptr_covers G1 tn1 root s1 (32*n)` by
    gvs[storage_copy_inv_ptr_def] >>
  `lookup_var root s1 = SOME (n2w b)` by
    (simp[Abbr `s1`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `32*k < dimword(:256) /\ b < dimword(:256) /\ b+32*k < dimword(:256)` by
    decide_tac >>
  `ptr_covers G2 tn2 dv t 32` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `j`, Abbr `v`, Abbr `t`] >>
     irule (SRULE[] storage_copy_add_covers) >> simp[] >>
     qexists_tac `32*n` >> simp[] >> decide_tac) >>
  qexistsl_tac [`G2`, `tn2`, `t`] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[Abbr `tn2`, Abbr `t`, Abbr `v`, Abbr `s1`, Abbr `u`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE, word_add_n2w,
       arithmeticTheory.ADD1, op_taint_def] >> rpt strip_tac >>
  simp[Abbr `tn1`, FLOOKUP_UPDATE]
QED

Finalise storage_copy_destination_pair_path_ptr

Theorem storage_copy_store_chunk_path_ptr:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  mv IN scratch /\ dv IN scratch /\ mv <> dv /\
  mv <> cv /\ dv <> cv /\ mv <> root /\ dv <> root /\
  src <> Var mv /\ src <> Var dv /\ vv <> mv /\ vv <> dv /\
  k < n /\ b+32*n < dimword(:256) /\
  lookup_var vv s = SOME w /\ op_taint tn (Var vv) = key_taint X slot /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var cv; Lit 32w] [mv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) ADD [Var root; Var mv] [dv]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME
    (mk_inst (id+2) MSTORE [Var dv; Var vv] []) ==>
  ?G' tn' u.
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G' tn' u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn' with t_mem :=
        (tn'.t_mem DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
        IMAGE (\r. b+32*k+r) {r | r < 32 /\ (slot,r) IN X})
      (OK (mstore (b+32*k) w u with vs_inst_idx := s.vs_inst_idx+3)) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\
    ~u.vs_halted
Proof
  rpt strip_tac >>
  drule_all storage_copy_destination_pair_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u)` >>
  `lookup_var vv u = SOME w /\ op_taint tn' (Var vv) = key_taint X slot` by
    metis_tac[] >>
  suspend "store"
QED

Resume storage_copy_store_chunk_path_ptr[store]:
  `b+32*k < dimword(:256)` by decide_tac >>
  `gas_path_ptr D 0 ctx fn PG G' tn' u 0 G'
    (step_taint (mk_inst (id+2) MSTORE [Var dv;Var vv] []) u
      (mstore (b+32*k) w u) tn')
    (OK (mstore (b+32*k) w u with vs_inst_idx := SUC u.vs_inst_idx))` by
    (qsuff_tac `gas_path_ptr D 0 ctx fn PG G' tn' u 0 G'
       (step_taint (mk_inst (id+2) MSTORE [Var dv;Var vv] []) u
         (mstore (w2n (n2w (b+32*k):bytes32)) w u) tn')
       (OK (mstore (w2n (n2w (b+32*k):bytes32)) w u with vs_inst_idx := SUC u.vs_inst_idx))`
     >- simp[] >>
     irule storage_copy_mstore_path_ptr >> simp[eval_operand_def] >>
     qexistsl_tac [`bb`, `n2w (b+32*k)`] >> simp[]) >>
  `{b+32*k+r | r < 32 /\ (slot,r) IN X} =
    IMAGE (\r. b+32*k+r) {r | r < 32 /\ (slot,r) IN X}` by
    (simp[EXTENSION, IN_IMAGE] >> metis_tac[]) >>
  `step_taint (mk_inst (id+2) MSTORE [Var dv;Var vv] []) u
    (mstore (b+32*k) w u) tn' =
    tn' with t_mem :=
      (tn'.t_mem DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
      IMAGE (\r. b+32*k+r) {r | r < 32 /\ (slot,r) IN X}` by
    (`eval_operand (Var dv) u = SOME (n2w (b+32*k)) /\
      eval_operand (Var vv) u = SOME w` by simp[eval_operand_def] >>
     qpat_assum `eval_operand (Var dv) u = _`
       (mp_then Any mp_tac storage_copy_mstore_ghost) >>
     disch_then drule >> simp[] >>
     disch_then (qspecl_then [`tn'`, `slot`, `id+2`, `X`] mp_tac) >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`G'`, `tn'`, `u`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[arithmeticTheory.ADD1]
QED

Finalise storage_copy_store_chunk_path_ptr


Theorem storage_copy_source_store_chunk_path_ptr:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  mv IN scratch /\ dv IN scratch /\ mv <> dv /\
  mv <> cv /\ dv <> cv /\ mv <> root /\ dv <> root /\
  src <> Var mv /\ src <> Var dv /\ vv <> mv /\ vv <> dv /\
  k < n /\ b+32*n < dimword(:256) /\
  lookup_var vv s = SOME (copy_runtime_word loc sbase (a+n2w k)) /\
  op_taint tn (Var vv) = key_taint
    (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) (a+n2w k) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var cv; Lit 32w] [mv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) ADD [Var root; Var mv] [dv]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME
    (mk_inst (id+2) MSTORE [Var dv; Var vv] []) ==>
  ?G' tn' u.
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G' tn' u /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn' with t_mem :=
        (tn'.t_mem DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
        IMAGE (\r. b+32*k+r) {r | r < 32 /\
          (a+n2w k,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans)})
      (OK (mstore (b+32*k) (copy_runtime_word loc sbase (a+n2w k)) u
        with vs_inst_idx := s.vs_inst_idx+3)) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\
    ~u.vs_halted
Proof
  strip_tac >> irule storage_copy_store_chunk_path_ptr >> simp[] >>
  qexistsl_tac [`dv`, `id`, `mv`, `vv`] >> simp[]
QED

Theorem storage_copy_body_path_ptr:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  (loc = LocStorage \/ loc = LocTransient) /\
  ALL_DISTINCT [sv;vv;mv;dv;nv;cv;root] /\
  EVERY (\x. x IN scratch /\ src <> Var x) [sv;vv;mv;dv;nv;cv] /\
  k < n /\ b+32*n < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src; Var cv] [sv]) /\
  get_instruction bb (s.vs_inst_idx+1) = SOME
    (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) /\
  get_instruction bb (s.vs_inst_idx+2) = SOME
    (mk_inst (id+2) MUL [Var cv; Lit 32w] [mv]) /\
  get_instruction bb (s.vs_inst_idx+3) = SOME
    (mk_inst (id+3) ADD [Var root; Var mv] [dv]) /\
  get_instruction bb (s.vs_inst_idx+4) = SOME
    (mk_inst (id+4) MSTORE [Var dv; Var vv] []) /\
  get_instruction bb (s.vs_inst_idx+5) = SOME
    (mk_inst (id+5) ADD [Var cv; Lit 1w] [nv]) /\
  get_instruction bb (s.vs_inst_idx+6) = SOME
    (mk_inst (id+6) ASSIGN [Var nv] [cv]) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase (k+1) G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx+7 /\
    ~t.vs_halted
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [listTheory.ALL_DISTINCT, listTheory.EVERY_DEF]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `vv <> sv /\ dv <> mv` by metis_tac[] >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv])` by
    simp[arithmeticTheory.ADD1] >>
  drule_all storage_copy_load_pair_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  suspend "store_chunk"
QED

Resume storage_copy_body_path_ptr[store_chunk]:
  `vv <> mv /\ vv <> dv` by metis_tac[] >>
  `get_instruction bb s1.vs_inst_idx = SOME
     (mk_inst (id+2) MUL [Var cv; Lit 32w] [mv]) /\
   get_instruction bb (SUC s1.vs_inst_idx) = SOME
     (mk_inst ((id+2)+1) ADD [Var root; Var mv] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME
     (mk_inst ((id+2)+2) MSTORE [Var dv; Var vv] []) /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[arithmeticTheory.ADD1] >>
  drule_all storage_copy_source_store_chunk_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qabbrev_tac `s2 = mstore (b+32*k) (copy_runtime_word loc sbase (a+n2w k)) u
    with vs_inst_idx := s1.vs_inst_idx+3` >>
  qabbrev_tac `tn2 = tn' with t_mem :=
    (tn'.t_mem DIFF {x | b+32*k <= x /\ x < b+32*k+32}) UNION
    IMAGE (\r. b+32*k+r) {r | r < 32 /\
      (a+n2w k,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans)}` >>
  suspend "increment"
QED

Resume storage_copy_body_path_ptr[increment]:
  `lookup_var cv u = SOME (n2w k) /\ op_prov G' (Var cv) = NONE /\
   op_taint tn' (Var cv) = {}` by
    fs[storage_copy_inv_ptr_def] >>
  qabbrev_tac `G3 = DRESTRICT (DRESTRICT G' (COMPL {nv})) (COMPL {cv})` >>
  qabbrev_tac `tn3 = tn2 with t_var := (tn2.t_var |+ (nv,{})) |+ (cv,{})` >>
  qabbrev_tac `t = update_var cv (n2w (k+1)) (update_var nv (n2w (k+1)) s2)
    with vs_inst_idx := s2.vs_inst_idx+2` >>
  `gas_path_ptr D 0 ctx fn PG G' tn2 s2 0 G3 tn3 (OK t)` by
    (map_every qunabbrev_tac [`G3`, `tn3`, `t`] >>
     irule storage_copy_increment_path_ptr >>
     simp[Abbr `s2`, Abbr `tn2`, lookup_var_def, mstore_def,
          write_memory_with_expansion_def, op_taint_def, arithmeticTheory.ADD1] >>
     fs[lookup_var_def, op_taint_def] >> qexists_tac `id+5` >> simp[]) >>
  suspend "successor"
QED

Resume storage_copy_body_path_ptr[successor]:
  `IMAGE (\r. b+32*k+r) {r | r < 32 /\
     (a+n2w k,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans)} =
   {x | ?r. r < 32 /\
     (a+n2w k,r) IN (if loc = LocStorage then tnbase.t_stor else tnbase.t_trans) /\
     x = b+32*k+r}` by
    (simp[EXTENSION, IN_IMAGE] >> metis_tac[]) >>
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase (k+1)
     G3 tn3 t` by
    (simp[Abbr `G3`, Abbr `tn3`, Abbr `t`, Abbr `s2`, Abbr `tn2`] >>
     mp_tac (Q.INST [`s` |-> `u with vs_inst_idx := s1.vs_inst_idx+3`,
       `G` |-> `G'`, `tn` |-> `tn'`] storage_copy_inv_ptr_store_increment) >>
     simp[update_var_def, mstore_def, write_memory_with_expansion_def,
          arithmeticTheory.LEFT_ADD_DISTRIB]) >>
  qexistsl_tac [`G3`, `tn3`, `t`] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[] >> disch_then assume_tac >>
      irule (SRULE[] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
      qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
  simp[Abbr `t`, Abbr `s2`, update_var_def, mstore_def,
       write_memory_with_expansion_def]
QED

Finalise storage_copy_body_path_ptr

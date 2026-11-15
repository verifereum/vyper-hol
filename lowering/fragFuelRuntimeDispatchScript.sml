(*
 * Fuel bounds for the runtime's selector dispatch.
 *
 * Each dispatcher jumps only to the fallback label, to the entry labels of
 * its selectors, and to blocks it starts itself.  The sparse dispatcher's
 * jump table targets the bucket blocks it emits after the table; the dense
 * dispatcher's targets the entry labels.  Data sections emit no code.
 *
 * TOP-LEVEL:
 *   fuel_ok_emit_inst_djmp, fuel_ok_data, fuel_ok_foldl,
 *   fuel_ok_compile_selector_checks,
 *   fuel_ok_compile_selector_dispatch_linear,
 *   fuel_ok_compile_selector_dispatch_sparse,
 *   fuel_ok_compile_selector_dispatch_dense
 *)

Theory fragFuelRuntimeDispatch
Ancestors
  fragFuel fragExec moduleLowering compileEnv emitHelper venomInst
  venomExecSemantics venomExecProofs venomState list alist pred_set pair
Libs
  fragFuelLib

(* ===== Jump tables ===== *)

Theorem extract_labels_MAP_Label[simp]:
  !ls. extract_labels (MAP Label ls) = SOME ls
Proof
  Induct >> simp[extract_labels_def]
QED

Theorem extract_labels_MEM[local]:
  !ops ls l. extract_labels ops = SOME ls /\ MEM l ls ==> MEM (Label l) ops
Proof
  ho_match_mp_tac extract_labels_ind >> rw[extract_labels_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

val djmp_err_tac =
  simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs] >>
  simp[Once exec_block_def, step_inst_non_invoke, step_inst_base_opcode_eqs]

Theorem fuel_ok_emit_djmp[local]:
  !inst sel ops Wv E.
    inst.inst_opcode = DJMP /\ inst.inst_operands = sel :: ops /\
    (!l. MEM (Label l) ops ==> l IN E) ==>
    fuel_ok Wv {} E (emit inst)
Proof
  rpt strip_tac >> simp[fuel_ok_def, emit_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- (simp[cs_extends_def] >> qexists_tac `[]` >> simp[])
  >- fs[cs_no_phi_def] >>
  qexists_tac `1` >> rw[frag_fuel_def] >>
  drule_all emit_frag_inst >> strip_tac >>
  qexists_tac `1` >> simp[] >>
  Cases_on `eval_operand sel s` >- djmp_err_tac >>
  rename1 `eval_operand sel s = SOME w` >>
  Cases_on `extract_labels ops` >- djmp_err_tac >>
  rename1 `extract_labels ops = SOME ls` >>
  reverse (Cases_on `w2n w < LENGTH ls`) >- djmp_err_tac >>
  `EL (w2n w) ls IN E` by metis_tac[extract_labels_MEM, MEM_EL] >>
  irule fuel_outcome_jump >>
  simp[is_terminator_def, step_inst_base_opcode_eqs] >>
  qexists_tac `EL (w2n w) ls` >>
  simp[jump_to_def, vars_kept_def, lookup_var_def]
QED

Theorem fuel_ok_emit_inst_djmp:
  !sel ops Wv E.
    (!l. MEM (Label l) ops ==> l IN E) ==>
    fuel_ok Wv {} E (emit_inst DJMP (sel :: ops) [])
Proof
  rw[emit_inst_def] >> match_mp_tac fuel_ok_bind0 >>
  conj_tac >- simp[fuel_ok_prims] >>
  gen_tac >> BETA_TAC >> match_mp_tac fuel_ok_emit_djmp >>
  simp[mk_inst_def]
QED

(* ===== Data sections ===== *)

Theorem fuel_ok_data:
  (!l Wv E. fuel_ok Wv {} E (emit_data_section l)) /\
  (!d Wv E. fuel_ok Wv {} E (emit_data_item d))
Proof
  rpt conj_tac >> rpt gen_tac >> irule fuel_ok_no_code >>
  rw[emit_data_section_def, emit_data_item_def] >> gvs[AllCaseEqs()]
QED

Theorem fuel_ok_foldl:
  !xs f m Wv E.
    fuel_ok Wv {} E m /\
    (!m x. fuel_ok Wv {} E m ==> fuel_ok Wv {} E (f m x)) ==>
    fuel_ok Wv {} E (FOLDL f m xs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* fuel_auto, with tactics tried before its own steps. *)
fun fuel_auto_pre pre ths =
  rpt (FIRST (pre @ [fuel_step] @ map leaf_tac (leaf_thms ths) @
              [first_assum MATCH_ACCEPT_TAC]))

val foldl_tac =
  match_mp_tac fuel_ok_foldl >> conj_tac
  >- MATCH_ACCEPT_TAC fuel_ok_return >>
  rpt gen_tac >> disch_tac >> BETA_TAC

val uncurry_tac =
  CHANGED_TAC (PURE_REWRITE_TAC [pairTheory.UNCURRY]) >> BETA_TAC

Theorem fuel_ok_emit_dense_data_sections[local]:
  !dbs fmb ei Wv E. fuel_ok Wv {} E (emit_dense_data_sections dbs fmb ei)
Proof
  Induct >- simp[emit_dense_data_sections_def, fuel_ok_return] >>
  rpt gen_tac >> PURE_ONCE_REWRITE_TAC [emit_dense_data_sections_def] >>
  fuel_auto_pre [foldl_tac, uncurry_tac] [fuel_ok_data]
QED

(* ===== Linear dispatch ===== *)

Theorem fuel_ok_compile_selector_checks:
  !sels mid Wv E.
    EVERY (\p. SND p IN E) sels ==>
    fuel_ok Wv {} E (compile_selector_checks mid sels)
Proof
  Induct >- simp[compile_selector_checks_def, fuel_ok_return] >>
  Cases >> rpt strip_tac >> fs[] >>
  last_x_assum (qspecl_then [`mid`, `Wv`, `E`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  PURE_ONCE_REWRITE_TAC [compile_selector_checks_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst_jmp] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_selector_dispatch_linear:
  !sels fb Wv E.
    fb IN E /\ EVERY (\p. SND p IN E) sels ==>
    fuel_ok Wv {} E (compile_selector_dispatch_linear sels fb)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_selector_dispatch_linear_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst_jmp,
             fuel_ok_compile_selector_checks] >>
  simp[is_terminator_def]
QED

(* ===== Sparse dispatch ===== *)

Theorem fuel_ok_compile_sparse_bucket_search[local]:
  !items mid fb Wv E.
    fb IN E /\ EVERY (\x. FST (SND x) IN E) items ==>
    fuel_ok Wv {} E (compile_sparse_bucket_search mid items fb)
Proof
  Induct
  >- (simp[compile_sparse_bucket_search_def] >> rpt strip_tac >>
      irule fuel_ok_emit_inst_jmp >> simp[]) >>
  PairCases >> rpt strip_tac >> fs[] >>
  last_x_assum (qspecl_then [`mid`, `fb`, `Wv`, `E`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  PURE_ONCE_REWRITE_TAC [compile_sparse_bucket_search_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz, fuel_ok_emit_inst_jmp] >>
  simp[is_terminator_def]
QED

Theorem group_into_buckets_every[local]:
  !sels n P.
    EVERY P sels ==> EVERY (\b. EVERY P (SND b)) (group_into_buckets sels n)
Proof
  Induct >- simp[group_into_buckets_def] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [group_into_buckets_def, LET_THM] >> fs[] >>
  first_x_assum (drule_then (qspec_then `n` assume_tac)) >>
  rw[EVERY_MAP] >> fs[EVERY_MEM, FORALL_PROD] >> rw[] >> res_tac >> fs[]
QED

Theorem alloc_bucket_labels_length[local]:
  !n st ls st'. alloc_bucket_labels n st = (ls, st') ==> LENGTH ls = n
Proof
  Induct >>
  simp[Once alloc_bucket_labels_def, comp_bind_def, comp_return_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> fs[]) >> gvs[] >> res_tac
QED

Theorem fuel_ok_alloc_bucket_labels[local]:
  !n Wv E. fuel_ok Wv {} E (alloc_bucket_labels n)
Proof
  Induct >> rw[Once alloc_bucket_labels_def] >> fuel_auto []
QED

Theorem fuel_okS_const[local]:
  !b Wv L E m. (b ==> fuel_ok Wv L E m) ==> fuel_okS (\st. b) Wv L E m
Proof
  Cases >> simp[fuel_okS_def, fuel_ok_def] >> metis_tac[]
QED

(* The bucket labels are as many as the buckets. *)
Theorem fuel_ok_alloc_bucket_bind[local]:
  !n f Wv L E.
    (!a. LENGTH a = n ==> fuel_ok Wv L E (f a)) ==>
    fuel_ok Wv L E (comp_bind (alloc_bucket_labels n) f)
Proof
  rpt strip_tac >> match_mp_tac fuel_ok_of_okS >> qexists_tac `\st. T` >>
  simp[] >>
  `fuel_okS (\st. T) Wv ({} UNION L) E (comp_bind (alloc_bucket_labels n) f)`
    suffices_by simp[] >>
  match_mp_tac fuel_okS_bind >>
  qexistsl_tac [`\a st. LENGTH a = n`, `E`, `E`] >> simp[] >> rpt conj_tac
  >- (irule fuel_okS_of_ok >> simp[fuel_ok_alloc_bucket_labels])
  >- metis_tac[alloc_bucket_labels_length] >>
  gen_tac >> irule fuel_okS_const >> simp[]
QED

Theorem fuel_ok_create_bucket_blocks[local]:
  !lbls bkts mid fb Wv E.
    LENGTH lbls = LENGTH bkts /\ fb IN E /\
    EVERY (\b. EVERY (\x. FST (SND x) IN E) (SND b)) bkts ==>
    fuel_ok Wv (set lbls) E (create_bucket_blocks mid lbls bkts fb)
Proof
  Induct
  >- (Cases >> simp[create_bucket_blocks_def, fuel_ok_return]) >>
  qx_gen_tac `lbl` >> Cases >> simp[] >>
  rename1 `create_bucket_blocks _ (lbl::lbls) (bk::bkts)` >>
  PairCases_on `bk` >> rpt strip_tac >> fs[] >>
  last_x_assum (qspecl_then [`bkts`, `mid`, `fb`, `Wv`, `E`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  PURE_ONCE_REWRITE_TAC [create_bucket_blocks_def] >>
  match_mp_tac (Q.SPECL [`{lbl}`, `set lbls`] fuel_ok_seq_fwd) >> rpt conj_tac
  >- MATCH_ACCEPT_TAC fuel_ok_new_block
  >- (match_mp_tac fuel_ok_ignore_bind0 >> conj_tac
      >- (irule fuel_ok_compile_sparse_bucket_search >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  simp[SUBSET_DEF]
QED

(* The jump table, then its data, then the bucket blocks it jumps to. *)
Theorem fuel_ok_djmp_buckets[local]:
  !sel ops s g z full mid lbls bks fb Wv E.
    (!l. MEM (Label l) ops ==> l IN E \/ MEM l lbls) /\
    fuel_ok Wv {} E (FOLDL g z full) /\
    fuel_ok Wv (set lbls) E (create_bucket_blocks mid lbls bks fb) ==>
    fuel_ok Wv {} E
      (comp_ignore_bind (emit_inst DJMP (sel :: ops) [])
        (comp_ignore_bind (emit_data_section s)
          (comp_ignore_bind (FOLDL g z full)
            (create_bucket_blocks mid lbls bks fb))))
Proof
  rpt strip_tac >>
  match_mp_tac (Q.SPECL [`{}`, `set lbls`] fuel_ok_seq_fwd) >> rpt conj_tac
  >- (irule fuel_ok_emit_inst_djmp >> metis_tac[IN_UNION])
  >- (rpt (match_mp_tac fuel_ok_ignore_bind0 >> conj_tac) >>
      simp[fuel_ok_data]) >>
  simp[]
QED

Theorem mem_map2_label[local]:
  !xs ys k v. MEM (k, v) (MAP2 (\(bid,_) lbl. (bid, lbl)) xs ys) ==> MEM v ys
Proof
  Induct >> rpt gen_tac >> Cases_on `ys` >> simp[] >>
  PairCases_on `h` >> rw[] >> metis_tac[]
QED

val alloc_tac =
  match_mp_tac fuel_ok_alloc_bucket_bind >> gen_tac >> disch_tac >> BETA_TAC

val djmp_tac = match_mp_tac fuel_ok_djmp_buckets >> rpt conj_tac

Theorem fuel_ok_compile_selector_dispatch_sparse:
  !sels n fb Wv E.
    fb IN E /\ EVERY (\x. FST (SND x) IN E) sels ==>
    fuel_ok Wv {} E (compile_selector_dispatch_sparse sels n fb)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_selector_dispatch_sparse_def] >>
  PURE_REWRITE_TAC [comp_bind_return] >> BETA_TAC >>
  fuel_auto_pre [alloc_tac, djmp_tac, foldl_tac]
    [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jnz,
     fuel_ok_emit_inst_jmp, fuel_ok_compile_selector_checks,
     fuel_ok_create_bucket_blocks, fuel_ok_data] >>
  simp[is_terminator_def]
  >- (fs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> metis_tac[])
  >- (rw[MEM_MAP, MEM_GENLIST] >> BasicProvers.every_case_tac >> simp[] >>
      drule ALOOKUP_MEM >> metis_tac[mem_map2_label]) >>
  irule group_into_buckets_every >> simp[]
QED

(* ===== Dense dispatch ===== *)

Theorem fuel_ok_compile_selector_dispatch_dense:
  !sels n fmb dbs ei lbls fb Wv E.
    fb IN E /\ EVERY (\l. l IN E) lbls ==>
    fuel_ok Wv {} E (compile_selector_dispatch_dense sels n fmb dbs ei lbls fb)
Proof
  rpt strip_tac >> simp_tac std_ss [compile_selector_dispatch_dense_def] >>
  fuel_auto_pre [foldl_tac]
    [fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jnz,
     fuel_ok_emit_inst_djmp, fuel_ok_data, fuel_ok_emit_dense_data_sections] >>
  simp[is_terminator_def] >> fs[EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

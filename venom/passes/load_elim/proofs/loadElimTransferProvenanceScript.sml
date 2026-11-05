Theory loadElimTransferProvenance
Ancestors
  loadElimDefs finite_map list rich_list pred_set

(* Syntactic generation only: no claim about a runtime operand value. *)
Definition le_transfer_generates_def:
  le_transfer_generates ctx inst k v <=>
    (inst.inst_opcode = ctx.lctx_config.lc_load /\
     ?addr out. inst.inst_operands = [addr] /\ inst.inst_outputs = [out] /\
       k = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
         (normalize_operand ctx.lctx_dfg []) inst /\ v = Var out) \/
    (inst.inst_opcode <> ctx.lctx_config.lc_load /\
     ?st addr. ctx.lctx_config.lc_store = SOME st /\ inst.inst_opcode = st /\
       inst.inst_operands = [addr;v] /\
       k = load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
         (normalize_operand ctx.lctx_dfg []) inst)
End

Theorem le_invalidate_lookup_origin[local]:
  FLOOKUP (load_invalidate aliases bp space ll key) k = SOME vs ==>
  FLOOKUP ll k = SOME vs
Proof
  simp[load_invalidate_def] >> IF_CASES_TAC >>
  simp[FLOOKUP_DRESTRICT] >>
  IF_CASES_TAC >> simp[]
QED

Theorem le_transfer_lookup_origin:
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) k = SOME vs ==>
  FLOOKUP (unwrap_load_lattice initial) k = SOME vs \/
  (?v. vs = [v] /\ le_transfer_generates ctx inst k v)
Proof
  Cases_on `inst.inst_opcode = ctx.lctx_config.lc_load`
  >- (simp[load_transfer_def, unwrap_load_lattice_def] >>
      Cases_on `inst.inst_operands` >- simp[] >>
      Cases_on `t` >- (
        Cases_on `inst.inst_outputs` >- simp[] >>
        Cases_on `t` >> simp[FLOOKUP_UPDATE, le_transfer_generates_def] >>
        IF_CASES_TAC >> simp[] >> metis_tac[]) >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = z::zs` >> Cases_on `zs` >> simp[]) >>
  Cases_on `ctx.lctx_config.lc_store` >>
  simp[load_transfer_def, unwrap_load_lattice_def] >>
  Cases_on `inst.inst_opcode = x` >> simp[]
  >- (Cases_on `inst.inst_operands` >- simp[] >>
      Cases_on `t` >- simp[] >>
      Cases_on `t'` >> simp[] >>
      simp[FLOOKUP_UPDATE, le_transfer_generates_def] >>
      IF_CASES_TAC >- (simp[] >> metis_tac[]) >>
      simp[] >> strip_tac >>
      drule le_invalidate_lookup_origin >> simp[]) >>
  IF_CASES_TAC >> simp[]
QED

Theorem le_transfer_multivalue_origin:
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) k = SOME vs /\
  1 < LENGTH vs ==> FLOOKUP (unwrap_load_lattice initial) k = SOME vs
Proof
  rpt strip_tac >> drule le_transfer_lookup_origin >>
  strip_tac >> gvs[]
QED

Theorem le_transfer_fold_multivalue_origin:
  !insts initial.
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) initial insts)) k = SOME vs /\
  1 < LENGTH vs ==> FLOOKUP (unwrap_load_lattice initial) k = SOME vs
Proof
  Induct_on `insts` >- simp[] >>
  simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >>
  strip_tac >> irule le_transfer_multivalue_origin >> metis_tac[]
QED

Theorem le_transfer_fold_multivalue_prefix:
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) initial (pre ++ post))) k = SOME vs /\
  1 < LENGTH vs ==>
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) initial pre)) k = SOME vs
Proof
  simp[FOLDL_APPEND] >> metis_tac[le_transfer_fold_multivalue_origin]
QED

Theorem le_transfer_generates_lookup:
  le_transfer_generates ctx inst k v ==>
  FLOOKUP (unwrap_load_lattice (load_transfer ctx inst initial)) k = SOME [v]
Proof
  rw[le_transfer_generates_def] >>
  simp[load_transfer_def, unwrap_load_lattice_def, FLOOKUP_UPDATE]
QED

Theorem le_prefix_snoc_cases[local]:
  !p xs q x. SNOC x xs = p ++ q ==>
    p = SNOC x xs \/ ?r. xs = p ++ r
Proof
  Induct_on `p` >- simp[] >>
  Cases_on `xs` >> simp[SNOC] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `q`, `x`] mp_tac) >> simp[SNOC_APPEND]
QED

(* Strong form: even the retained-input alternative certifies every prefix.
   The generated alternative restarts this property at its last generation. *)
Theorem le_transfer_fold_singleton_origin:
  !insts initial.
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) initial insts)) k = SOME [v] ==>
  (!p q. insts = p ++ q ==>
    FLOOKUP (unwrap_load_lattice
      (FOLDL (\ll i. load_transfer ctx i ll) initial p)) k = SOME [v]) \/
  (?before inst after.
    insts = before ++ inst::after /\ le_transfer_generates ctx inst k v /\
    !p q. after = p ++ q ==>
      FLOOKUP (unwrap_load_lattice
        (FOLDL (\ll i. load_transfer ctx i ll) initial (before ++ inst::p))) k = SOME [v])
Proof
  Induct_on `insts` using SNOC_INDUCT
  >- (simp[] >> rpt strip_tac >> disj1_tac >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  gvs[FOLDL_SNOC] >>
  drule le_transfer_lookup_origin >> strip_tac
  >- (first_x_assum drule >> strip_tac
      >- (disj1_tac >> rpt strip_tac >>
          drule le_prefix_snoc_cases >> strip_tac
          >- gvs[FOLDL_SNOC] >> metis_tac[]) >>
      disj2_tac >> qexistsl [`before`, `inst`, `SNOC x after`] >>
      simp[SNOC_APPEND] >> rpt strip_tac >>
      `SNOC x after = p ++ q` by simp[SNOC_APPEND] >>
      drule le_prefix_snoc_cases >> strip_tac
      >- (`before ++ inst::p = SNOC x insts` by
            (qpat_assum `p = SNOC x after` (fn th => pure_rewrite_tac[th]) >>
             qpat_assum `insts = _` (fn th => pure_rewrite_tac[th]) >>
             simp[NoAsms, SNOC_APPEND]) >>
          qpat_x_assum `before ++ inst::p = SNOC x insts`
            (fn th => pure_rewrite_tac[th, FOLDL_SNOC]) >>
          BETA_TAC >> first_assum ACCEPT_TAC) >>
      metis_tac[]) >>
  gvs[] >> disj2_tac >> qexistsl [`insts`, `x`, `[]`] >>
  simp[FOLDL_SNOC, FOLDL_APPEND]
QED

Theorem le_transfer_fold_empty_input:
  (initial = NONE \/ initial = SOME FEMPTY) /\
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) initial insts)) k = SOME vs ==>
  LENGTH vs <= 1
Proof
  rpt strip_tac >>
  (Cases_on `1 < LENGTH vs` >- (
    drule le_transfer_fold_multivalue_origin >> simp[] >>
    strip_tac >> gvs[unwrap_load_lattice_def]) >> simp[])
QED

(* A class is uniform in the input lattice, including NONE. *)
Definition le_fold_preserves_def:
  le_fold_preserves ctx insts k <=>
    !a. FLOOKUP (unwrap_load_lattice
      (FOLDL (\ll i. load_transfer ctx i ll) a insts)) k =
      FLOOKUP (unwrap_load_lattice a) k
End

Definition le_fold_deletes_def:
  le_fold_deletes ctx insts k <=>
    !a. FLOOKUP (unwrap_load_lattice
      (FOLDL (\ll i. load_transfer ctx i ll) a insts)) k = NONE
End

Definition le_fold_constant_def:
  le_fold_constant ctx insts k v <=>
    !a. FLOOKUP (unwrap_load_lattice
      (FOLDL (\ll i. load_transfer ctx i ll) a insts)) k = SOME [v]
End

Theorem le_invalidate_uniform_lookup[local]:
  (!ll. FLOOKUP (load_invalidate aliases bp space ll key) k = FLOOKUP ll k) \/
  (!ll. FLOOKUP (load_invalidate aliases bp space ll key) k = NONE)
Proof
  Cases_on `load_key_to_memloc bp space key = ml_undefined` >>
  simp[load_invalidate_def, FLOOKUP_DRESTRICT] >>
  Cases_on `load_key_to_memloc bp space k <> ml_undefined /\
    ~ma_may_alias aliases (load_key_to_memloc bp space k)
      (load_key_to_memloc bp space key)` >> simp[]
QED

Theorem le_transfer_uniform_lookup:
  (!a. FLOOKUP (unwrap_load_lattice (load_transfer ctx inst a)) k =
       FLOOKUP (unwrap_load_lattice a) k) \/
  (!a. FLOOKUP (unwrap_load_lattice (load_transfer ctx inst a)) k = NONE) \/
  (?v. !a. FLOOKUP (unwrap_load_lattice (load_transfer ctx inst a)) k = SOME [v])
Proof
  Cases_on `inst.inst_opcode = ctx.lctx_config.lc_load`
  >- (simp[load_transfer_def, unwrap_load_lattice_def] >>
      Cases_on `inst.inst_operands` >- simp[] >>
      Cases_on `t` >- (
        Cases_on `inst.inst_outputs` >- simp[] >>
        Cases_on `t` >> simp[FLOOKUP_UPDATE] >>
        Cases_on `load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
          (normalize_operand ctx.lctx_dfg []) inst = k` >> simp[]) >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = z::zs` >> Cases_on `zs` >> simp[]) >>
  Cases_on `ctx.lctx_config.lc_store` >>
  simp[load_transfer_def, unwrap_load_lattice_def] >>
  Cases_on `inst.inst_opcode = x` >> simp[]
  >- (Cases_on `inst.inst_operands` >- simp[] >>
      Cases_on `t` >- simp[] >>
      Cases_on `t'` >> simp[] >>
      simp[FLOOKUP_UPDATE] >>
      Cases_on `load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg []) inst = k` >- simp[] >>
      simp[] >> metis_tac[le_invalidate_uniform_lookup]) >>
  Cases_on `(case ctx.lctx_addr_space of
      AddrSp_Memory => Eff_MEMORY | AddrSp_Storage => Eff_STORAGE |
      AddrSp_Transient => Eff_TRANSIENT | _ => Eff_MEMORY)
        IN write_effects inst.inst_opcode` >> simp[]
QED

Theorem le_fold_lookup_classification:
  !insts. le_fold_preserves ctx insts k \/ le_fold_deletes ctx insts k \/
    ?v. le_fold_constant ctx insts k v
Proof
  Induct >- simp[le_fold_preserves_def] >> gen_tac >>
  fs[le_fold_preserves_def, le_fold_deletes_def, le_fold_constant_def] >>
  metis_tac[le_transfer_uniform_lookup]
QED

Theorem le_fold_preserves_lookup:
  le_fold_preserves ctx insts k ==>
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) a insts)) k =
  FLOOKUP (unwrap_load_lattice a) k
Proof
  simp[le_fold_preserves_def]
QED

Theorem le_fold_deletes_lookup:
  le_fold_deletes ctx insts k ==>
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) a insts)) k = NONE
Proof
  simp[le_fold_deletes_def]
QED

Theorem le_fold_constant_lookup:
  le_fold_constant ctx insts k v ==>
  FLOOKUP (unwrap_load_lattice
    (FOLDL (\ll i. load_transfer ctx i ll) a insts)) k = SOME [v]
Proof
  simp[le_fold_constant_def]
QED

(* Original-cut frames for concat's scratch allocation and operand phases. *)
Theory bodyMemBiConcatPost
Ancestors
  protectedAllocationFrame exprSimProps exprSimWordArgs exprLoweringProps
  loweringPosts compileEnv venomState finite_map list arithmetic
  exprSimConcatResult exprSimAlloc exprSimHash exprSimMemDefs
  concatMemory exprSimConcatPath freshWrites valueEncodingProps
  emitHelperProps venomMemProps context

Theorem concat_prefix_frame:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
           FLOOKUP t.vs_allocas aid = SOME a) /\
  (!aid p n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
             w2n ow + 64 <= p \/ p+n <= w2n ow) /\
  (!name p n. local_region cenv es.scopes t name p n ==>
              w2n ow + 64 <= p \/ p+n <= w2n ow) /\
  (!p n. p+n <= w2n ow \/ w2n ow+64 <= p ==>
         mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) ==>
  wb_frame cenv es sa s0 t
Proof
  strip_tac >>
  `locals_kept cenv es s0 t` by
    (irule locals_kept_regions >> rpt strip_tac >>
     `local_region cenv es.scopes t n b sz` by
       (irule local_region_frame_fwd >> qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >>
     qpat_x_assum `!p n. _ \/ _ ==> mem_bytes_at p n t.vs_memory = _` irule >>
     metis_tac[]) >>
  simp[wb_frame_def] >> rpt strip_tac >>
  qpat_x_assum `!p n. _ \/ _ ==> mem_bytes_at p n t.vs_memory = _` irule >>
  metis_tac[]
QED

Theorem concat_prefix_list_frame:
  wb_frame cenv es sa s0 t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= sc.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var /\
  (!z w. not_fresh_at sc z /\ lookup_var z t = SOME w ==>
         lookup_var z u = SOME w) /\
  (!aid a. FLOOKUP t.vs_allocas aid = SOME a ==>
           FLOOKUP u.vs_allocas aid = SOME a) /\
  locals_kept cenv ee t u /\
  (!aid p n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
     (B+bsz <= p \/ p+n <= B) /\ (w2n ow+64 <= p \/ p+n <= w2n ow)) /\
  (!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ aid < sc.cs_next_id /\
     (p+n <= B \/ B+bsz <= p) /\ (p+n <= w2n ow \/ w2n ow+64 <= p) /\
     (!name lo sz. local_region cenv ee.scopes t name lo sz ==>
                   p+n <= lo \/ lo+sz <= p) ==>
     mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory) ==>
  wb_frame cenv es sa s0 u
Proof
  strip_tac >> irule protected_allocation_frame_tail >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
  qexistsl_tac [`\p n. (p+n <= B \/ B+bsz <= p) /\
                       (p+n <= w2n ow \/ w2n ow+64 <= p)`,
                `ee`, `sc`, `t`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (qpat_x_assum `!aid p n. aid < sa.cs_next_id /\ _ ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* The suffix changes one fresh register and the result's length word. *)
Theorem concat_suffix_frame[local]:
  wb_frame cenv es sa s0 t /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x. not_fresh_at sa x ==> x <> fresh) /\
  (!aid p n. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
     B+32 <= p \/ p+n <= B) /\
  (!name p n. local_region cenv ee.scopes t name p n ==>
     B+32 <= p \/ p+n <= B) ==>
  wb_frame cenv es sa s0
    (mstore B w (update_var fresh w t))
Proof
  strip_tac >> irule wb_frame_allocating_tail >> simp[] >>
  qexistsl_tac [`t`, `ee.scopes`, `sa`] >>
  simp[mstore_def, update_var_def, lookup_var_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`b`, `sz`, `B`, `w`, `t`]
        mstore_mem_bytes_at_disjoint) >>
      impl_tac >- metis_tac[] >> simp[mstore_def])
  >- (rpt strip_tac >> `x <> fresh` by metis_tac[] >> simp[FLOOKUP_UPDATE]) >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`b`, `sz`, `B`, `w`, `t`]
    mstore_mem_bytes_at_disjoint) >>
  impl_tac >- metis_tac[] >> simp[mstore_def]
QED

Theorem concat_suffix_value[local]:
  (!off mem. val_in_memory tv v off mem <=>
     mem_word_at off mem = n2w (LENGTH bytes) /\
     mem_bytes_at (off+32) (LENGTH bytes) mem = bytes) /\
  w = n2w (LENGTH bytes) /\
  mem_bytes_at (B+32) (LENGTH bytes) t.vs_memory = bytes ==>
  val_in_memory tv v B
    (mstore B w (update_var fresh w t)).vs_memory
Proof
  strip_tac >> gvs[] >> conj_tac
  >- simp[mem_word_at_eq_mload, mload_def, mstore_def, update_var_def,
          GSYM mload_def, mload_mstore_same] >>
  `mem_bytes_at (B+32) (LENGTH bytes)
     (mstore B (n2w (LENGTH bytes)) t).vs_memory =
   mem_bytes_at (B+32) (LENGTH bytes) t.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  fs[mstore_def, update_var_def]
QED

Theorem concat_suffix_state[local]:
  stmt_state_rel ctx func cenv cx ee t /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> x <> fresh) /\
  not_local_ptr cenv ee.scopes fresh /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (B,bsz) /\ 32 <= bsz /\
  (!name p n. local_region cenv ee.scopes t name p n ==>
     B+bsz <= p \/ p+n <= B) ==>
  stmt_state_rel ctx func cenv cx ee
    (mstore B w (update_var fresh w t))
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  irule literal_mstore_state_rel >>
  reverse conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  qexistsl_tac [`B`, `inst`, `bsz`] >> simp[update_var_def] >>
  rpt strip_tac >> first_x_assum irule >>
  mp_tac (Q.SPECL [`cenv`, `sa`, `ee.scopes`, `t`,
    `update_var fresh w t`, `name`, `lb`, `lsz`] concat_local_region_vars) >>
  impl_tac
  >- (simp[lookup_var_update_var] >> rpt strip_tac >> metis_tac[]) >>
  simp[update_var_def] >> metis_tac[]
QED

Theorem concat_suffix_post:
  post_value_type cenv e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ val_wf tv v /\
  val_footprint tv v = 32 + LENGTH bytes /\
  (!off mem. val_in_memory tv v off mem <=>
     mem_word_at off mem = n2w (LENGTH bytes) /\
     mem_bytes_at (off+32) (LENGTH bytes) mem = bytes) /\
  mload (w2n ow) t = n2w (LENGTH bytes) /\
  mem_bytes_at (B+32) (LENGTH bytes) t.vs_memory = bytes /\
  32 + LENGTH bytes <= bsz /\ B < dimword (:256) /\
  val_store_size tv v <= bsz /\
  (!ltv. evaluate_type (get_tenv cx) lt = SOME ltv ==>
         type_memory_size ltv <= bsz) /\ B+bsz <= t.vs_alloca_next /\
  lookup_var bv t = SOME (n2w B) /\ bv <> fresh /\
  wb_frame cenv es sa s0 t /\ stmt_state_rel ctx func cenv cx ee t /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x. not_fresh_at sa x ==> x <> fresh) /\
  not_local_ptr cenv ee.scopes fresh /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (B,bsz) /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  (!aid p n. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
     B+32 <= p \/ p+n <= B) /\
  (!name p n. local_region cenv ee.scopes t name p n ==>
     B+bsz <= p \/ p+n <= B) ==>
  let u = (mstore B (mload (w2n ow) t)
             (update_var fresh (mload (w2n ow) t) t)) with vs_inst_idx := k in
  vv_post ctx func cenv cx e es sa sb s0 ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var bv) LocMemory)) u /\
  vv_store_bound cx (expr_type e) lt ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr (Var bv) LocMemory)) u
Proof
  strip_tac >> simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `vv_post _ _ _ _ _ _ _ _ _ _ _ _ u` >>
  `32 <= bsz` by decide_tac >>
  `wb_frame cenv es sa s0 u` by
    (simp[Abbr `u`] >> irule concat_suffix_frame >>
     asm_rewrite_tac[] >> qexists_tac `ee` >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!name p n. local_region _ _ _ _ _ _ ==> _` drule >>
     decide_tac) >>
  `stmt_state_rel ctx func cenv cx ee u` by
    (simp[Abbr `u`] >> irule concat_suffix_state >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`bsz`, `inst`] >> asm_rewrite_tac[] >>
         rpt strip_tac >>
         qpat_x_assum `!name p n. local_region _ _ _ _ _ _ ==> _` drule >>
         decide_tac)
     >> qexists_tac `sa` >> asm_rewrite_tac[] >> metis_tac[]) >>
  `lookup_var bv u = SOME (n2w B)` by
    simp[Abbr `u`, mstore_def, lookup_var_update_var] >>
  `!name p n. local_region cenv ee.scopes u name p n ==>
     B+bsz <= p \/ p+n <= B` by
    (rpt strip_tac >> first_x_assum irule >>
     mp_tac (Q.SPECL [`cenv`, `sa`, `ee.scopes`, `t`, `u`, `name`, `p`, `n`]
       concat_local_region_vars) >> impl_tac
     >- (simp[Abbr `u`, mstore_def, lookup_var_update_var] >>
         rpt strip_tac >> metis_tac[]) >> metis_tac[]) >>
  `val_in_memory tv v B u.vs_memory` by
    (qpat_assum `Abbrev (u = _)`
       (fn th => pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     irule concat_suffix_value >> qexists_tac `bytes` >> simp[]) >>
  conj_asm1_tac
  >- (irule vv_post_allocated_memory_intro >>
      simp[mk_ptr_def, eval_operand_def] >>
      qexistsl_tac [`inst.inst_id`, `B`, `bsz`] >>
      asm_rewrite_tac[] >> conj_tac >- decide_tac >>
      simp[Abbr `u`, mstore_def, update_var_def]) >>
  simp[vv_store_bound_def, mk_ptr_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def, eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      simp[Abbr `u`, mstore_def, update_var_def] >> decide_tac) >>
  rpt strip_tac >>
  `type_memory_size tvt <= bsz` by metis_tac[] >>
  simp[Abbr `u`, mstore_def, update_var_def] >> decide_tac
QED

(* Original-cut frames for concat's scratch allocation and operand phases. *)
Theory bodyMemBiConcatPost
Ancestors
  protectedAllocationFrame exprSimProps exprSimWordArgs exprLoweringProps
  loweringPosts compileEnv venomState finite_map list arithmetic

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

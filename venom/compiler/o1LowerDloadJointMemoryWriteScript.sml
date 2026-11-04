(* Masked writes under occurrence geometry, including empty protected sites. *)
Theory o1LowerDloadJointMemoryWrite
Ancestors
  o1LowerDloadJointRelation o1LowerDloadMemoryConsumer
  o1LowerDloadRelocationKernel ptrDiscipline venomState words finite_map pred_set codegenRel

Theorem ld_memory_agree_mstore_geometry:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\ word_agree_except m v w /\
  ((a = c /\ a+32 <= lo) \/
   (?id b d z j. FLOOKUP sites id = SOME (b,d,z) /\ j+32 <= z /\
     a = b+j /\ c = d+j)) ==>
  ld_memory_agree sites lo
    ((mask DIFF {i | a <= i /\ i < a+32}) UNION {a+k | k IN m})
    (mstore a v s).vs_memory (mstore c w t).vs_memory
Proof
  strip_tac
  >- (gvs[] >> rewrite_tac[ld_memory_agree_def] >> conj_tac
      >- (rpt strip_tac >> simp[ld_mstore_bytes] >>
          Cases_on `a <= i /\ i < a+32`
          >- (`i-a NOTIN m` by (gvs[] >> metis_tac[arithmeticTheory.SUB_ADD]) >>
              gvs[word_agree_except_def]) >>
          simp[] >> irule ld_memory_agree_fixed_byte >>
          qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[]) >>
      rpt strip_tac >>
      `lo <= b /\ lo <= c` by metis_tac[ld_joint_geometry_def] >>
      `~(a <= b+j /\ b+j < a+32) /\
       ~(a <= c+j /\ c+j < a+32)` by decide_tac >>
      asm_rewrite_tac[ld_mstore_bytes] >>
      irule ld_memory_agree_site_byte >>
      qexistsl_tac [`id`,`lo`,`mask`,`sites`,`z`] >> gvs[]) >>
  gvs[] >>
  `lo <= b /\ lo <= d` by metis_tac[ld_joint_geometry_def] >>
  rewrite_tac[ld_memory_agree_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(b+j <= i /\ i < b+j+32) /\
       ~(d+j <= i /\ i < d+j+32)` by decide_tac >>
      asm_rewrite_tac[ld_mstore_bytes] >>
      irule ld_memory_agree_fixed_byte >>
      qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[]) >>
  rpt strip_tac >>
  rename1 `read_byte (sb+k) (mstore (b+j) v s).vs_memory =
    read_byte (tb+k) (mstore (d+j) w t).vs_memory` >>
  rename1 `FLOOKUP sites jd = SOME (sb,tb,sz)` >>
  Cases_on `jd = id`
  >- (gnvs[] >>
      Cases_on `j <= k /\ k < j+32`
      >- (`k = j+(k-j)` by decide_tac >>
          `k-j NOTIN m` by (gvs[] >> metis_tac[]) >>
          qpat_x_assum `word_agree_except _ _ _` mp_tac >>
          simp[word_agree_except_def] >>
          disch_then (qspec_then `k-j` mp_tac) >> simp[ld_mstore_bytes]) >>
      gvs[ld_mstore_bytes] >>
      `k < sz` by decide_tac >>
      fs[ld_memory_agree_def] >> metis_tac[]) >>
  `0 < z /\ 0 < sz` by decide_tac >>
  `(sb+sz <= b \/ b+z <= sb) /\ (tb+sz <= d \/ d+z <= tb)` by
    (qpat_x_assum `ld_joint_geometry _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ld_joint_geometry_def]) >>
     metis_tac[]) >>
  `~(b+j <= sb+k /\ sb+k < b+j+32) /\
   ~(d+j <= tb+k /\ tb+k < d+j+32)` by decide_tac >>
  asm_rewrite_tac[ld_mstore_bytes] >> irule ld_memory_agree_site_byte >>
  qexistsl_tac [`jd`,`lo`,`mask`,`sites`,`sz`] >> gvs[]
QED

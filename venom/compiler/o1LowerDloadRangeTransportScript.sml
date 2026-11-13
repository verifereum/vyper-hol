(* Source-indexed byte range transport, including padded and empty reads. *)
Theory o1LowerDloadRangeTransport
Ancestors
  o1LowerDloadRelocationKernel o1LowerDloadJointGeometry o1LowerDloadJointRelation
  regularCallEmitSim venomState codegenRel list rich_list arithmetic pred_set finite_map

Theorem ld_read_memory_length:
  LENGTH (read_memory p len s) = len
Proof
  simp[read_memory_def, LENGTH_TAKE_EQ]
QED

Theorem ld_read_memory_element:
  k < len ==> EL k (read_memory p len s) = read_byte (p+k) s.vs_memory
Proof
  strip_tac >> simp[read_memory_def, EL_TAKE, EL_APPEND_EQN, EL_DROP,
                   EL_REPLICATE, read_byte_def] >>
  Cases_on `p+k < LENGTH s.vs_memory` >> simp[] >> decide_tac
QED

Theorem ld_memory_agree_slice_element:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ((p=q /\ p+len<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                 p=b+j /\ q=c+j)) /\
  k<len /\ p+k NOTIN mask ==>
  EL k (read_memory p len s) = EL k (read_memory q len t)
Proof
  strip_tac >> simp[ld_read_memory_element] >-
    (irule ld_memory_agree_fixed_byte >>
     qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[ADD_COMM] >> decide_tac) >>
  `j+k < z` by decide_tac >>
  `b+(j+k) NOTIN mask` by
    (qpat_x_assum `p+k NOTIN mask` mp_tac >>
     pure_asm_rewrite_tac[ADD_ASSOC] >> simp[]) >>
  metis_tac[ld_memory_agree_site_byte]
QED

Theorem ld_memory_agree_empty_write:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory ==>
  ld_memory_agree sites lo mask
    (write_memory_with_expansion p [] s).vs_memory
    (write_memory_with_expansion q [] t).vs_memory
Proof
  simp[ld_memory_agree_def, read_byte_write_memory_with_expansion] >> metis_tac[]
QED

Theorem ld_memory_agree_write_geometry:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\
  LENGTH xs = len /\ LENGTH ys = len /\
  (!k. k<len /\ k NOTIN payload_mask ==> EL k xs = EL k ys) /\
  ((p=q /\ p+len<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                 p=b+j /\ q=c+j)) ==>
  ld_memory_agree sites lo
    ((mask DIFF {i | p<=i /\ i<p+len}) UNION
      {p+k | k<len /\ k IN payload_mask})
    (write_memory_with_expansion p xs s).vs_memory
    (write_memory_with_expansion q ys t).vs_memory
Proof
  strip_tac
  >- (gvs[] >> rewrite_tac[ld_memory_agree_def] >> conj_tac
      >- (rpt strip_tac >> simp[read_byte_write_memory_with_expansion] >>
          Cases_on `p<=i /\ i<p+LENGTH xs`
          >- (`i-p<LENGTH xs /\ i-p NOTIN payload_mask` by
                (gvs[] >> metis_tac[arithmeticTheory.SUB_ADD]) >> simp[]) >>
          simp[] >> irule ld_memory_agree_fixed_byte >>
          qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[]) >>
      rpt strip_tac >>
      `lo<=b /\ lo<=c` by metis_tac[ld_joint_geometry_def] >>
      `~(p<=b+j /\ b+j<p+LENGTH xs) /\ ~(p<=c+j /\ c+j<p+LENGTH xs)` by decide_tac >>
      asm_rewrite_tac[read_byte_write_memory_with_expansion] >>
      irule ld_memory_agree_site_byte >>
      qexistsl_tac [`id`,`lo`,`mask`,`sites`,`z`] >> gvs[]) >>
  gvs[] >>
  `lo<=b /\ lo<=c` by metis_tac[ld_joint_geometry_def] >>
  rewrite_tac[ld_memory_agree_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(b+j<=i /\ i<b+j+LENGTH xs) /\ ~(c+j<=i /\ i<c+j+LENGTH xs)` by decide_tac >>
      asm_rewrite_tac[read_byte_write_memory_with_expansion] >>
      irule ld_memory_agree_fixed_byte >>
      qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[]) >>
  rpt strip_tac >>
  rename1 `FLOOKUP sites jd = SOME (sb,tb,sz)` >>
  rename1 `read_byte (sb+k) _ = read_byte (tb+k) _` >>
  Cases_on `jd=id`
  >- (gnvs[] >> Cases_on `j<=k /\ k<j+LENGTH xs`
      >- (`k-j<LENGTH xs /\ k-j NOTIN payload_mask` by
            (gvs[] >> metis_tac[arithmeticTheory.SUB_ADD]) >>
          simp[read_byte_write_memory_with_expansion]) >>
      gvs[read_byte_write_memory_with_expansion] >>
      `k<sz` by decide_tac >>
      fs[ld_memory_agree_def] >> metis_tac[]) >>
  Cases_on `LENGTH xs=0`
  >- (gvs[read_byte_write_memory_with_expansion] >>
      fs[ld_memory_agree_def] >> metis_tac[ADD_COMM]) >>
  `0<z /\ 0<sz` by decide_tac >>
  `(sb+sz<=b \/ b+z<=sb) /\ (tb+sz<=c \/ c+z<=tb)` by
    (qpat_x_assum `ld_joint_geometry _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ld_joint_geometry_def]) >> metis_tac[]) >>
  `~(b+j<=sb+k /\ sb+k<b+j+LENGTH xs) /\
   ~(c+j<=tb+k /\ tb+k<c+j+LENGTH xs)` by decide_tac >>
  asm_rewrite_tac[read_byte_write_memory_with_expansion] >>
  irule ld_memory_agree_site_byte >>
  qexistsl_tac [`jd`,`lo`,`mask`,`sites`,`sz`] >> gvs[]
QED

Theorem ld_memory_agree_clean_write:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\
  ((p=q /\ p+LENGTH xs<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+LENGTH xs<=z /\
                 p=b+j /\ q=c+j)) ==>
  ld_memory_agree sites lo (mask DIFF {i | p<=i /\ i<p+LENGTH xs})
    (write_memory_with_expansion p xs s).vs_memory
    (write_memory_with_expansion q xs t).vs_memory
Proof
  strip_tac >>
  `mask DIFF {i | p<=i /\ i<p+LENGTH xs} =
    (mask DIFF {i | p<=i /\ i<p+LENGTH xs}) UNION
      {p+k | k<LENGTH xs /\ k IN {}}` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_write_geometry >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Theorem ld_memory_agree_snapshot_copy:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\
  ((rp=rq /\ rp+len<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                 rp=b+j /\ rq=c+j)) /\
  ((p=q /\ p+len<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                 p=b+j /\ q=c+j)) ==>
  ld_memory_agree sites lo
    ((mask DIFF {i | p<=i /\ i<p+len}) UNION
      {p+k | k<len /\ rp+k IN mask})
    (write_memory_with_expansion p (read_memory rp len s) s).vs_memory
    (write_memory_with_expansion q (read_memory rq len t) t).vs_memory
Proof
  strip_tac >>
  `!k. k<len /\ rp+k NOTIN mask ==>
    EL k (read_memory rp len s) = EL k (read_memory rq len t)` by
    (rpt strip_tac >> irule ld_memory_agree_slice_element >> metis_tac[]) >>
  `{p+k | k<len /\ rp+k IN mask} =
   {p+k | k<len /\ k IN {k | rp+k IN mask}}` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_write_geometry >>
  disch_then irule >>
  simp[ld_read_memory_length] >> metis_tac[ADD_COMM]
QED

(* Checked padding/empty edge cases; the copy theorem above has no
   non-overlap premise and the write theorem separates distinct sites. *)
Theorem ld_read_memory_padding_probe[local]:
  read_memory 1 4 (s with vs_memory := [7w;8w]) = [8w;0w;0w;0w] /\
  read_memory 100 0 s = []
Proof
  simp[read_memory_def] >> EVAL_TAC
QED

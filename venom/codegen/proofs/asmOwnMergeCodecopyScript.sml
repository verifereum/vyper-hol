(* CODECOPY with fixed own bytes preserves the existing rename relation. *)
Theory asmOwnMergeCodecopy
Ancestors
  asmOptMergeJumpdests asmSymOwnCode asmSymSem asmSem list rich_list

Theorem codecopy_rel_own:
  rn_rel x y ss ss' /\ ~sym_data_label p env x ==>
  res_rel x y (sym_codecopy_own p env own ss)
              (sym_codecopy_own p env own ss')
Proof
  strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack /\
   ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  Cases_on `?dst l d sz stk.
              ss.sym_stack = Val dst :: Lab l d :: Val sz :: stk`
  >- (gvs[] >> gvs[LIST_REL_CONS1, sv_rel_val] >>
      simp[sym_codecopy_own_def] >>
      gvs[sv_rel_def] >> rw[res_rel_def] >> gvs[] >>
      irule lift_rel >> fs[rn_rel_def] >>
      simp[ml_rel_clear, blocks_clear]) >>
  Cases_on `?dst src sz stk.
              ss.sym_stack = Val dst :: Val src :: Val sz :: stk`
  >- (gvs[] >> gvs[LIST_REL_CONS1, sv_rel_val] >>
      simp[sym_codecopy_own_def] >>
      irule lift_rel >> fs[rn_rel_def] >>
      simp[ml_rel_clear, blocks_clear]) >>
  `?e. sym_codecopy_own p env own ss = SymError e \/
       sym_codecopy_own p env own ss = SymBad e`
    by (simp[sym_codecopy_own_def] >>
        Cases_on `ss.sym_stack` >> simp[] >>
        rename1 `ss.sym_stack = v1 :: t1` >> Cases_on `t1` >> simp[] >>
        rename1 `ss.sym_stack = v1 :: v2 :: t2` >>
        Cases_on `t2` >> Cases_on `v1` >> Cases_on `v2` >> simp[] >>
        rename1 `ss.sym_stack = _ :: _ :: v3 :: _` >>
        Cases_on `v3` >> gvs[]) >>
  gvs[res_rel_def]
QED

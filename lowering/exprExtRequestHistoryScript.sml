(* Accumulated frames relative to a fixed captured producer endpoint. *)
Theory exprExtRequestHistory
Ancestors
  exprExtRequestReadProbe exprExtRequestImmutableFrame exprSimProps
  loweringPosts exprLoweringProps compileEnv

Definition extrequest_history_frame_def:
  extrequest_history_frame cenv cx ec sc tc ee sn t <=>
    extrequest_read_frame cx ec ee /\
    sc.cs_next_var <= sn.cs_next_var /\ sc.cs_next_id <= sn.cs_next_id /\
    local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sn /\
    (!x w. not_fresh_at sc x /\ lookup_var x tc = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP tc.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!n b sz. local_region cenv ec.scopes tc n b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz tc.vs_memory) /\
    (!aid b sz. FLOOKUP tc.vs_allocas aid = SOME (b,sz) /\
       aid < sc.cs_next_id /\
       (!n lb lsz. local_region cenv ec.scopes tc n lb lsz ==>
          compileEnv$regions_disjoint b sz lb lsz) ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz tc.vs_memory) /\
    (cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ec.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables cenv.ce_module imms)
         name = SOME (tv,v) ==>
       mem_bytes_at off (type_memory_size tv) t.vs_memory =
         mem_bytes_at off (type_memory_size tv) tc.vs_memory)
End

Theorem extrequest_history_frame_refl:
  local_ptrs_reserved cenv sc ==>
  extrequest_history_frame cenv cx ec sc tc ec sc tc
Proof
  simp[extrequest_history_frame_def, extrequest_read_frame_def]
QED

Theorem extrequest_history_local_regions:
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ec tc ==>
  (local_region cenv ec.scopes tc n b sz <=>
   local_region cenv ee.scopes t n b sz)
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (irule local_region_frame_fwd >>
      gvs[extrequest_history_frame_def, extrequest_read_frame_def] >>
      qexistsl_tac [`tc`, `sc`, `ee.scopes`] >> simp[]) >>
  irule local_region_frame >>
  gvs[extrequest_history_frame_def, extrequest_read_frame_def,
      stmt_state_rel_def] >>
  conj_tac
  >- (qexists_tac `func` >> gvs[state_rel_def]) >>
  qexistsl_tac [`sc`, `ee.scopes`, `t`] >> simp[]
QED

Theorem extrequest_history_frame_extend:
  extrequest_history_frame cenv cx ec sc tc ee sm t /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee t /\
  vv_post ctx func cenv cx e ee sm sn t ee' r vv t' /\
  extrequest_read_frame cx ee ee' /\
  local_ptrs_reserved cenv sn /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!n b sz. local_region cenv ee.scopes t n b sz ==>
     mem_bytes_at b sz t'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!off len.
     (!inst b sz.
        MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint off len b sz) ==>
     mem_bytes_at off len t'.vs_memory = mem_bytes_at off len t.vs_memory) ==>
  extrequest_history_frame cenv cx ec sc tc ee' sn t'
Proof
  strip_tac >> rewrite_tac[extrequest_history_frame_def] >>
  rpt conj_tac
  >- suspend "source"
  >- (gvs[extrequest_history_frame_def])
  >- (gvs[extrequest_history_frame_def])
  >- (gvs[extrequest_history_frame_def])
  >- simp[]
  >- suspend "vars"
  >- suspend "allocas"
  >- suspend "locals"
  >- suspend "bytes"
  >> suspend "immutables"
QED

Resume extrequest_history_frame_extend[source]:
  gvs[extrequest_history_frame_def, extrequest_read_frame_def]
QED

Resume extrequest_history_frame_extend[vars]:
  rpt strip_tac >>
  `not_fresh_at sm x` by
    (gvs[extrequest_history_frame_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `lookup_var x t = SOME w` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  gvs[vv_post_def] >> metis_tac[]
QED

Resume extrequest_history_frame_extend[allocas]:
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME b` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  gvs[vv_post_def] >> metis_tac[]
QED

Resume extrequest_history_frame_extend[locals]:
  rpt strip_tac >>
  `local_region cenv ee.scopes t n b sz` by
    (drule_all extrequest_history_local_regions >> metis_tac[]) >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz tc.vs_memory` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  metis_tac[]
QED

Resume extrequest_history_frame_extend[bytes]:
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  `aid < sm.cs_next_id` by (gvs[extrequest_history_frame_def]) >>
  `!n lb lsz. local_region cenv ee.scopes t n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b` by
    (rpt strip_tac >>
     `local_region cenv ec.scopes tc n lb lsz` by
       (drule_all extrequest_history_local_regions >> metis_tac[]) >>
     gvs[regions_disjoint_def] >> metis_tac[]) >>
  `mem_bytes_at b sz t'.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (gvs[vv_post_def] >> metis_tac[]) >>
  gvs[extrequest_history_frame_def] >> metis_tac[]
QED

Resume extrequest_history_frame_extend[immutables]:
  rpt strip_tac >>
  `ALOOKUP ec.immutables cx.txn.target = ALOOKUP ee'.immutables cx.txn.target` by
    gvs[extrequest_history_frame_def, extrequest_read_frame_def] >>
  `immutable_alloca_sep func cenv cx ee' t'` by
    gvs[vv_post_def, stmt_state_rel_def] >>
  `mem_bytes_at off (type_memory_size tv) t'.vs_memory =
     mem_bytes_at off (type_memory_size tv) t.vs_memory` by
    (gvs[] >> drule_all extrequest_immutable_memory_kept >> simp[]) >>
  gvs[extrequest_history_frame_def] >> metis_tac[]
QED

Finalise extrequest_history_frame_extend

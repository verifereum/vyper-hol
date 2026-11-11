(* Transport the entry-expression frame across allocation-backed scratch writes. *)
Theory extcallReturnPostFrame
Ancestors
  extcallReturnFrame abiCallerAllocation abiCallerLocalScratch abiDecoderFrame
  exprSimProps loweringPosts compileEnv valueEncodingProps venomState
  finite_map pred_set list arithmetic

Theorem extcall_return_scratch_wb_frame:
  wb_frame ce es sa s0 s /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM scopes /\
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce scopes s /\
  FINITE ids /\ s.vs_alloca_next <= b + cap /\
  (!id. id IN ids ==> sa.cs_next_id <= id) /\
  (!id off len. id IN ids /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q) /\
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) ==>
  wb_frame ce es sa s0 t
Proof
  strip_tac >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz s.vs_memory` by
    (rpt strip_tac >> irule abi_caller_local_scratch_frame >>
     simp[] >> qexistsl_tac [`b`, `cap`] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ce`, `func`, `name`, `scopes`] >> simp[] >>
     irule local_region_frame_fwd >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `sa` >> fs[wb_frame_def]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (fs[wb_frame_def] >> metis_tac[])
  >- (fs[wb_frame_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by
        (fs[wb_frame_def] >> metis_tac[]) >>
      `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by
        (irule abi_caller_allocation_frame >>
         goal_assum (drule_at Any) >> simp[] >>
         qexistsl_tac [`b`, `cap`, `ids`, `sz`, `aid`, `off`] >> simp[] >>
         metis_tac[LESS_NOT_SUC, LESS_EQ_ANTISYM, NOT_LESS]) >>
      fs[wb_frame_def] >> metis_tac[]) >>
  fs[wb_frame_def, locals_kept_def] >> rpt strip_tac >>
  `mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (`mem_bytes_at b' sz t.vs_memory = mem_bytes_at b' sz s.vs_memory` by
       metis_tac[] >>
     drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`off - b'`, `len`] mp_tac) >> simp[]) >>
  metis_tac[]
QED

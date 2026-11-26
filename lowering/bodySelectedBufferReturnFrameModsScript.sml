(* Recover the linked immutable frame after a typed return-buffer copy. *)
Theory bodySelectedBufferReturnFrameMods
Ancestors
  bodyFullPostsMods bodyInvSplit loweringSlice exprLoweringProps
  allocationGrowth compileEnv loweringStateRelDefs vyperState
  finite_map alist list pair

(* A buffered return may change memory and allocate fresh result temporaries,
   but its writes are outside the immutable regions and old local regions are
   either retained or newly allocated above the old frontier. *)
Theorem selected_buffer_return_frame_mods:
  immutable_frame_mods func ce cx ee t /\
  allocation_growth t u /\
  u.vs_data_section = t.vs_data_section /\
  LENGTH t.vs_memory <= LENGTH u.vs_memory /\
  (!src tops name tv v off.
     ALOOKUP ce.ce_modules src = SOME tops /\
     ce.ce_is_ctor /\
     FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name =
       SOME (tv,v) ==>
     mem_bytes_at off (type_memory_size tv) u.vs_memory =
       mem_bytes_at off (type_memory_size tv) t.vs_memory) /\
  (!src tops aid b sz.
     ALOOKUP ce.ce_modules src = SOME tops /\
     FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP t.vs_allocas aid = SOME (b,sz) \/
       t.vs_alloca_next <= b) /\
  (!src tops id b sz.
     ALOOKUP ce.ce_modules src = SOME tops /\
     local_region (ce with ce_module := src) ee.scopes u id b sz ==>
       (?id0. local_region (ce with ce_module := src) ee.scopes t id0 b sz) \/
       (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
               FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz)) \/
       t.vs_alloca_next <= b) ==>
  immutable_frame_mods func ce cx ee u
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      metis_tac[immutables_rel_mem_agree])
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum
        `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> _`
        (qspecl_then [`src`, `tops`] drule) >>
      disch_tac >>
      match_mp_tac (Q.SPECL
        [`func`, `(ce with ce_module := src)`, `cx`, `ee`, `ee`, `t`, `u`]
        immutable_alloca_sep_frame) >>
      conj_tac
      >- simp[]
      >- (conj_tac
          >- simp[]
          >- (conj_tac
              >- (drule_all allocation_growth_next >> simp[])
              >- (conj_tac
                  >- (rpt strip_tac >>
                      qpat_assum `!src tops aid b sz. _ /\\ _ ==> _`
                        drule_all >> simp[])
                  >- (rpt strip_tac >>
                      qpat_assum `!src tops id b sz. _ /\\ _ ==> _`
                        drule_all >> simp[])))))
QED

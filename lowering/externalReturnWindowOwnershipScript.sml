(* A source window is backed by a registered allocation or a borrowed
   region below the frontier and clear of the frame's allocations. *)
Theory externalReturnWindowOwnership
Ancestors
  externalReturnWindowResource loweringReturnWindow allocaSiteResource
  finite_map arithmetic

Definition return_window_ownership_def:
  return_window_ownership func op ei msz nkey ut iv st x sf sb cap s <=>
  ?owner loff capacity.
    loff <= sb /\ sb + cap <= loff + capacity /\
    (case owner of
       SOME aid => FLOOKUP s.vs_allocas aid = SOME (loff,capacity)
     | NONE => loff + capacity <= s.vs_alloca_next /\
         !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
           venomMemDefs$regions_disjoint (loff,capacity) (b,sz)) /\
    (!st1 buf sa len se.
      compile_external_return (SOME op) F F ei msz F nkey ut iv st1 = (x,sf) /\
      st1.cs_next_var = st.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
      compile_alloc_buffer msz st1 = (buf,sa) /\
      compile_abi_encode_to_buf buf.buf_operand op ei sa = (len,se) /\
      emit_inst RETURN [buf.buf_operand;len] [] se = (x,sf) ==>
      owner <> SOME st1.cs_next_id /\
      (!b sz. FLOOKUP s.vs_allocas st1.cs_next_id = SOME (b,sz) ==> sz = msz) /\
      (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id IN frag_ids sa se ==> owner <> SOME inst.inst_id) /\
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id IN frag_ids sa se /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32))
End

Theorem return_window_optional_owner_below:
  alloca_inv s /\ loff <= sb /\ sb + cap <= loff + capacity /\
  (case owner of
     SOME aid => FLOOKUP s.vs_allocas aid = SOME (loff,capacity)
   | NONE => loff + capacity <= s.vs_alloca_next /\
       !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
         venomMemDefs$regions_disjoint (loff,capacity) (b,sz)) ==>
  sb + cap <= s.vs_alloca_next
Proof
  Cases_on `owner`
  >- (simp[] >> decide_tac) >>
  simp[] >> strip_tac >>
  drule_all alloca_site_registered_below >> decide_tac
QED

Theorem return_window_optional_owner_separate:
  alloca_inv s /\ loff <= sb /\ sb + cap <= loff + capacity /\
  (case owner of
     SOME aid => FLOOKUP s.vs_allocas aid = SOME (loff,capacity)
   | NONE => loff + capacity <= s.vs_alloca_next /\
       !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
         venomMemDefs$regions_disjoint (loff,capacity) (b,sz)) /\
  owner <> SOME site /\ FLOOKUP s.vs_allocas site = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (sb,cap) (b,sz)
Proof
  Cases_on `owner` >> simp[] >> strip_tac
  >- (first_x_assum drule >>
      simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule return_window_owned_separate >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem return_window_ownership_resources:
  alloca_inv s /\
  return_window_ownership func op ei msz nkey ut iv st x sf sb cap s ==>
  sb + cap <= s.vs_alloca_next /\
  (!st1 buf sa len se.
    compile_external_return (SOME op) F F ei msz F nkey ut iv st1 = (x,sf) /\
    st1.cs_next_var = st.cs_next_var /\ st.cs_next_id <= st1.cs_next_id /\
    compile_alloc_buffer msz st1 = (buf,sa) /\
    compile_abi_encode_to_buf buf.buf_operand op ei sa = (len,se) /\
    emit_inst RETURN [buf.buf_operand;len] [] se = (x,sf) ==>
    (!b sz. FLOOKUP s.vs_allocas st1.cs_next_id = SOME (b,sz) ==>
      sz = msz /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids sa se /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)))
Proof
  simp_tac bool_ss [return_window_ownership_def] >> strip_tac >>
  conj_tac
  >- (irule return_window_optional_owner_below >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      irule return_window_optional_owner_separate >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  irule return_window_optional_owner_separate >> metis_tac[]
QED

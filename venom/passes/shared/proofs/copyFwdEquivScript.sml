(*
 * Copy Forwarding — Semantic Equivalence Properties
 *
 * Semantic bridge between pointer_confined (structural: pointer-derived
 * vars only at memory-address or pointer-preserving positions) and
 * copy forwarding pass correctness (NOP mcopy + rewrite dst→src).
 *
 * Complements allocaRemapProofs which handles a different scenario:
 *   allocaRemap : same code, different alloca addresses, same content
 *   copyFwdEquiv: different code (operand rewrite), same addresses,
 *                 content differs at dead (dst) alloca
 *
 * The copy forwarding argument:
 *   1. invoke writes data D to src region
 *   2. mcopy (original) copies D to dst / nop (transformed) does nothing
 *   3. Rewritten instructions read from src (transformed) vs dst (original)
 *   4. Both regions have D → same values read → same observable output
 *   5. pointer_confined ensures pointer values never reach observable state
 *
 * TOP-LEVEL:
 *   cross_mem_region_equiv     — regions in different memories match
 *   mcopy_establishes_equiv    — mcopy makes dst content = src content
 *   mcopy_preserves_disjoint   — mcopy doesn't touch other regions
 *   copy_fwd_cross_equiv       — mcopy vs nop → cross equiv holds
 *   copy_fwd_rel               — simulation invariant for copy forwarding
 *   mload_cross_equiv          — MLOAD same result at cross-equiv regions
 *)

Theory copyFwdEquiv
Ancestors
  allocaRemapDefs pointerConfinedDefs memLocDefs passResidualFrame
  venomExecSemantics venomState stateEquiv
  finite_map list rich_list
Libs
  dep_rewrite

(* =========================================================================
   1. Cross-State Memory Region Equivalence
   ========================================================================= *)

(* Two memory regions in possibly-different memories have identical content.
   Uses mem_byte_at (from allocaRemapDefs) for OOB-safe byte access.
   This is the cross-state analog of alloca_mem_agrees (which is per-alloca). *)
Definition cross_mem_region_equiv_def:
  cross_mem_region_equiv
    (mem1 : word8 list) (addr1 : num)
    (mem2 : word8 list) (addr2 : num)
    (sz : num) ⇔
    ∀i. i < sz ⇒
      mem_byte_at mem1 (addr1 + i) = mem_byte_at mem2 (addr2 + i)
End

(* Symmetry *)
Theorem cross_mem_region_equiv_sym:
  ∀m1 a1 m2 a2 sz.
    cross_mem_region_equiv m1 a1 m2 a2 sz ⇒
    cross_mem_region_equiv m2 a2 m1 a1 sz
Proof
  rw[cross_mem_region_equiv_def]
QED

(* Sub-region *)
Theorem cross_mem_region_equiv_sub:
  ∀m1 a1 m2 a2 n k.
    cross_mem_region_equiv m1 a1 m2 a2 n ∧ k ≤ n ⇒
    cross_mem_region_equiv m1 a1 m2 a2 k
Proof
  rw[cross_mem_region_equiv_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

(* Reflexive when same memory, same address *)
Theorem cross_mem_region_equiv_refl:
  ∀mem addr sz. cross_mem_region_equiv mem addr mem addr sz
Proof
  rw[cross_mem_region_equiv_def]
QED

(* =========================================================================
   2. MCOPY and Region Equivalence — Helpers
   ========================================================================= *)

(* Reading from TAKE n (DROP m l ++ REPLICATE n 0w) equals mem_byte_at *)
Theorem take_drop_replicate_el:
  ∀i n m (l : word8 list).
    i < n ⇒
    EL i (TAKE n (DROP m l ++ REPLICATE n 0w)) = mem_byte_at l (m + i)
Proof
  rpt strip_tac >> simp[mem_byte_at_def, EL_TAKE, EL_APPEND_EQN, LENGTH_DROP] >>
  Cases_on `i < LENGTH l - m` >> simp[EL_DROP, EL_REPLICATE]
QED

(* Length of memory after write_memory_with_expansion *)
Theorem wmwe_length:
  ∀offset bytes s.
    LENGTH (write_memory_with_expansion offset bytes s).vs_memory ≥
    offset + LENGTH bytes
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

(* The actual newmem in wmwe *)
Theorem wmwe_vs_memory:
  ∀offset bytes s.
    (write_memory_with_expansion offset bytes s).vs_memory =
    let mem = s.vs_memory in
    let needed = offset + LENGTH bytes − LENGTH mem in
    let expanded = if needed > 0 then mem ++ REPLICATE needed 0w
                   else mem in
    TAKE offset expanded ++ bytes ++ DROP (offset + LENGTH bytes) expanded
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

(* write_memory_with_expansion: reading a written byte *)
Theorem wmwe_byte_at_written:
  ∀offset bytes s i.
    i < LENGTH bytes ⇒
    mem_byte_at (write_memory_with_expansion offset bytes s).vs_memory
      (offset + i) = EL i bytes
Proof
  rpt strip_tac >>
  rewrite_tac[wmwe_vs_memory] >> simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `TAKE offset expanded ++ bytes ++ _` >>
  `LENGTH expanded >= offset + LENGTH bytes` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[LENGTH_APPEND, LENGTH_REPLICATE]) >>
  simp[mem_byte_at_def, LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_DROP,
       EL_APPEND_EQN]
QED

(* write_memory_with_expansion: reading an unwritten byte *)
Theorem wmwe_byte_at_outside:
  ∀offset bytes s addr.
    (addr < offset ∨ offset + LENGTH bytes ≤ addr) ⇒
    mem_byte_at (write_memory_with_expansion offset bytes s).vs_memory addr =
    mem_byte_at s.vs_memory addr
Proof
  rpt strip_tac >>
  rewrite_tac[wmwe_vs_memory] >> simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `TAKE offset expanded ++ _ ++ _` >>
  rename1 `Abbrev (expanded = if _ then mem ++ _ else mem)` >>
  `LENGTH expanded >= offset + LENGTH bytes ∧
   LENGTH expanded >= LENGTH mem ∧
   (∀a. a < LENGTH mem ⇒ EL a expanded = EL a mem)` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >>
     simp[LENGTH_APPEND, LENGTH_REPLICATE, EL_APPEND_EQN]) >>
  simp[mem_byte_at_def, LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_DROP,
       EL_APPEND_EQN] >>
  rpt strip_tac >> gvs[EL_TAKE, EL_DROP] >>
  Cases_on `addr < LENGTH mem` >> gvs[] >>
  simp[Abbr `expanded`] >>
  rpt IF_CASES_TAC >>
  gvs[EL_APPEND_EQN, EL_REPLICATE, LENGTH_APPEND, LENGTH_REPLICATE]
QED

(* =========================================================================
   2b. MCOPY and Region Equivalence
   ========================================================================= *)

(* After mcopy dst src sz, each byte in [dst, dst+sz) equals the
   corresponding byte from [src, src+sz) in the PRE-copy memory.
   This is the foundational property of the copy. *)
(* LENGTH of mcopy data *)
Theorem mcopy_data_length:
  ∀src sz mem. LENGTH (TAKE sz (DROP src mem ++ REPLICATE sz 0w)) = sz
Proof
  simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP, LENGTH_REPLICATE]
QED

Theorem mcopy_establishes_equiv:
  ∀s dst src sz.
    let s' = mcopy dst src sz s in
    ∀i. i < sz ⇒
      mem_byte_at s'.vs_memory (dst + i) =
      mem_byte_at s.vs_memory (src + i)
Proof
  simp[mcopy_def, LET_THM] >> rpt strip_tac >>
  simp[wmwe_byte_at_written, mcopy_data_length, take_drop_replicate_el]
QED

(* mcopy does not modify bytes outside [dst, dst+sz).
   (It may expand memory with zeros, but those are beyond existing size.) *)
Theorem mcopy_preserves_disjoint:
  ∀s dst src sz addr region_sz.
    (addr + region_sz ≤ dst ∨ dst + sz ≤ addr) ⇒
    let s' = mcopy dst src sz s in
    ∀i. i < region_sz ⇒
      mem_byte_at s'.vs_memory (addr + i) =
      mem_byte_at s.vs_memory (addr + i)
Proof
  simp[mcopy_def, LET_THM] >> rpt strip_tac >>
  irule wmwe_byte_at_outside >> simp[mcopy_data_length]
QED

(* The cross-state property needed at the mcopy/nop divergence point.
   Original: mcopy ran → dst has data from src (pre-copy).
   Transformed: nop ran → src still has its data (unchanged).
   If src wasn't modified between invoke and copy, then
   dst-in-original and src-in-transformed have the same content. *)
Theorem copy_fwd_cross_equiv:
  ∀mem dst_addr src_addr sz.
    let mem_after_copy = (mcopy dst_addr src_addr sz
                           ((init_venom_state "") with vs_memory := mem)).vs_memory in
    cross_mem_region_equiv mem_after_copy dst_addr mem src_addr sz
Proof
  rw[cross_mem_region_equiv_def, LET_THM] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`((init_venom_state "") with vs_memory := mem)`, `dst_addr`, `src_addr`, `sz`]
    mcopy_establishes_equiv) >> simp[LET_THM] >>
  disch_then drule >> simp[]
QED

(* =========================================================================
   3. Memory Reads Under Cross-Equivalence
   ========================================================================= *)

(* Bridge: cross_mem_region_equiv implies TAKE/DROP equality
   (needed because mload/sha3/return use TAKE/DROP, not mem_byte_at). *)
Theorem cross_equiv_take_drop:
  ∀mem1 addr1 mem2 addr2 sz.
    cross_mem_region_equiv mem1 addr1 mem2 addr2 sz ⇒
    TAKE sz (DROP addr1 mem1 ++ REPLICATE sz 0w) =
    TAKE sz (DROP addr2 mem2 ++ REPLICATE sz 0w)
Proof
  rw[cross_mem_region_equiv_def] >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP,
                         LENGTH_REPLICATE] >>
  rpt strip_tac >> simp[take_drop_replicate_el]
QED

(* MLOAD: reading 32 bytes from cross-equivalent regions gives same word. *)
Theorem mload_cross_equiv:
  ∀s1 s2 addr1 addr2.
    cross_mem_region_equiv s1.vs_memory addr1 s2.vs_memory addr2 32 ⇒
    mload addr1 s1 = mload addr2 s2
Proof
  rw[mload_def] >> rpt strip_tac >>
  imp_res_tac cross_equiv_take_drop >> fs[]
QED

(* SHA3: hashing cross-equivalent regions gives same hash. *)
Theorem sha3_cross_equiv:
  ∀mem1 addr1 mem2 addr2 sz.
    cross_mem_region_equiv mem1 addr1 mem2 addr2 sz ⇒
    let data1 = TAKE sz (DROP addr1 mem1 ++ REPLICATE sz 0w) in
    let data2 = TAKE sz (DROP addr2 mem2 ++ REPLICATE sz 0w) in
    data1 = data2
Proof
  rpt strip_tac >> imp_res_tac cross_equiv_take_drop >> fs[]
QED

(* =========================================================================
   4. Copy Forwarding Simulation Relation

   Captures the state of the two executions between the NOP'd mcopy
   and the last rewritten use. The key property: states agree on
   everything except memory at the dst alloca (which was never written
   in the transformed execution).

   In the ORIGINAL execution, instructions use dst-alias operands
   to access dst's memory (which has copied data).
   In the TRANSFORMED execution, those operands were rewritten to
   src_root, so instructions access src's memory (which has original
   data from the invoke).

   cross_mem_region_equiv connects the two: dst-in-original has the
   same content as src-in-transformed.
   ========================================================================= *)

Definition copy_fwd_rel_def:
  copy_fwd_rel (dst_addr : num) (src_addr : num) (alloca_sz : num) s1 s2 ⇔
    (* Observable state agrees *)
    observable_equiv s1 s2 ∧
    (* All variables agree *)
    (∀v. lookup_var v s1 = lookup_var v s2) ∧
    (* The dst region in s1 and the src region in s2 have same content.
       s1 = original (mcopy wrote to dst), s2 = transformed (src unchanged). *)
    cross_mem_region_equiv
      s1.vs_memory dst_addr s2.vs_memory src_addr alloca_sz ∧
    (* The src region is the same in both (not clobbered) *)
    cross_mem_region_equiv
      s1.vs_memory src_addr s2.vs_memory src_addr alloca_sz ∧
    (* Variables, memory and six observable components are related above;
       four FMP components were unconstrained. Control and allocation state
       and every other component remain in this residual record. *)
    copy_fwd_frame s1 = copy_fwd_frame s2
End

(* copy_fwd_rel implies observable_equiv *)
Theorem copy_fwd_rel_observable_equiv:
  ∀dst src sz s1 s2.
    copy_fwd_rel dst src sz s1 s2 ⇒
    observable_equiv s1 s2
Proof
  rw[copy_fwd_rel_def]
QED

(* =========================================================================
   5. ASSIGN Transparency

   ASSIGN forwards values unchanged. pointer_confined + ASSIGN means
   the output is pointer-derived (if input was), so it stays in the
   pointer-derived set and remains confined.
   ========================================================================= *)

(* Cache the proved ASSIGN branch without unfolding the full opcode dispatch. *)
val step_inst_base_assign = valOf (List.find (fn th =>
  aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) ``ASSIGN``)
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs));

Theorem assign_transparent:
  ∀inst s s' out v.
    inst.inst_opcode = ASSIGN ∧
    inst.inst_operands = [Var v] ∧
    inst.inst_outputs = [out] ∧
    step_inst_base inst s = OK s' ⇒
    lookup_var out s' = lookup_var v s
Proof
  rpt strip_tac >>
  gvs[step_inst_base_assign, eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[update_var_def, FLOOKUP_UPDATE]
QED

Theorem phi_transparent:
  !inst s out prev v.
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var v) ==>
    !val. eval_one_phi s inst = SOME (out,val) ==>
      val = THE (lookup_var v s) /\
      lookup_var out (update_var out val s) = lookup_var v s
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def, AllCaseEqs()] >>
  gvs[eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars v` >> gvs[update_var_def, FLOOKUP_UPDATE]
QED

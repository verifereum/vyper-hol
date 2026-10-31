Theory immutableMemoryFrame
Ancestors
  immutableRelation immutableEncodingProofs staticLayoutWf

(* An unconditional normal form exposes both in-bounds writes and expansion. *)
Theorem immutable_write_memory_bytes:
  (write_memory_with_expansion at bs s).vs_memory =
    TAKE at (s.vs_memory ++ REPLICATE (at + LENGTH bs - LENGTH s.vs_memory) 0w) ++
    bs ++ DROP (at + LENGTH bs)
      (s.vs_memory ++ REPLICATE (at + LENGTH bs - LENGTH s.vs_memory) 0w)
Proof
  simp[venomStateTheory.write_memory_with_expansion_def] >>
  Cases_on `at + LENGTH bs - LENGTH s.vs_memory > 0` >> simp[] >>
  `at + LENGTH bs - LENGTH s.vs_memory = 0` by decide_tac >> simp[]
QED

Theorem immutable_write_memory_capacity:
  LENGTH (write_memory_with_expansion at bs s).vs_memory =
    MAX (LENGTH s.vs_memory) (at + LENGTH bs)
Proof
  simp[immutable_write_memory_bytes, listTheory.LENGTH_TAKE_EQ,
       listTheory.LENGTH_DROP] >>
  simp[arithmeticTheory.MIN_DEF, arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem immutable_expanded_slice:
  off + n <= LENGTH mem ==>
  TAKE n (DROP off (mem ++ extra)) = TAKE n (DROP off mem)
Proof
  strip_tac >> simp[listTheory.DROP_APPEND1, listTheory.TAKE_APPEND1]
QED

Theorem immutable_write_memory_disjoint:
  off + n <= LENGTH s.vs_memory /\
  (off + n <= at \/ at + LENGTH bs <= off) ==>
  TAKE n (DROP off (write_memory_with_expansion at bs s).vs_memory) =
    TAKE n (DROP off s.vs_memory)
Proof
  strip_tac >> rewrite_tac[immutable_write_memory_bytes] >>
  irule EQ_TRANS >>
  irule_at (Pos hd) immutable_slice_splice_disjoint >>
  simp[] >> irule immutable_expanded_slice >> simp[]
QED

Theorem immutable_write_memory_prefix:
  cap <= LENGTH s.vs_memory /\ cap <= at ==>
  TAKE cap (write_memory_with_expansion at bs s).vs_memory = TAKE cap s.vs_memory
Proof
  strip_tac >>
  mp_tac (Q.INST [`off` |-> `0`, `n` |-> `cap`] immutable_write_memory_disjoint) >>
  simp[]
QED

Theorem immutable_write_memory_in_bounds:
  at + LENGTH bs <= LENGTH s.vs_memory ==>
  (write_memory_with_expansion at bs s).vs_memory =
    TAKE at s.vs_memory ++ bs ++ DROP (at + LENGTH bs) s.vs_memory
Proof
  strip_tac >> `at + LENGTH bs - LENGTH s.vs_memory = 0` by decide_tac >>
  simp[immutable_write_memory_bytes]
QED

Theorem immutable_write_memory_slice:
  TAKE (LENGTH bs) (DROP at (write_memory_with_expansion at bs s).vs_memory) = bs
Proof
  simp[immutable_write_memory_bytes, listTheory.DROP_APPEND,
       listTheory.LENGTH_TAKE_EQ, listTheory.TAKE_APPEND1,
       listTheory.DROP_TAKE]
QED

Theorem immutable_mstore_as_write:
  mstore at w s = write_memory_with_expansion at (word_to_bytes w T) s
Proof
  simp[venomStateTheory.mstore_def, venomStateTheory.write_memory_with_expansion_def,
       byteTheory.LENGTH_word_to_bytes, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem immutable_istore_as_write:
  (istore at w s).vs_memory =
    (write_memory_with_expansion at (word_to_bytes w T) s).vs_memory
Proof
  simp[venomExecSemanticsTheory.istore_def, immutable_mstore_as_write]
QED

(* In particular a successful concrete placement protects the reserved prefix.
   A zero-sized allocation does not imply this inequality. *)
Theorem immutable_static_position_after_region:
  static_position_wf reserved pos sz /\ MEM (0,cap) reserved /\ 0 < w2n sz ==>
  cap <= pos /\ pos + w2n sz < dimword (:256)
Proof
  simp[staticLayoutWfTheory.static_position_wf_def, listTheory.EVERY_MEM] >>
  strip_tac >> gvs[] >> first_x_assum (qspec_then `(0,cap)` mp_tac) >>
  simp[staticLayoutDefsTheory.reserved_intervals_disjoint_def] >>
  strip_tac >> gvs[]
QED

Theorem immutable_word_address_no_wrap:
  (region:num) + off < dimword (:256) ==>
  w2n ((n2w region : bytes32) + n2w off) = region + off
Proof
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w]
QED

(* A bounded update has the same byte replacement equation in the reserved
   prefix as in whole memory. This supplies the staging boundary, including
   all capacity bytes rather than just the decoded payload. *)
Theorem immutable_write_memory_prefix_replace:
  at + LENGTH bs <= cap /\ cap <= LENGTH s.vs_memory ==>
  TAKE cap (write_memory_with_expansion at bs s).vs_memory =
    TAKE at (TAKE cap s.vs_memory) ++ bs ++
    DROP (at + LENGTH bs) (TAKE cap s.vs_memory)
Proof
  strip_tac >>
  `at + LENGTH bs <= LENGTH s.vs_memory` by decide_tac >>
  simp[immutable_write_memory_in_bounds] >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_DROP,
       listTheory.EL_TAKE, listTheory.EL_APPEND_EQN, listTheory.EL_DROP] >>
  rpt strip_tac >> simp[]
QED

Theorem immutable_staging_write_outside:
  immutable_staging_exact tops imms s /\
  LENGTH (immutables_section tops imms) <= LENGTH s.vs_memory /\
  LENGTH (immutables_section tops imms) <= at ==>
  immutable_staging_exact tops imms (write_memory_with_expansion at bs s)
Proof
  strip_tac >>
  drule_all immutable_staging_prefix >> strip_tac >>
  `LENGTH (immutables_section tops imms) <=
     LENGTH (write_memory_with_expansion at bs s).vs_memory` by
    (gvs[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF] >>
     IF_CASES_TAC >> gvs[]) >>
  simp[immutable_staging_exact_def, listTheory.TAKE_APPEND1,
       immutable_write_memory_prefix]
QED

Theorem immutable_staging_write_replace:
  immutable_staging_exact tops imms s /\
  LENGTH (immutables_section tops imms) <= LENGTH s.vs_memory /\
  at + LENGTH bs <= LENGTH (immutables_section tops imms) /\
  immutables_section tops imms' =
    TAKE at (immutables_section tops imms) ++ bs ++
    DROP (at + LENGTH bs) (immutables_section tops imms) ==>
  immutable_staging_exact tops imms' (write_memory_with_expansion at bs s)
Proof
  strip_tac >>
  drule_all immutable_staging_prefix >> strip_tac >>
  `LENGTH (immutables_section tops imms') = LENGTH (immutables_section tops imms)` by
    (simp[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_DROP] >> decide_tac) >>
  `LENGTH (immutables_section tops imms') <=
     LENGTH (write_memory_with_expansion at bs s).vs_memory` by
    (gvs[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF] >>
     IF_CASES_TAC >> gvs[]) >>
  simp[immutable_staging_exact_def, listTheory.TAKE_APPEND1] >>
  drule_all immutable_write_memory_prefix_replace >> simp[]
QED

Theorem immutable_mstore_prefix:
  cap <= LENGTH s.vs_memory /\ cap <= at ==>
  TAKE cap (mstore at w s).vs_memory = TAKE cap s.vs_memory
Proof
  simp[immutable_mstore_as_write, immutable_write_memory_prefix]
QED

Theorem immutable_istore_word_slice:
  TAKE 32 (DROP at (istore at w s).vs_memory) = word_to_bytes w T
Proof
  mp_tac (Q.INST [`bs` |-> `word_to_bytes (w:bytes32) T`]
    immutable_write_memory_slice) >>
  simp[immutable_istore_as_write, byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem immutable_relation_write_disjoint:
  (!name tv v off.
    FLOOKUP cenv.ce_vars (module_var_key (src,name)) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP vs.immutables addr of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    immutable_value_admissible tv v /\
    off + type_memory_size tv <= LENGTH s.vs_memory /\
    TAKE (type_memory_size tv) (DROP off s.vs_memory) = encode_immutable_value tv v /\
    (off + type_memory_size tv <= at \/ at + LENGTH bs <= off)) ==>
  immutables_rel cenv addr src T vs (write_memory_with_expansion at bs s)
Proof
  strip_tac >> irule immutable_relation_from_slices >> simp[] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  simp[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF,
       immutable_write_memory_disjoint]
QED

(* The allocation certificate is consumed at its concrete-position boundary;
   arbitrary pointer writes are deliberately not certified by reservation. *)
Theorem immutable_reserved_allocation_write_prefix:
  static_position_wf reserved pos sz /\ MEM (0,cap) reserved /\
  0 < w2n sz /\ cap <= LENGTH s.vs_memory ==>
  TAKE cap (write_memory_with_expansion (pos + k) bs s).vs_memory =
    TAKE cap s.vs_memory
Proof
  strip_tac >> drule_all immutable_static_position_after_region >> strip_tac >>
  irule immutable_write_memory_prefix >> simp[]
QED

Theorem immutable_reserved_allocation_word_prefix:
  static_position_wf reserved pos sz /\ MEM (0,cap) reserved /\
  k + 32 <= w2n sz /\ cap <= LENGTH s.vs_memory ==>
  TAKE cap (mstore (w2n ((n2w pos : bytes32) + n2w k)) w s).vs_memory =
    TAKE cap s.vs_memory
Proof
  strip_tac >>
  `0 < w2n sz` by decide_tac >>
  drule_all immutable_static_position_after_region >> strip_tac >>
  `pos + k < dimword (:256)` by decide_tac >>
  simp[immutable_word_address_no_wrap, immutable_mstore_prefix]
QED

Theorem immutable_mstore_word_bytes:
  (mstore at w s).vs_memory =
    TAKE at (s.vs_memory ++ REPLICATE (at + 32 - LENGTH s.vs_memory) 0w) ++
    word_to_bytes w T ++
    DROP (at + 32) (s.vs_memory ++ REPLICATE (at + 32 - LENGTH s.vs_memory) 0w)
Proof
  simp[venomStateTheory.mstore_def] >>
  Cases_on `at + 32 - LENGTH s.vs_memory > 0` >> simp[] >>
  `at + 32 - LENGTH s.vs_memory = 0` by decide_tac >> simp[]
QED

Theorem immutable_mstore_capacity:
  LENGTH (mstore at w s).vs_memory = MAX (LENGTH s.vs_memory) (at + 32)
Proof
  simp[immutable_mstore_as_write, immutable_write_memory_capacity,
       byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

(* Boundary checks include a destination beyond current capacity and the
   degenerate empty write; even that write expands up to its destination. *)
Theorem immutable_memory_frame_edge_probe:
  let s = (init_venom_state "entry") with vs_memory := [1w;2w;3w;4w] in
    TAKE 4 (write_memory_with_expansion 8 [9w;10w] s).vs_memory = [1w;2w;3w;4w] /\
    LENGTH (write_memory_with_expansion 8 [9w;10w] s).vs_memory = 10 /\
    (write_memory_with_expansion 8 [] s).vs_memory = [1w;2w;3w;4w;0w;0w;0w;0w] /\
    TAKE 2 (DROP 1 (write_memory_with_expansion 1 [9w;10w] s).vs_memory) = [9w;10w]
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_MEMORY_FRAME_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable memory frame theorem: " ^ name)
  end) (DB.thms "immutableMemoryFrame");

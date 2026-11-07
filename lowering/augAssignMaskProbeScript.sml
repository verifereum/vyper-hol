(* Finite changing-mask probes. These are paired source-format writes,
   NOT a theorem about the compiled nested store-copy path. *)
Theory augAssignMaskProbe
Ancestors
  venomState venomMemProps compileEnv vyperStorage vyperStorageBackend vyperValue vfmState list words

Theorem saved_inner_shrink_growth_mask_probe:
  let tv = ArrayTV (BaseTV (UintT 256)) (Dynamic 2);
      outer = ArrayTV tv (Dynamic 2);
      src = (\k:bytes32. if k = 0w then 2w else
                          if k = 4w then 1w else
                          if k = 5w then 7w else
                          if k = 6w then 91w else 0w);
      ir = (\k:bytes32. if k = 0w then 2w else
                         if k = 4w then 1w else
                         if k = 5w then 7w else
                         if k = 6w then 92w else 0w);
      shrink = [(0,0w)];
      grow = [(0,2w); (1,0w); (4,2w); (5,11w); (6,12w)];
      src1 = apply_writes 0w shrink src;
      ir1 = apply_writes 0w shrink ir;
      src2 = apply_writes 0w grow src1;
      ir2 = apply_writes 0w grow ir1
  in
    encode_value outer (ArrayV (DynArrayV [])) = SOME shrink /\
    encode_value outer (ArrayV (DynArrayV
      [ArrayV (DynArrayV []);
       ArrayV (DynArrayV [IntV 11; IntV 12])])) = SOME grow /\
    MAP (\k. lookup_storage k src1) [4w;5w;6w] = [1w;7w;91w] /\
    MAP (\k. lookup_storage k ir1) [4w;5w;6w] = [1w;7w;92w] /\
    (!b. b < 32 ==> dead_bytes src 4 tv 6 b /\ dead_bytes src1 4 tv 6 b) /\
    (!b. ~dead_bytes src1 4 tv 4 b /\ ~dead_bytes src1 4 tv 5 b) /\
    MAP (\k. lookup_storage k src2) [4w;5w;6w] = [2w;11w;12w] /\
    MAP (\k. lookup_storage k ir2) [4w;5w;6w] = [2w;11w;12w] /\
    (!b. ~dead_bytes src2 4 tv 6 b)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac
QED

(* Opposite-backend effects preserve the entire saved-region relation,
   including its recomputed mask; no equality on dead capacity is needed. *)
Theorem saved_region_opposite_backend:
  (!k b. w2n root <= w2n k /\
    w2n k < w2n root + type_slot_size tv /\ b < 32 /\
    ~dead_bytes (get_storage cx es tr) (w2n root) tv (w2n k) b ==>
    EL b (word_to_bytes (lookup_storage k (get_storage cx es tr)) T) =
    EL b (word_to_bytes (if tr then tload k s else sload k s) T)) ==>
  !k b. w2n root <= w2n k /\
    w2n k < w2n root + type_slot_size tv /\ b < 32 /\
    ~dead_bytes (get_storage cx (set_storage cx es (~tr) store') tr)
      (w2n root) tv (w2n k) b ==>
    EL b (word_to_bytes
      (lookup_storage k (get_storage cx (set_storage cx es (~tr) store') tr)) T) =
    EL b (word_to_bytes
      (if tr then tload k (sstore key value s)
       else sload k (tstore key value s)) T)
Proof
  Cases_on `tr` >>
  simp[get_storage_after_set_other, tload_def, sload_def,
       contract_transient_def, contract_storage_def, sstore_def, tstore_def]
QED

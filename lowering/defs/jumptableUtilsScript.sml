(*
 * Jumptable Utilities for Selector Dispatch
 *
 * Port of vyper/codegen/jumptable_utils.py
 *
 * Pure-functional utilities for computing perfect hash tables
 * used in dense and sparse selector dispatch strategies.
 *
 * TOP-LEVEL:
 *   generate_dense_jumptable_info    -- compute dense buckets + magic
 *   generate_sparse_jumptable_buckets -- compute sparse bucket assignment
 *   compute_fn_metadata_bytes        -- metadata byte width
 *   build_dense_data_sections        -- data sections for dense dispatch
 *   build_sparse_data_sections       -- data sections for sparse dispatch
 *)

Theory jumptableUtils
Ancestors
  venomInst
Libs
  stringLib

(* ===== Jumptable Utilities ===== *)

Definition BITS_MAGIC_def:
  BITS_MAGIC = 24n
End

(* image_of xs magic = [((x * magic) >> BITS_MAGIC) MOD len | x <- xs] *)
Definition image_of_def:
  image_of (xs : num list) (magic : num) =
    let n = LENGTH xs in
    if n = 0 then [] else
    MAP (λx. ((x * magic) DIV (2 ** BITS_MAGIC)) MOD n) xs
End

(* Check if image is a perfect hash (all distinct) *)
Definition is_perfect_hash_def:
  is_perfect_hash xs magic =
    ALL_DISTINCT (image_of xs magic)
End

(* find_magic_for: brute-force search for perfect hash magic in 0..65535.
   Returns SOME magic or NONE. Uses OWHILE for termination. *)
Definition find_magic_for_def:
  find_magic_for (xs : num list) =
    let result = OWHILE (λ(found, m). ¬found ∧ m < 65536)
      (λ(_, m). if is_perfect_hash xs m then (T, m) else (F, m + 1))
      (F, 0n) in
    case result of
      SOME (T, m) => SOME m
    | _ => NONE
End

(* Group method_ids into buckets by (method_id MOD n_buckets).
   Returns (bucket_id, method_ids) alist. *)
Definition mk_buckets_def:
  mk_buckets (method_ids : num list) (n_buckets : num) =
    FOLDL (λacc mid.
      let bid = mid MOD n_buckets in
      case ALOOKUP acc bid of
        SOME ids => MAP (λ(b,ids'). if b = bid then (b, ids' ++ [mid]) else (b,ids')) acc
      | NONE => acc ++ [(bid, [mid])])
    [] method_ids
End

(* Dense bucket info: (bucket_id, magic, method_ids) *)
Datatype:
  dense_bucket = <|
    db_id : num;
    db_magic : num;
    db_method_ids : num list
  |>
End

(* Sort method_ids by their image under the hash.
   Returns method_ids in image order. *)
Definition method_ids_image_order_def:
  method_ids_image_order (mids : num list) (magic : num) =
    let imgs = image_of mids magic in
    MAP SND (QSORT (λ(i1,_) (i2,_). i1 ≤ i2) (ZIP (imgs, mids)))
End

(* Try to build dense jumptable info for a given n_buckets.
   Returns SOME bucket_list if all buckets have a magic, NONE otherwise. *)
Definition try_dense_info_def:
  try_dense_info (method_ids : num list) (n_buckets : num) =
    let buckets = mk_buckets method_ids n_buckets in
    if LENGTH buckets ≠ n_buckets then NONE  (* empty buckets *)
    else
      let with_magic = MAP (λ(bid, mids).
        case find_magic_for mids of
          NONE => NONE
        | SOME m => SOME <| db_id := bid; db_magic := m;
                           db_method_ids := mids |>) buckets in
      if EXISTS IS_NONE with_magic then NONE
      else SOME (MAP THE with_magic)
End

(* generate_dense_jumptable_info: search for optimal n_buckets.
   Starts at n/5+1 and decreases. Returns SOME (n_buckets, bucket_list). *)
Definition generate_dense_jumptable_info_def:
  generate_dense_jumptable_info (method_ids : num list) =
    let n = LENGTH method_ids in
    let start = n DIV 5 + 1 in
    let result = OWHILE
      (λ(best, nb). nb > 0)
      (λ(best, nb).
        case try_dense_info method_ids nb of
          SOME info => (SOME (nb, info), nb - 1)
        | NONE =>
            (case best of
               SOME _ => (best, 0)  (* found one before, stop *)
             | NONE => (NONE, nb - 1)))
      (NONE, start) in
    case result of
      SOME (best, _) => best
    | _ => NONE
End

(* generate_sparse_jumptable_buckets: find n_buckets minimizing max bucket size.
   Searches range [0.85*n, 1.15*n]. Returns (n_buckets, buckets). *)
Definition generate_sparse_jumptable_buckets_def:
  generate_sparse_jumptable_buckets (method_ids : num list) =
    let n = LENGTH method_ids in
    let lo = MAX 1 ((n * 85) DIV 100) in
    let hi = MAX 1 ((n * 115 + 99) DIV 100) in  (* ceiling *)
    let candidates = GENLIST (λi. i + lo) (hi - lo + 1) in
    let scored = MAP (λnb.
      let buckets = mk_buckets method_ids nb in
      let max_sz = FOLDL (λacc (_, mids). MAX acc (LENGTH mids)) 0 buckets in
      (max_sz, nb, buckets)) candidates in
    let best = FOLDL (λacc (sz, nb, bkts).
      case acc of
        NONE => SOME (sz, nb, bkts)
      | SOME (best_sz, _, _) =>
          if sz < best_sz then SOME (sz, nb, bkts) else acc)
      NONE scored in
    case best of
      SOME (_, nb, bkts) => (nb, bkts)
    | NONE => (1, mk_buckets method_ids 1)
End

(* Compute fn_metadata_bytes from min_calldatasize values.
   ceil(bit_length(max_value) / 8), minimum 1. *)
Definition compute_fn_metadata_bytes_def:
  compute_fn_metadata_bytes (min_cds_values : num list) =
    let max_val = FOLDL MAX 0 min_cds_values in
    if max_val = 0 then 1
    else (LOG2 max_val DIV 8) + 1
End

(* ===== Dense Data Section Builder ===== *)

(* Build BUCKET_HEADERS data section for dense dispatch.
   Each entry: magic (2 bytes big-endian) ++ DataLabel bucket_lbl ++ size (1 byte). *)
Definition dense_bucket_header_items_def:
  dense_bucket_header_items [] = ([] : data_item list) ∧
  dense_bucket_header_items (db :: rest) =
    let magic_hi = (db.db_magic DIV 256) MOD 256 in
    let magic_lo = db.db_magic MOD 256 in
    DataBytes [n2w magic_hi; n2w magic_lo] ::
    DataLabel ("bucket_" ++ toString db.db_id) ::
    DataBytes [n2w (LENGTH db.db_method_ids)] ::
    dense_bucket_header_items rest
End

(* Build per-bucket data section items for dense dispatch.
   Each entry: method_id (4 bytes big-endian) ++ DataLabel entry_lbl ++
   metadata (fn_metadata_bytes bytes big-endian).
   entry_map: method_id -> (entry_label, min_calldatasize, is_nonpayable). *)
Definition dense_bucket_items_def:
  dense_bucket_items [] _ _ = ([] : data_item list) ∧
  dense_bucket_items (mid :: rest) fn_metadata_bytes
      (entry_map : num -> (string # num # bool)) =
    let (lbl, min_cds, is_nonpayable) = entry_map mid in
    let metadata_val = min_cds + (if is_nonpayable then 1 else 0) in
    (* method_id: 4 bytes big-endian *)
    let b0 = (mid DIV (2 ** 24)) MOD 256 in
    let b1 = (mid DIV (2 ** 16)) MOD 256 in
    let b2 = (mid DIV (2 ** 8)) MOD 256 in
    let b3 = mid MOD 256 in
    DataBytes [n2w b0; n2w b1; n2w b2; n2w b3] ::
    DataLabel lbl ::
    (* metadata: fn_metadata_bytes bytes big-endian *)
    DataBytes (GENLIST (λi.
      n2w ((metadata_val DIV (2 ** ((fn_metadata_bytes - 1 - i) * 8))) MOD 256))
      fn_metadata_bytes) ::
    dense_bucket_items rest fn_metadata_bytes entry_map
End

(* Build all data sections for dense dispatch (pure version).
   Returns list of data_section: BUCKET_HEADERS + per-bucket sections.
   The monad-based emit_dense_data_sections in moduleLowering performs
   the same computation within the compile monad. This pure version
   is for specification and correctness proofs. *)
Definition build_dense_data_sections_def:
  build_dense_data_sections (buckets : dense_bucket list)
      fn_metadata_bytes
      (entry_map : num -> (string # num # bool)) =
    let sorted_buckets = QSORT (λb1 b2. b1.db_id ≤ b2.db_id) buckets in
    let header_sec = <| ds_label := "BUCKET_HEADERS";
                        ds_items := dense_bucket_header_items sorted_buckets |> in
    let bucket_secs = MAP (λdb.
      let ordered_mids = method_ids_image_order db.db_method_ids db.db_magic in
      <| ds_label := "bucket_" ++ toString db.db_id;
         ds_items := dense_bucket_items ordered_mids fn_metadata_bytes entry_map |>)
      sorted_buckets in
    header_sec :: bucket_secs
End

(* Build data sections for sparse dispatch (pure version).
   BUCKET_HEADERS: one 2-byte DataLabel per bucket (bucket code block label).
   For specification; actual emission is inline in compile_selector_dispatch_sparse. *)
Definition build_sparse_data_sections_def:
  build_sparse_data_sections (bucket_labels : string list) =
    [<| ds_label := "BUCKET_HEADERS";
        ds_items := MAP DataLabel bucket_labels |>]
End

val _ = export_theory();

(* Natural-slot deadness boundaries, independent of storage backend.
   Conversion from word keys requires separate no-wrap reasoning. *)
Theory bodyPtrBopInStorageContents
Ancestors accountsRelProps compileEnv

Theorem fixed_array_deadless_children:
  !st tv bs cap j b.
    (!base j b. ~dead_bytes st base tv j b) ==>
    ~dead_bytes st bs (ArrayTV tv (Fixed cap)) j b
Proof
  simp[Once dead_bytes_def]
QED

Theorem dynamic_array_live_deadless_child:
  !st tv bs cap i j b.
    (!base j b. ~dead_bytes st base tv j b) /\
    i < cap /\ i < w2n (lookup_storage (n2w bs) st) /\
    bs + 1 + i * type_slot_size tv <= j /\
    j < bs + 1 + i * type_slot_size tv + type_slot_size tv ==>
    ~dead_bytes st bs (ArrayTV tv (Dynamic cap)) j b
Proof
  metis_tac[dyn_array_elem_dead]
QED

Theorem dynamic_array_header_not_dead:
  !st bs tv cap b.
    ~dead_bytes st bs (ArrayTV tv (Dynamic cap)) bs b
Proof
  rpt strip_tac >> drule (cj 1 dead_bytes_range) >> simp[]
QED

Theorem flag_storage_deadless:
  !st base k j b. ~dead_bytes st base (FlagTV k) j b
Proof
  simp[dead_bytes_def]
QED

Theorem base_storage_deadless:
  !ty st base j b.
    (!n. ty <> StringT n) /\ (!n. ty <> BytesT (Dynamic n)) ==>
    ~dead_bytes st base (BaseTV ty) j b
Proof
  Cases >> simp[dead_bytes_def] >> Cases_on `b` >> simp[dead_bytes_def]
QED

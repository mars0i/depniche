Inductive niche (k : nat) : Type :=
  mkniche : nat -> niche k.

Definition incorg {k : nat} (o : niche k) :=
match o with
  mkniche k => mkniche (S k)
end.

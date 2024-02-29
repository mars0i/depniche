(* This has been checked in https://coq.vercel.app/scratchpad.html *)
  
Inductive foo : Set :=
  | fooey.

(* Note that the type on a constructor doesn't use a function type to
   represent the argument. I guess that's just derived from the signature
   of the whole datatype. *)

Inductive niche (k : nat) : Set :=
  | mkniche : niche k.

(* Increment the index of a niche user. *)
Definition incorg {k : nat} (o : niche k) :=
match o with
  (mkniche _) => mkniche (S k)   (* weird syntax that error messages forced *)
end.

Check (niche 5).
Check (mkniche 5).
Check incorg (mkniche 5).

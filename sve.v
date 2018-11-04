
Require Import List.
Import ListNotations.
Require Import Nat.




Definition var := nat.

Definition monomial := list var.

Definition polynomial := list monomial.

Definition subst := list (prod var polynomial).


(* Apply a comparator to lists lexicographically *)
Fixpoint lex {T : Type} (cmp : T -> T -> comparison) (l1 l2 : list T)
              : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | h1 :: t1, h2 :: t2 =>
      match cmp h1 h2 with
      | Eq => lex cmp t1 t2
      | c => c
      end
  end.


Example lex1 : lex compare [] [1] = Lt.
Proof.
reflexivity.
Qed.

Example lex2 : lex compare [1] [2] = Lt.
Proof.
reflexivity.
Qed.

Example lex3 : lex compare [1;2] [2] = Lt.
Proof.
reflexivity.
Qed.


(* Polynomial Arithmetic *)

Fixpoint addPP (p : polynomial) : polynomial -> polynomial 
                := fix addPPq (q : polynomial) :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | m :: p', n :: q' =>
      match lex compare m n with
      | Eq => addPP p' q'
      | Lt => m :: addPP p' q
      | Gt => n :: addPPq q'
      end
  end.


Fixpoint mulMM (m : monomial) : monomial -> monomial 
                := fix mulMMn (n : monomial) :=
  match m, n with
  | [], _ => n
  | _, [] => m
  | a :: m', b :: n' =>
      match compare a b with
      | Eq => a :: mulMM m' n'
      | Lt => a :: mulMM m' n
      | Gt => b :: mulMMn n'
      end
  end.


Fixpoint mulMP (m : monomial) (p : polynomial) : polynomial :=
  match p with
  | [] => []
  | n :: p' => addPP [mulMM m n] (mulMP m p')
  end.


Fixpoint mulPP (p : polynomial) (q : polynomial) : polynomial :=
  match p with
  | [] => []
  | m :: p' => addPP (mulMP m q) (mulPP p' q)
  end.



Example arith1 : mulPP [[1];[2]] [[1]] = [[1];[1;2]].
Proof.
reflexivity.
Qed.

Example arith2 : mulPP [[1];[]] [[1]] = [].
Proof.
reflexivity.
Qed.


(* Unification helpers *)

Definition indom (x : var) (s : subst) : bool :=
  existsb (eqb x) (map fst s).


Fixpoint app (s : subst) (x : var) : polynomial :=
  match s with
  | [] => [] (* Shouldn't get here *)
  | (y, p) :: s' => if x =? y then p else app s' x
  end.


Fixpoint substM (s : subst) (m : monomial) : polynomial :=
  match m with
  | [] => [[]]
  | x :: m' => if indom x s then mulPP (app s x) (substM s m')
               else mulMP [x] (substM s m')
  end.


Fixpoint substP (s : subst) (p : polynomial) : polynomial :=
  match p with
  | [] => []
  | m :: p' => addPP (substM s m) (substP s p')
  end.


(* Successive Variable Elimination *)

Fixpoint decomp2 (x : var) (p r s : polynomial)
                 : prod polynomial polynomial :=
  match p with
  | [] => (r, s)
  | [] :: p' => (r, s ++ p) (* Shouldn't get here *)
  | (y :: m) :: p' => if x =? y then decomp2 x p' (r ++ [m]) s
                      else (r, s ++ (y :: m) :: p')
  end.


Definition decomp (p : polynomial)
                  : option (prod var (prod polynomial polynomial)) :=
  match p with
  | [] => None (* Shouldn't get here *)
  | [[]] => None (* Shouldn't get here *)
  | [] :: [] :: p' => None (* Shouldn't get here *)
  | [] :: (x :: m) :: p' => Some (x, decomp2 x p' [m] [[]])
  | (x :: m) :: p' => Some (x, decomp2 x p' [m] [])
  end.


(*Fixpoint bunify (p : polynomial) : option subst :=
  match p, decomp p  with
  | [], _ => Some []
  | [[]], _ => None
  | _, None => None (* Shouldn't get here *)
  | _, Some (x, (r, s)) =>
      let r1 := addPP [[]] r in
      match bunify (mulPP r1 s) with
      | None => None
      | Some u =>
          let r1u := substP u r1 in
          let su  := substP u s in
          Some ((x, addPP (mulMP [x] r1u) su) :: u)
      end
  end.*)

Fixpoint bunifyN (n : nat) : polynomial -> option subst := fun p =>
  match p, n  with
  | [], _ => Some []
  | [[]], _ => None
  | _, 0 => None
  | _, S n' => 
      match decomp p with
      | None => None (* Shouldn't get here *)
      | Some (x, (r, s)) =>
          let r1 := addPP [[]] r in
          match bunifyN n' (mulPP r1 s) with
          | None => None
          | Some u =>
              let r1u := substP u r1 in
              let su  := substP u s in
              Some ((x, addPP (mulMP [x] r1u) su) :: u)
          end
      end
  end.


Definition bunify (p : polynomial) := bunifyN (length p) p.







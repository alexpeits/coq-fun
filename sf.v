Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
      | monday => tuesday
      | tuesday => wednesday
      | wednesday => thursday
      | thursday => friday
      | friday => monday
      | saturday => monday
      | sunday => monday
  end.

Compute (next_weekday friday).

Example test_next_weekday:
  (next_weekday friday) = monday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.
           
Definition negb (b:bool) : bool :=
  match b with
      | true => false
      | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
      | true => b2
      | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
      | true => true
      | false => b2
  end.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb: false || false || true = true.
Proof. simpl. reflexivity. Qed.


Check true.
                  
Module Playground1.
  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
  
  Definition pred (n: nat) : nat :=
    match n with
      | O => O
      | S n' => n'
    end.

End Playground1.


Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S (O) => false
    | S (S n') => evenb n'
  end.
  

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.


Module Playground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
      | O => m
      | S n' => S (plus n' m)
    end.

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O => O
      | S n' => plus m (mult n' m)
    end.
  


  Example test_mult1: (mult 3 3) = 9.
  Proof. reflexivity. Qed.

  Fixpoint minus (m n:nat) : nat :=
    match m, n with
      | O , _ => O
      | S _, O => n
      | S m', S n' => minus m' n'
    end.


End Playground2.

Example test_minus: (minus 10 3) = 7.
Proof. reflexivity. Qed.

Fixpoint factorial (n:nat) :nat :=
  match n with
    | O => 1
    | S O => 1
    | S n' => S n' * factorial n'
  end.

Example test_factorial: (factorial 5) = 5 * 4 * 3 * 2 * 1.
Proof. reflexivity. Qed.


Theorem plus_O_n : forall n : nat,  0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Theorem, Example, Lemma, Fact, Remark are all synonymous *)

Theorem plus_id: forall n m : nat,
                   n = m ->
                   n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.


Theorem plus_id_exercise: forall n m o : nat,
                            n = m ->
                            m = o ->
                            n + m = m + o.

Proof.
  intros n m o.
  intros H.
  intros H'.
  rewrite <- H.
  rewrite <- H'.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_0_plus: forall n m : nat,
                       (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.
                       

Theorem plus_S_1: forall n: nat,
                    1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

                  

Theorem mult_S_1: forall n m : nat,
                    m = S n ->
                    m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_S_1.
  rewrite -> H.
  reflexivity.
Qed.

Definition eq_bool (n m : bool) : bool:=
  match n, m with
    | true, true  => true
    | false, false => true
    | _, _ => false
  end.

Definition not (n : bool) : bool:=
  match n with
    | true => false
    | false => true
  end.


Fixpoint eq_nat (n m : nat) : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n', S m' => eq_nat n' m'
  end.

Definition neq_nat (n m: nat): bool := not (eq_nat n m ).

Theorem plus_1_neq_0_first : forall n : nat,
                               eq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
                            negb (negb b) = b.
Proof.
  intros b. destruct b as [|].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_comm : forall b c : bool,
                     andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Theorem andb_true_elim2 : forall b c : bool,
                            andb b c = true -> c = true.
Proof.
  intros [] [].
  {
    intros H.
    reflexivity.
  }
  {
    intros H.
    rewrite <- H.
    reflexivity.
  }
  {
    intros H.
    reflexivity.
  }
  {
    intros H.
    destruct H.
    reflexivity.
  }
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
                             eq_nat 0 (n + 1) = false.
Proof.
  intros [|x]. 
  - reflexivity.
  - reflexivity.
Qed.


Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x: bool), f x = x) ->
  forall (b : bool),  f( f b) = b.
Proof.
  intros f.
  intros h.
  intros [].
  - rewrite -> h.
    rewrite -> h.
    reflexivity.
  - rewrite -> h.
    rewrite -> h.
    reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (b && c = b || c) -> b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl.
    intro H.
    rewrite <- H.
    reflexivity.
  - simpl.
    intro H.
    rewrite <- H.
    reflexivity.
  - reflexivity.
Qed.

Inductive bin : Type :=
| Zero : bin
| Twice : bin -> bin
| STwice : bin -> bin.

Fixpoint incr_bin (b:bin) : bin :=
  match b with
    | Zero => STwice Zero
    | Twice x => STwice  x
    | STwice x => Twice (incr_bin x)
  end.

Fixpoint decr_bin (b:bin) : bin :=
  match b with
    | Zero => Zero
    | STwice Zero => Zero
    | STwice x => Twice x
    | Twice x => STwice (decr_bin x)
  end.

Fixpoint add_bin (b c : bin) : bin :=
  match b, c with
    | x, Zero => x
    | x, STwice y =>  incr_bin (add_bin (add_bin x y) y)
    | x, Twice y =>  add_bin (add_bin x y) y
  end.

Fixpoint sub_bin (b c : bin) : bin :=
  match b, c with
    | x, Zero => x
    | x, STwice y =>  decr_bin (sub_bin (sub_bin x y) y)
    | x, Twice y =>  sub_bin (sub_bin x y) y
  end.


Fixpoint bin_to_nat (b: bin) : nat :=
  match b with
    | Zero => 0
    | Twice x => bin_to_nat x + bin_to_nat x
    | STwice x => 1 +  (bin_to_nat x + bin_to_nat x)
  end.

Fixpoint nat_to_bin (n: nat) : bin :=
  match n with
    | O => Zero
    | S x =>  incr_bin (nat_to_bin x)
  end.

Compute bin_to_nat ((nat_to_bin 100)).
Compute bin_to_nat (add_bin (nat_to_bin 100) (nat_to_bin 100)).
Compute bin_to_nat (sub_bin (nat_to_bin 100) (nat_to_bin 100)).
Compute bin_to_nat (sub_bin (nat_to_bin 200) (nat_to_bin 33)).

Example bin_test_1 : (bin_to_nat(incr_bin Zero) = 1).
Proof. simpl. reflexivity.  Qed.

Example bin_test_2 : (bin_to_nat(incr_bin (incr_bin Zero)) = 2).
Proof. simpl. reflexivity.  Qed.

Example bin_test_3 : (bin_to_nat(incr_bin (incr_bin (incr_bin Zero))) = 3).
Proof. reflexivity.  Qed.

Example bin_test_4 : (bin_to_nat(incr_bin( incr_bin (incr_bin (incr_bin Zero)))) = 4).
Proof. simpl. reflexivity.  Qed.



(* Theorem nat_id : forall n : nat, bin_to_nat (nat_to_bin n) = n. *)
(* Proof. *)
(*   intros [|x]. *)
(*   - simpl. reflexivity. *)
(*   - simpl.  *)

(* Theorem bin_id : forall b : bin, nat_to_bin (bin_to_nat b) = b. *)
(* Proof. *)
(*   intros [|x|y]. *)
(*   - simpl. reflexivity. *)
(*   - simpl. reflexivity. *)

Theorem plus_n_0 : forall n : nat, n = n + 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag : forall n, n - n = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
                     n * 0 = 0.
Proof.
  induction n as [| n' IHn' ].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_n_Sm : forall n m : nat,
                      S (n + m) = n + (S m).
Proof.
  induction n as [| n' ihn' ].
  - reflexivity.
  - simpl. intros. rewrite <- ihn'. reflexivity.
Qed.

Theorem plus_comm2 : forall n m : nat,
                       n + m = m + n.
Proof.
  induction n as [|h' ihn'].
  - intros. rewrite <- plus_n_0. reflexivity.
  - intros. simpl.
    rewrite <- plus_n_Sm.
    rewrite -> ihn'.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
                       n + (m + p) = (n + m) + p.
Proof.
  induction n as [|n' ih].
  - reflexivity.
  - simpl. intros. rewrite -> ih. reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
    | O => O
    | S n => S (S (double n))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [|n' ihn'].
  - reflexivity.
  - simpl. rewrite -> ihn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
                    evenb (S n) = negb (evenb n).
Proof.
  assert (H: forall n, evenb n = evenb (S (S n))). {
    induction n as [|n' ih].
    - reflexivity.
    - reflexivity.
  }
  induction n as [|n' ih].
  - reflexivity.
  - rewrite -> ih.
    rewrite <- H.
    rewrite -> negb_involutive.
    reflexivity.
Qed.


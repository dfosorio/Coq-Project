(*****************************************************************)
(******                       M2 LMFI                      *******)
(******   Functional programming and formal proofs in Coq  *******)
(****** Project : compiling expressions with sums          *******)
(******            designed by Pierre Letouzey             *******)
(*****************************************************************)

Require Import String Datatypes Arith List Lia.
Import ListNotations.
Open Scope list_scope.

(** What you should do :
    a) Remove axiom TODO  and replace its uses by working code.
    b) Replace all uses of  Admitted by actual proofs. *)

(** I) Library *)

(** Compararing integers

    In Coq, comparing a <= b is a logical statement (that is
    a term in Prop). One cannot use it as a test in a
    program. To do so, one shall use boolean comparison
    a <=? b (corresponding to constant Nat.leb).
    Here is the link lien between the two notions,  *)

Lemma leb_le x y : (x <=? y) = true <-> x <= y.
Proof.
 apply Nat.leb_le.
Qed.

Lemma leb_gt x y : (x <=? y) = false <-> y < x.
Proof.
 apply Nat.leb_gt.
Qed.

(** Substraction in Option.

    In natural numbers, Coq usual subtrsaction is truncated:
    when a < b, one has a - b = 0.
    Here, one uses [None] to indicate this and [Some] to
    indicate an "exact" subtraction. *)

Fixpoint safe_minus a b : option nat :=
 match b, a with
   | 0, _ => Some a
   | S b, 0 => None
   | S b, S a => safe_minus a b
 end.

Lemma safe_minus_spec a b :
 match safe_minus a b with
 | Some c => a = b + c
 | None => a < b
 end.
Proof.
 revert b; induction a; destruct b; simpl; auto with arith.
 specialize (IHa b). destruct (safe_minus a b); auto with arith.
Qed.

(** Accessing the n-th element in a list

   NB: list_get exists also in the standard library,
   as List.nth_error. *)

Fixpoint list_get {A} (l:list A) i : option A :=
  match i,l with
    | 0,   x::_ => Some x
    | S j, _::l => list_get l j
    | _, _ => None
  end.

Definition option_map {A B} (f:A->B) (o:option A) :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.

Fixpoint list_set {A} (l:list A) i x : option (list A) :=
  match i,l with
    | 0, _::l => Some (x::l)
    | S j, a::l => option_map (cons a) (list_set l j x)
    | _, _ => None
  end.

Lemma get_app_l {A} (l l':list A)(n:nat) : n < length l ->
  list_get (l++l') n = list_get l n.
Proof.
 revert l.
 induction n; destruct l; simpl; auto with arith; inversion 1.
Qed.

Lemma get_app_r {A} (l l':list A)(n:nat) :
  list_get (l++l') (length l + n) = list_get l' n.
Proof.
 induction l; auto.
Qed.

Lemma get_app_r0 {A} (l l':list A)(n:nat) : n = length l ->
  list_get (l++l') n = list_get l' 0.
Proof.
  intros. rewrite <- (get_app_r l l'). f_equal. lia.
Qed.

Lemma get_app_r' {A} (l l':list A)(n:nat) : length l <= n ->
  list_get (l++l') n = list_get l' (n-length l).
Proof.
 intros. rewrite <- (get_app_r l l'). f_equal. lia.
Qed.

Lemma get_None {A} (l:list A) n :
 list_get l n = None <-> length l <= n.
Proof.
 revert n. induction l; destruct n; simpl; rewrite ?IHl; split;
  auto with arith; inversion 1.
Qed.

Lemma get_Some {A} (l:list A) n x :
 list_get l n = Some x -> n < length l.
Proof.
 revert n. induction l; destruct n; simpl; try discriminate.
  - auto with arith.
  - intros. apply IHl in H. auto with arith.
Qed.

Global Hint Resolve get_Some : core.

Open Scope string_scope.
(** Equivalent of List.assoc, specialized for [string]. 
Here [=?] is [String.eqb] *)

Fixpoint lookup {A}(s:string)(l:list (string*A))(default:A) :=
  match l with
    | nil => default
    | (x,d)::l => if s =? x then d else lookup s l default
  end.

(** Index of an element in a list, specialized for `string` *)

Fixpoint index (s:string)(l:list string) :=
  match l with
    | nil => 0
    | x::l => if s =? x then 0 else S (index s l)
  end.

(** Summation operator : sum f x n = f x + ... + f (x+n).
    Beware, there are  (n+1) terms in this sum...
    In particular sum f 0 n = f 0 + ... + f n. *)

Fixpoint sum f x k :=
  match k with
    | 0 => f x
    | S n' => f x + sum f (S x) n'
  end.

Compute sum (fun _ => 1) 0 10. (* 11 *)
Compute sum (fun x => x) 0 10. (* 0 + 1 + ... + 10 = 55 *)

(** II) Arithmetical expressions with summations *)

(** Expressions *)

Definition var := string.

Inductive op := Plus | Minus | Mult.

Inductive expr :=
  | EInt : nat -> expr
  | EVar : var -> expr
  | EOp  : op -> expr -> expr -> expr
  | ESum : var -> expr -> expr -> expr.

(** (ESum var max body) is the sum of the values of [body]
    when var takes  values from  0 to max
    (included). For example, here is the sum of squares from 0 to 10,
    written sum(x^2,x=0..10) in Maple or
    $\sum_{x=0}^{10}{x^2}$ in LaTeX. *)

Definition test1 :=
  ESum "x" (EInt 10) (EOp Mult (EVar "x") (EVar "x")).

(** More complex, a double summation:
    sum(sum(x*y,y=0..x),x=0..10) *)

Definition test2 :=
  ESum "x" (EInt 10)
   (ESum "y" (EVar "x")
     (EOp Mult (EVar "x") (EVar "y"))).

(** Evaluating expressions *)


(*axuliary function that assigns a value to a variable in the environment.
if the variable is not in, then it is added to the environment*)

Fixpoint assign (env: list (string*nat)) (v: var) (val: nat) :=
  match env with
    | nil => (v,val)::nil
    | (x,d)::l => if v =? x then (v,val)::l else (x,d)::(assign l v val)
  end.

(*Some tests*)
Definition env1 := [("x",5);("y",3); ("z",1)].
Compute assign env1 "y" 10.
Compute assign env1 "a" 2.

Definition eval_op o :=
  match o with
    | Plus => plus
    | Minus => minus
    | Mult => mult
  end.  

(*
The function works in the following way:
  - If int the returned value is the integer
  - If var the returned value is its number in the environment (0 if the var is not in)
  - If op the returned value is the evaluation of the operation over the evaluation of
    the inner expressions
  - If sum, then consider ecorps as a function nat -> nat. Then the returned value is:
    eval (ecorps 0) + eval (ecorps 1) + ... + eval (ecorps (eval efin)). To do this, the
    value of the variable v is changed in the environment for each call of eval (ecorps v).  
*)
Fixpoint eval (env:list (string*nat)) e :=
  match e with
    | EInt n => n
    | EVar v => lookup v env 0
    | EOp o e1 e2 => (eval_op o) (eval env e1) (eval env e2)
    | ESum v efin ecorps => let fix sumExp m : nat :=
                            match m with
                            | 0 => eval (assign env v m) ecorps
                            | S n => (eval (assign env v m) ecorps) + (sumExp n)
                            end
                            in sumExp (eval env efin)
  end.


Compute (eval nil test1). (* 385 expected: n(n+1)(2n+1)/6 for n=10 *)
Compute (eval nil test2). (* 1705 expected result *)


(** III) Stack machine *)

(** Our machine is made of two stacks : a main stack to store 
computations and an auxiliary stack of  variables. Instructions
are stored eleswhere. *)

Record machine :=
  Mach {
      (** Code Pointer *)
      pc : nat;
      (** Main stack *)
      stack : list nat;
      (** Variables stack *)
      vars : list nat
    }.

Definition initial_machine := Mach 0 nil nil.

Inductive instr :=
  (** Push a integer value to the stack. *)
  | Push : nat -> instr
  (** Pop the value from the top of the stack. *)
  | Pop : instr
  (** Pop two values and push the result of the binary operation. *)
  | Op : op -> instr
  (** Creates a new variable on top of the stack variable,
      initialized to 0. *)
  | NewVar : instr
  (** Remove a variable from the top of the variables stack.
      Its current value is lost. *)
  | DelVar : instr
  (** Push a value to the  i-th variable on the stack. *)
  | GetVar : nat -> instr
  (** Pop the value on the top of the stack and store it to the 
  i-th variable. *)
  | SetVar : nat -> instr
  (** Jump offset: remove  offset from the code pointer if the
  first variable is less than or equal to the top of the stack.
     Stack and variables are left unchanged. *)
  | Jump : nat -> instr.

(* NB: There is no Halt instruction, one stops when 
   pc goes beyond the end of the code. *)

(* Reference Semantics for instructions,
   defined via an inductive relation *)

Inductive Stepi : instr -> machine -> machine -> Prop :=
| SPush pc stk vs n :
    Stepi (Push n) (Mach pc stk vs) (Mach (S pc) (n::stk) vs)
| SPop pc stk vs x :
    Stepi Pop (Mach pc (x::stk) vs) (Mach (S pc) stk vs)
| SOp pc stk vs o y x :
    Stepi (Op o) (Mach pc (y::x::stk) vs)
                 (Mach (S pc) (eval_op o x y :: stk) vs)
| SNewVar pc stk vs :
    Stepi NewVar (Mach pc stk vs) (Mach (S pc) stk (0::vs))
| SDelVar pc stk vs x :
    Stepi DelVar (Mach pc stk (x::vs)) (Mach (S pc) stk vs)
| SGetVar pc stk vs i x :
    list_get vs i = Some x ->
    Stepi (GetVar i) (Mach pc stk vs) (Mach (S pc) (x::stk) vs)
| SSetVar pc stk vs vs' i x :
    list_set vs i x = Some vs' ->
    Stepi (SetVar i) (Mach pc (x::stk) vs)
                     (Mach (S pc) stk vs')
| SJumpYes pc stk vs v x off : off <= pc -> v <= x ->
    Stepi (Jump off) (Mach pc (x::stk) (v::vs))
                     (Mach (pc-off) (x::stk) (v::vs))
| SJumpNo pc stk vs v x off : x < v ->
    Stepi (Jump off) (Mach pc (x::stk) (v::vs))
                     (Mach (S pc) (x::stk) (v::vs)).

Definition Step (code:list instr) (m m' : machine) : Prop :=
 match list_get code m.(pc) with
  | Some instr => Stepi instr m m'
  | None => False
 end.

(*SomeSteps define a transitive relation*)
Inductive Steps (code:list instr) : machine -> machine -> Prop :=
 | NoStep m : Steps code m m
 | SomeSteps m1 m2 m3 :
     Step code m1 m2 -> Steps code m2 m3 -> Steps code m1 m3.

(** state : state of a machine, that is its computation stack 
together with its variables stack, but not its code pointer. *)

Definition state := (list nat * list nat)%type.

(** A complete execution goes from  pc=0 to pc=(length code) *)

Definition Exec code '(stk, vs) '(stk', vs') :=
  Steps code (Mach 0 stk vs) (Mach (length code) stk' vs').

(** Run : relation between the code and the result of 
its execution. *)

Definition Run code res := Exec code (nil,nil) (res::nil,nil).

(** Small example using this semantics *)

Lemma Run_example :
  Run (Push 7 :: Push 3 :: Op Minus :: nil) 4.
Proof.
 repeat econstructor.
Qed.

(** Basic properties of Steps : transitivity, ... *)

Global Hint Constructors Stepi Steps : core.

Lemma Steps_trans code m1 m2 m3 :
 Steps code m1 m2 -> Steps code m2 m3 -> Steps code m1 m3.
Proof.
intros.
induction H.
- assumption.
- apply (SomeSteps code m1 m2 m3).
  + assumption.
  + apply IHSteps in H0 as H2. assumption.
Qed.

Lemma OneStep code st st' : Step code st st' -> Steps code st st'.
Proof.
intros.
apply (SomeSteps code st st' st').
- assumption.
- apply (NoStep code st').
Qed.

(** Shifting the pc in a machine *)
(*moving the pc by k positions*)
Definition shift_pc k (p:machine) :=
 let '(Mach pc stk vars) := p in
 (Mach (k+pc) stk vars).

Lemma pc_shift n m : (shift_pc n m).(pc) = n + m.(pc).
Proof.
 now destruct m.
Qed.

(** Adding code before / after the znoe of interest *)
Open Scope nat_scope.
Lemma Step_extend code code' m m' :
 Step code m m' -> Step (code++code') m m'.
Proof.
unfold Step.
revert code. (*necessary to get the implicit forall quantification*)
induction (pc m). 
- destruct code.
  + simpl. contradiction.
  + simpl. trivial.
- destruct code.
  + simpl. contradiction. 
  + simpl. intros. apply IHn. assumption. 
Qed.

Lemma Steps_extend code code' m m' :
 Steps code m m' -> Steps (code++code') m m'.
Proof.
intros.
induction H. 
- apply (NoStep (code ++ code') m).
- apply (SomeSteps (code ++ code') m1 m2 m3).
  + apply Step_extend. assumption.
  + assumption.
Qed.

Lemma Stepi_shift instr n m m' :
 Stepi instr m m' ->
 Stepi instr (shift_pc n m) (shift_pc n m').
Proof.
(*
intros.
induction n.
- destruct m. destruct m'. simpl. assumption.
- destruct m. destruct m'. simpl. .
*)
Admitted.

Lemma Step_shift code0 code m m' (n := List.length code0) :
 Step code m m' ->
 Step (code0 ++ code) (shift_pc n m) (shift_pc n m').
Proof.
Admitted.

Lemma Steps_shift code0 code  m m' (n := List.length code0) :
 Steps code m m' ->
 Steps (code0 ++ code) (shift_pc n m) (shift_pc n m').
Proof.
Admitted.

(** Composition of complete executions *)

Lemma Exec_trans code1 code2 stk1 vars1 stk2 vars2 stk3 vars3 :
 Exec code1 (stk1, vars1) (stk2, vars2) ->
 Exec code2 (stk2, vars2) (stk3, vars3) ->
 Exec (code1 ++ code2) (stk1, vars1) (stk3, vars3).
Proof.
Admitted.


(** Correctness of jumps in a loop:

    - Variable 0 is the variable for loop a,
    - Variable 1 is the accumulator acc
    - The top of the stack is the upper limit b
    of the loop variable

    One first shows that if a code adds f(a) to acc and
    increments a, then repeting this  (via a later Jump)
    will add (sum f a (b-a)) to acc.
    Variable N (of vaue b-a) is the number of loop round 
    to make.
*)

(** The following lemma is hard. You can first skip it and come back later, after finishing part IV... *)

Global Hint Resolve le_n_S le_plus_r : core.

Lemma Steps_jump code n (f:nat->nat) stk vars b :
  length code = n ->
  (forall a acc,
   Steps code
         (Mach 0 (b::stk) (a::acc::vars))
         (Mach n (b::stk) ((S a)::(acc + f a)::vars)))
  ->
  forall N a acc,
    b = N + a ->
    Steps (code++(Jump n)::nil)
          (Mach 0 (b::stk) (a::acc::vars))
          (Mach (S n) (b::stk) ((S b)::(acc + sum f a N)::vars)).
Proof.
Admitted.

(** Specialized version of the previous result, with
    Exec instead of Step, and 0 as initial value for loop variables
    and accumulators. *)

Lemma Exec_jump code (f:nat->nat) stk vars b :
  (forall a acc,
     Exec code (b::stk, a::acc::vars)
               (b::stk, (S a)::(acc + f a)::vars))
  ->
  Exec (code++(Jump (length code))::nil)
      (b::stk, 0::0::vars)
      (b::stk, (S b)::(sum f 0 b)::vars).
Proof.
Admitted.


(** IV) The compiler

    One transforms an expression into a series of instructions
    for the stack machine.

    Conventions:
     - At any loop entry, one created two variables,
       the loop variable and the accumulator.
     - Loop variables always have even positions in the variable 
     stack.
     - the compilation environment cenv contains only
       loop variables.
    See also the invariant EnvsOk below for details. *)

Fixpoint comp (cenv:list string) e :=
  match e with
    | EInt n => Push n :: nil
    | EVar v => TODO
    | EOp o e1 e2 => TODO
    | ESum v efin ecorps =>
      let prologue := TODO in
      let corps := TODO in
      let boucle := corps ++ Jump TODO :: nil in
      let epilogue := TODO in
      prologue ++ boucle ++ epilogue
  end.

Definition compile e := comp nil e.

(** Free variables in an expression *)

Inductive FV (v:var) : expr -> Prop :=
| FVVar : FV v (EVar v).
(* TODO : ajouter les règles manquantes... *)

Global Hint Constructors FV : core.

Definition Closed e := forall v, ~ FV v e.

(** Environment invariants.
    env : evaluation environment (list (string*nat))
    cenv : compilation environment (list string)
    vars : stack variable for the machines *)

Definition EnvsOk e env cenv vars :=
 forall v, FV v e ->
   In v cenv /\
   list_get vars (index v cenv * 2) = Some (lookup v env 0).

Global Hint Unfold EnvsOk : core.

Lemma EnvsOk_ESum v e1 e2 env cenv vars a b :
  EnvsOk (ESum v e1 e2) env cenv vars ->
  EnvsOk e2 ((v,a)::env) (v::cenv) (a::b::vars).
Proof.
Admitted.


(** Compiler correctness *)

Ltac basic_exec :=
  (* This tactics proves goal (Exec code m m')
      when the code and the machine m are known in detail. *)
  unfold Exec; repeat (eapply SomeSteps; [constructor|]);
   try apply NoStep; try reflexivity.

(* Note that if you think you are proving something impossible,
if may be a sign that you got the wrong definition for comp. *)

Theorem comp_ok e env cenv vars stk :
 EnvsOk e env cenv vars ->
 Exec (comp cenv e) (stk,vars) (eval env e :: stk, vars).
Proof.
Admitted.

Theorem compile_ok e : Closed e -> Run (compile e) (eval nil e).
Proof.
Admitted.

(** V) Executable semantics

    Instead of the previous relations (Step*, Exec, Run...),
    one know wants to get a function computing the result of
    executing a stack machine. *)

(** This part is much harder that the previous one and
it is optional. *)

Inductive step_result : Type :=
  | More : machine -> step_result (* calcul en cours *)
  | Stop : machine -> step_result (* calcul fini (pc hors code) *)
  | Bug : step_result. (* situation illégale, machine plantée *)

(** For function [step] below, these two monadic operators
    may help (even thoug this is essentially a matter of 
    taste...). *)

Definition option_bind {A} (o:option A) (f : A -> step_result) :=
  match o with
    | None => Bug
    | Some x => f x
  end.

Infix ">>=" := option_bind (at level 20, left associativity).

Definition list_bind {A} (l:list A) (f:A->list A->step_result) :=
 match l with
  | nil => Bug
  | x::l => f x l
 end.

Infix "::>" := list_bind (at level 20, left associativity).

(** One step of computation *)

Definition step code (m:machine) : step_result :=
  let '(Mach pc stk vars) := m in
  (** usual answer: *)
  let more := fun stk vars => More (Mach (S pc) stk vars) in
  match list_get code pc with
    | None => Stop m
    | Some instr => match instr with
      | Push n => more (n::stk) vars
      | Pop => TODO
      | Op o => TODO
      | NewVar => TODO
      | DelVar => TODO
      | GetVar i => TODO
      | SetVar i => TODO
      | Jump off => TODO
      end
    end.

(** The [steps] function iterates [step] [count] many times
    (or less if [Stop _] or [Bug] are reached before...). *)

Fixpoint steps count (code:list instr)(m:machine) :=
  match count with
    | 0 => More m
    | S count' => TODO
  end.

(** Function [run] executes a certain code from the initial
    machine, then extracts the result.
    One returns  [None] if the computation is not finished
    after [count] steps, or if there is a problem during 
    execution or in the end state (eg. empty final stack,
    non empty final variables, etc). *)

Definition run (count:nat)(code : list instr) : option nat :=
  TODO.

Compute (run 1000 (compile test1)). (* expected value: Some 385 *)
Compute (run 1000 (compile test2)). (* expected value: Some 1705 *)

(** Equivalence between the two semantics *)

(** TODO: in this part, you have to step yourself the intermediate results. *)

Lemma run_equiv code res :
 Run code res <-> exists count, run count code = Some res.
Proof.
Admitted.

(** Here is the  main theorem formulated for run *)

Theorem run_compile e :
 Closed e ->
 exists count, run count (compile e) = Some (eval nil e).
Proof.
Admitted.
